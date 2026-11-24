//! The compiled program must give exec code the types (and the functions it calls, and the
//! literals it uses) that Verus verified.
//!
//! Verus type-checks the crate twice: once with its ghost code, to verify it, and once with the
//! ghost code erased, to compile it (the "erase" run, see `driver.rs`). When ghost code is the only
//! thing that fixes the type of exec code, the two runs infer different types:
//!
//! ```ignore
//! let n = 1;                 // verified: `u64`; compiled: `i32`, the default of an integer literal
//! proof { let g: u64 = n; }
//! n.mk()                     // verified: `<u64 as Mk>::mk`; compiled: `<i32 as Mk>::mk`
//! ```
//!
//! and the compiled program runs code that Verus did not verify (other arithmetic, another impl,
//! another type argument). The same goes for a `let ghost`, a `Ghost(..)` or `Tracked(..)` argument,
//! a loop invariant, a `#[verus_spec]` return type, or a never-type or float literal fallback.
//!
//! The verification records, for every expression and pattern of the bodies of the exec functions
//! and constants that it builds VIR for, its type, what it resolves to (with its type arguments),
//! and its value if it is a literal, by source location and kind of node (`ExecTypes::of`). The
//! compilation records the same for all of its bodies and compares them at each location and kind
//! that both have (`ExecTypes::differences`): what the compiled program has there must be among what
//! the verified program has there. Nodes that only one of the runs has are not compared: ghost code
//! is erased, and Verus's macros generate some code for one run only. (That the two runs have the
//! same exec code is the macros' part, and with -V alloc-check also `VerifiedInputs`.)

use rustc_hir::HirId;
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_span::def_id::LocalDefId;
use std::collections::BTreeMap;

/// Where a node is (its file, by content hash, and the file-relative offsets of its span) and what
/// kind of node it is
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct NodeKey {
    /// the path of the body's owner (by its definition path: the verified twin of a
    /// `#[verus_spec(with ..)]` function is named as the function, see `normalize`). (Macros such
    /// as vstd's `exec_spec!` give the code they generate the spans of the user's tokens, which
    /// other items of the other run have as well.)
    owner: String,
    file: Vec<u8>,
    lo: u32,
    hi: u32,
    kind: (u8, u64),
    /// the kind of rustc desugaring that the node comes from, if any (rustc desugars a `for` loop
    /// that the compiled program has, while the verified program has the loop that `verus!`
    /// builds for it, with the spans of the user's tokens)
    desugaring: u64,
    /// for a node of a `macro_rules!` expansion, the location of the outermost macro call (the
    /// node's own span is in the macro's definition, the same for each call)
    call_site: (u32, u32),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Fact {
    Type(String),
    Resolution(String),
    Literal(String),
    /// in place of a type that contains `Ghost` or `Tracked` (see `is_ghost_wrapper`): the types
    /// at the key are not compared (the other facts are)
    GhostType,
}

/// The exec types of one run (see the module documentation): for each key, each fact with the
/// number of nodes at the key that have it (a macro can put the same tokens in a body more than
/// once, with other types each time)
#[derive(Clone, Debug, Default)]
pub(crate) struct ExecTypes {
    nodes: BTreeMap<NodeKey, BTreeMap<Fact, u32>>,
}

/// The names of the items that Verus's macros generate for the verification in place of the
/// user's: the verified twin `_VERUS_VERIFIED_f` of a `#[verus_spec(with ..)]` function `f`, and
/// the unerased proxy of a `const`. (The crate's source may not use these prefixes under
/// -V alloc-check; see `alloc_check_forbidden_idents`.)
fn normalize(s: String) -> String {
    let s = if s.contains("VERUS_") {
        s.replace("_VERUS_VERIFIED_", "").replace("VERUS_UNERASED_PROXY__", "")
    } else {
        s
    };
    // A closure's (or coroutine's) type is printed with its span, which `#[verus_spec]` extends
    // over the closure's specification in the verified program: name it by its kind only (the
    // code of its body is compared node by node)
    let s = if s.contains('@') {
        static CLOSURE: std::sync::LazyLock<regex::Regex> =
            std::sync::LazyLock::new(|| regex::Regex::new(r"\{([a-z][a-z -]*)@[^{}]*\}").unwrap());
        CLOSURE.replace_all(&s, "{$1}").into_owned()
    } else {
        s
    };
    // Items nested in a closure are named by the closure's index among its parent's closures, which
    // the closures that Verus's macros add to one of the runs shift
    let s = if s.contains('#') {
        static INDEX: std::sync::LazyLock<regex::Regex> =
            std::sync::LazyLock::new(|| regex::Regex::new(r"\{([a-z][a-z_ -]*)#[0-9]+\}").unwrap());
        INDEX.replace_all(&s, "{$1#}").into_owned()
    } else {
        s
    };
    // Ghost code can make rustc infer a stricter kind for a closure in the verified program (a
    // closure that moves a captured variable into a specification is `FnOnce` there), and call it
    // by value instead of by reference; the verifier checks the stricter kind, and the call runs
    // the same body (what differs is when the captured values are dropped)
    if s.contains("{closure} as core::ops::function::Fn") {
        s.replace("<&{closure} as ", "<{closure} as ")
            .replace("<&mut {closure} as ", "<{closure} as ")
            .replace("core::ops::function::FnOnce<", "core::ops::function::Fn<")
            .replace("core::ops::function::FnMut<", "core::ops::function::Fn<")
            .replace(">::call_once", ">::call")
            .replace(">::call_mut", ">::call")
    } else {
        s
    }
}

/// `Ghost<T>` and `Tracked<T>` values carry nothing at run time, and the compilation builds them
/// without their argument (`Ghost::assume_new_fallback(|| unreachable!())`, at the span of the
/// user's `Ghost(..)`), and returns them from a function with ghost outputs (`-> z: Ghost<T>`)
/// only in the verified program: the types that contain them, and their constructors, are not
/// compared. (Only these facts: a call of a function with a `Ghost<T>` parameter is still compared
/// by the function's type arguments.) (`core::verus_builtin` when vstd is imported through core.)
fn is_ghost_wrapper(fact: &Fact) -> bool {
    match fact {
        Fact::Type(s) if !s.starts_with("fn ") => {
            s.contains("verus_builtin::Ghost<") || s.contains("verus_builtin::Tracked<")
        }
        Fact::Type(s) | Fact::Resolution(s) => {
            let s = s.strip_prefix("fn ").unwrap_or(s);
            let s = s.strip_prefix("core::").unwrap_or(s);
            [
                "verus_builtin::Ghost",
                "verus_builtin::Tracked",
                "verus_builtin::ghost_exec",
                "verus_builtin::tracked_exec",
            ]
            .iter()
            .any(|p| {
                s.strip_prefix(p).is_some_and(|rest| {
                    rest.starts_with('<') || rest.starts_with("::") || rest.is_empty()
                })
            })
        }
        Fact::Literal(_) | Fact::GhostType => false,
    }
}

/// The crates whose macros expand differently for the verification and for the compilation by
/// design, and are trusted (`open_local_invariant!`, `atomic_with_ghost!`, ...)
fn is_verus_crate(name: &str) -> bool {
    matches!(
        name,
        "vstd" | "verus_builtin" | "verus_builtin_macros" | "verus_state_machines_macros"
    )
}

/// Prints items by their definition paths (not by a re-export, which depends on what is in scope,
/// and differs between the runs where Verus's macros import something for one only)
fn canonical(print: impl FnOnce() -> String) -> String {
    rustc_middle::ty::print::with_no_trimmed_paths!(
        rustc_middle::ty::print::with_no_visible_paths!(print())
    )
}

fn kind_hash<T>(kind: &T) -> u64 {
    use std::hash::{Hash, Hasher};
    // (both runs are in the same process, so the discriminants and this hasher agree)
    let mut h = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(kind).hash(&mut h);
    h.finish()
}

impl ExecTypes {
    /// The exec types of the bodies of `owners` (typeck roots), or of all bodies of the crate
    pub(crate) fn of<'tcx>(tcx: TyCtxt<'tcx>, owners: Option<&[LocalDefId]>) -> ExecTypes {
        let all: Vec<LocalDefId>;
        let owners = match owners {
            Some(owners) => owners,
            None => {
                all =
                    tcx.hir_body_owners().filter(|d| !tcx.is_typeck_child(d.to_def_id())).collect();
                &all
            }
        };
        let mut exec_types = ExecTypes::default();
        for owner in owners.iter() {
            exec_types.add_body(tcx, *owner, None, None);
        }
        exec_types
    }

    /// The key and span of a node of a body, if its code is compared
    fn node_key<'tcx>(tcx: TyCtxt<'tcx>, owner: &str, hir_id: HirId) -> Option<(NodeKey, Span)> {
        let (kind, span) = match tcx.hir_node(hir_id) {
            rustc_hir::Node::Expr(e) => ((0u8, kind_hash(&e.kind)), e.span),
            // (not the parameters: the signature gives their types, and the compiled program
            // drops or replaces the ghost ones; their uses in the body are compared)
            rustc_hir::Node::Pat(_)
                if matches!(tcx.parent_hir_node(hir_id), rustc_hir::Node::Param(_)) =>
            {
                return None;
            }
            rustc_hir::Node::Pat(p) => ((1u8, kind_hash(&p.kind)), p.span),
            rustc_hir::Node::PatExpr(p) => ((2u8, kind_hash(&p.kind)), p.span),
            _ => ((3u8, 0), tcx.hir_span(hir_id)),
        };
        if span.is_dummy() {
            return None;
        }
        // Which code is compared: the code that the user wrote, as its tokens' spans show (also
        // when Verus's macros pass them on), in the source or in a `macro_rules!` definition, and
        // rustc's desugarings of it. Not the tokens that a procedural macro makes itself (they
        // have the span of its call, or of the item for a derive or attribute macro), nor the
        // code of Verus's and vstd's macros: both differ between the runs by design.
        let sm = tcx.sess.source_map();
        let mut call_site = (0, 0);
        if span.from_expansion() {
            let mut ctxt = span.ctxt();
            let mut innermost = true;
            while !ctxt.is_root() {
                let data = ctxt.outer_expn_data();
                match data.kind {
                    rustc_span::hygiene::ExpnKind::Desugaring(_) => {}
                    rustc_span::hygiene::ExpnKind::Macro(
                        rustc_span::hygiene::MacroKind::Bang,
                        _,
                    ) => {
                        if innermost
                            && span.lo() == data.call_site.lo()
                            && span.hi() == data.call_site.hi()
                        {
                            return None;
                        }
                    }
                    _ => return None,
                }
                if data
                    .macro_def_id
                    .is_some_and(|d| is_verus_crate(tcx.crate_name(d.krate).as_str()))
                {
                    return None;
                }
                innermost = false;
                ctxt = data.call_site.ctxt();
            }
            let (_, lo, hi) = crate::fip_mir::span_offsets(sm, span.source_callsite())?;
            call_site = (lo, hi);
        }
        let (file, lo, hi) = crate::fip_mir::span_offsets(sm, span)?;
        let desugaring = span.desugaring_kind().map_or(0, |d| kind_hash(&d).max(1));
        Some((
            NodeKey { owner: owner.to_string(), file, lo, hi, kind, desugaring, call_site },
            span,
        ))
    }

    /// Records the nodes of the body of `owner` (only those with a key in `only`, if given), and
    /// their spans in `spans`
    fn add_body<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        only: Option<&ExecTypes>,
        mut spans: Option<&mut BTreeMap<NodeKey, Span>>,
    ) {
        let results = tcx.typeck(owner);
        if results.tainted_by_errors.is_some() {
            return;
        }
        let hir_owner = results.hir_owner;
        let owner_path = normalize(canonical(|| tcx.def_path_str(owner.to_def_id())));
        let mut keys: BTreeMap<rustc_hir::ItemLocalId, Option<NodeKey>> = BTreeMap::new();
        let mut key_of = |local_id: rustc_hir::ItemLocalId| -> Option<NodeKey> {
            keys.entry(local_id)
                .or_insert_with(|| {
                    let (key, span) =
                        Self::node_key(tcx, &owner_path, HirId { owner: hir_owner, local_id })?;
                    if only.is_some_and(|only| !only.nodes.contains_key(&key)) {
                        return None;
                    }
                    if let Some(spans) = spans.as_mut() {
                        spans.entry(key.clone()).or_insert(span);
                    }
                    Some(key)
                })
                .clone()
        };
        let mut facts: BTreeMap<NodeKey, Vec<Fact>> = BTreeMap::new();
        for (local_id, ty) in results.node_types().items_in_stable_order() {
            if ty.references_error() {
                continue;
            }
            let Some(key) = key_of(local_id) else { continue };
            let ty = tcx.erase_and_anonymize_regions(*ty);
            // (a function item by its path and type arguments: its signature lacks the ghost
            // parameters in the compiled program)
            let s = match ty.kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, args) => normalize(canonical(|| {
                    format!("fn {}", tcx.def_path_str_with_args(*def_id, args.skip_binder()))
                })),
                _ => normalize(canonical(|| ty.to_string())),
            };
            let node_facts = facts.entry(key).or_default();
            node_facts.push(Fact::Type(s));
            if let rustc_hir::Node::Expr(rustc_hir::Expr {
                kind: rustc_hir::ExprKind::Lit(lit),
                ..
            }) = tcx.hir_node(HirId { owner: hir_owner, local_id })
            {
                node_facts.push(Fact::Literal(format!("{:?}", lit.node)));
            }
        }
        for (local_id, res) in results.type_dependent_defs().items_in_stable_order() {
            let Ok((_, def_id)) = res else { continue };
            let Some(key) = key_of(local_id) else { continue };
            let args = tcx.erase_and_anonymize_regions(
                results.node_args(HirId { owner: hir_owner, local_id }),
            );
            let s = normalize(canonical(|| tcx.def_path_str_with_args(*def_id, args)));
            facts.entry(key).or_default().push(Fact::Resolution(s));
        }
        for (key, node_facts) in facts {
            let counts = self.nodes.entry(key).or_default();
            for fact in node_facts {
                let fact = match fact {
                    Fact::Type(_) if is_ghost_wrapper(&fact) => Fact::GhostType,
                    _ if is_ghost_wrapper(&fact) => continue,
                    _ => fact,
                };
                *counts.entry(fact).or_default() += 1;
            }
        }
    }

    /// The places where the compiled program (the crate of `tcx`) has other types, resolutions or
    /// literals than the verified program (`self`), with an error message for each: at most one
    /// for each body, the first in it
    pub(crate) fn differences<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Vec<(Span, String)> {
        let mut found = vec![];
        for owner in tcx.hir_body_owners() {
            if tcx.is_typeck_child(owner.to_def_id()) {
                continue;
            }
            let mut compiled = ExecTypes::default();
            let mut spans: BTreeMap<NodeKey, Span> = BTreeMap::new();
            compiled.add_body(tcx, owner, Some(self), Some(&mut spans));
            let mut differing: Vec<(&NodeKey, String)> = vec![];
            for (key, compiled_facts) in compiled.nodes.iter() {
                let Some(verified_facts) = self.nodes.get(key) else { continue };
                // (code that never produces a value in the compiled program, as the erased stubs
                // that Verus's macros leave in place of some bodies, runs no unverified code; nor
                // does a unit value, as the empty block that a ghost statement is erased to (an
                // exec call that returns `()` there is compared by what it calls))
                // (each fact must be on at least as many nodes at the key in the verified program)
                let erased = [Fact::Type("!".to_string()), Fact::Type("()".to_string())];
                let ghost_typed = verified_facts.contains_key(&Fact::GhostType);
                let Some((fact, _)) = compiled_facts.iter().find(|(f, n)| {
                    !erased.contains(*f)
                        && !matches!(f, Fact::GhostType)
                        && !(ghost_typed && matches!(f, Fact::Type(_)))
                        && verified_facts.get(*f).copied().unwrap_or(0) < **n
                }) else {
                    continue;
                };
                let verified = |pick: fn(&Fact) -> Option<&String>| {
                    let all: Vec<String> =
                        verified_facts.keys().filter_map(pick).map(|t| format!("`{t}`")).collect();
                    if all.is_empty() { "something else".to_string() } else { all.join(" or ") }
                };
                let what = match fact {
                    Fact::Type(s) => format!(
                        "this exec code has type `{s}` in the compiled program, but {} in the verified program",
                        verified(|f| if let Fact::Type(t) = f { Some(t) } else { None })
                    ),
                    Fact::Resolution(s) => format!(
                        "this exec code refers to `{s}` in the compiled program, but to {} in the verified program",
                        verified(|f| if let Fact::Resolution(t) = f { Some(t) } else { None })
                    ),
                    Fact::Literal(s) => format!(
                        "this literal is `{s}` in the compiled program, but {} in the verified program",
                        verified(|f| if let Fact::Literal(t) = f { Some(t) } else { None })
                    ),
                    // (not compared, see above)
                    Fact::GhostType => continue,
                };
                differing.push((key, format!(
                    "{what}: Verus verifies the code together with its ghost code and compiles it with the ghost code erased, and here only the ghost code (such as a `proof` block, a `let ghost`, a `Ghost(..)` or `Tracked(..)` argument, a loop invariant or a specification) decides the type, so the compiled program would run code that was not verified; write the type in the exec code (for example `let x: u64 = ..`, `1u64` or `f::<u64>(..)`)"
                )));
            }
            // (the first in the body: a binding or literal comes before the code that uses it)
            differing.sort_by_key(|(key, _)| (key.file.clone(), key.lo, std::cmp::Reverse(key.hi)));
            if let Some((key, message)) = differing.first() {
                let mut message = message.clone();
                if differing.len() > 1 {
                    message.push_str(&format!(
                        " ({} more places in this body differ)",
                        differing.len() - 1
                    ));
                }
                found.push((spans[*key], message));
            }
        }
        found
    }
}
