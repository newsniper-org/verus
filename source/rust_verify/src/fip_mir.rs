//! -V alloc-check, `#[verifier::fip]` (fully in-place, FP²): a fip function must not deallocate
//! memory on a normal return. Its calls are checked by the verifier (`vir::ast_to_sst`, the
//! callees' `deallocates_when` conditions); the drops that the compiler inserts are checked here,
//! on the MIR of the compiled program (after ghost code is erased and after drop elaboration),
//! which is the only place where they are known. A drop on a path that returns normally
//! deallocates unless the dropped type is `vstd::alloc_check::NoDeallocDrop` (or has no drop
//! glue at all); paths that unwind are not covered, like `allocates`.

use crate::attributes::{Attr, parse_attrs_opt};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeVisitableExt, TypingEnv};
use rustc_span::Span;
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_trait_selection::infer::InferCtxtExt;

const MARKER: &str = "vstd::alloc_check::NoDeallocDrop";
const FIP_ALLOCATOR: &str = "vstd::alloc_check::FipAllocator";
const FIP_STRICT_ALLOCATOR: &str = "vstd::alloc_check::FipStrictAllocator";

/// `core::alloc::Allocator` and vstd's `FipAllocator`/`FipStrictAllocator`
struct AllocTraits {
    allocator: DefId,
    fip: DefId,
    strict: DefId,
}

fn alloc_traits(tcx: TyCtxt<'_>) -> Option<AllocTraits> {
    let allocator = tcx.all_traits_including_private().find(|d| {
        tcx.crate_name(d.krate).as_str() == "core" && tcx.item_name(*d).as_str() == "Allocator"
    })?;
    let fip = tcx.all_traits_including_private().find(|d| tcx.def_path_str(*d) == FIP_ALLOCATOR)?;
    let strict = tcx
        .all_traits_including_private()
        .find(|d| tcx.def_path_str(*d) == FIP_STRICT_ALLOCATOR)?;
    Some(AllocTraits { allocator, fip, strict })
}

/// The global or the system allocator (std's own, whose methods are not user code)
fn is_std_allocator<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Adt(adt, _) => {
            matches!(tcx.crate_name(adt.did().krate).as_str(), "alloc" | "std" | "core")
                && matches!(tcx.item_name(adt.did()).as_str(), "Global" | "System")
        }
        _ => false,
    }
}

/// The allocators other than std's (user code) among the types in `args`: std or vstd code
/// instantiated with them may call their methods (a container that grows calls `allocate`)
fn user_allocators<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    at: &AllocTraits,
    args: ty::GenericArgsRef<'tcx>,
) -> Vec<Ty<'tcx>> {
    let mut out: Vec<Ty<'tcx>> = Vec::new();
    for arg in args.iter() {
        let Some(t) = arg.as_type() else { continue };
        for g in t.walk() {
            let Some(u) = g.as_type() else { continue };
            if u.has_escaping_bound_vars() || matches!(u.kind(), ty::Ref(..)) {
                // (the referent is visited too)
                continue;
            }
            if is_std_allocator(tcx, u) || out.contains(&u) {
                continue;
            }
            if implements(tcx, typing_env, at.allocator, u) {
                out.push(u);
            }
        }
    }
    out
}

/// Marker rule: `unsafe impl FipAllocator for X` (`FipStrictAllocator`) is accepted only if the
/// methods of `X` that std's containers may call in a fip function are `#[verifier::fip]`
/// (`#[verifier::fip(strict)]`) functions of this crate: `allocate`, `allocate_zeroed` (std's
/// default body calls `allocate`) and `Clone::clone` (of every `Clone` impl of `X`'s type
/// constructor). (A container calls `grow` or `shrink` only on a buffer it has, which frees the
/// old one, and `deallocate` only to free, both of which a fip function's own checks rule out.)
/// Returns the strict methods, for `check_strict_stack`.
fn check_fip_allocator_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    at: &AllocTraits,
    checked: &[(String, u128)],
) -> Vec<(LocalDefId, Span)> {
    let mut strict_methods = Vec::new();
    let method_of = |tr: DefId, name: &str| {
        tcx.associated_items(tr)
            .in_definition_order()
            .find(|i| i.ident(tcx).as_str() == name)
            .map(|i| i.def_id)
    };
    for (marker, strict) in [(at.fip, false), (at.strict, true)] {
        let kind = if strict { "#[verifier::fip(strict)]" } else { "#[verifier::fip]" };
        for impl_def_id in tcx.all_impls(marker) {
            if tcx.crate_name(impl_def_id.krate).as_str() == "vstd" {
                continue;
            }
            if !impl_def_id.is_local() {
                // checked when its crate was compiled, if it was verified with -V alloc-check
                dependency_impl_checked(
                    tcx,
                    impl_def_id,
                    checked,
                    if strict { "FipStrictAllocator" } else { "FipAllocator" },
                );
                continue;
            }
            let span = tcx.def_span(impl_def_id);
            let typing_env = TypingEnv::post_analysis(tcx, impl_def_id);
            let self_ty = tcx.erase_and_anonymize_regions(
                tcx.type_of(impl_def_id).instantiate_identity().skip_normalization(),
            );
            let err = |what: String| {
                tcx.dcx().span_err(
                    span,
                    format!(
                        "-V alloc-check: this `{}` impl is not accepted: {}",
                        if strict { "FipStrictAllocator" } else { "FipAllocator" },
                        what
                    ),
                );
            };
            let ok_kind = |d: LocalDefId| match fip_kind_local(tcx, d) {
                Some(s) => s || !strict,
                None => false,
            };
            for (name, default_ok) in [("allocate", false), ("allocate_zeroed", true)] {
                let Some(m) = method_of(at.allocator, name) else { continue };
                let args = tcx.mk_args(&[self_ty.into()]);
                match ty::Instance::try_resolve(tcx, typing_env, m, args) {
                    Ok(Some(inst)) if inst.def_id() == m && default_ok => {}
                    Ok(Some(inst)) => match inst.def_id().as_local() {
                        Some(d) if ok_kind(d) => {
                            if strict {
                                strict_methods.push((d, span));
                            }
                        }
                        _ => err(format!(
                            "`{}::{}` must be a {} function of this crate",
                            self_ty, name, kind
                        )),
                    },
                    _ => {
                        err(format!("the `Allocator::{}` of `{}` is not known here", name, self_ty))
                    }
                }
            }
            if let (Some(clone_trait), ty::Adt(adt, _)) =
                (tcx.lang_items().clone_trait(), self_ty.kind())
            {
                for clone_impl in tcx.all_impls(clone_trait) {
                    let cty = tcx.type_of(clone_impl).instantiate_identity().skip_normalization();
                    if cty.ty_adt_def().map(|a| a.did()) != Some(adt.did()) {
                        continue;
                    }
                    for item in tcx.associated_items(clone_impl).in_definition_order() {
                        if item.ident(tcx).as_str() != "clone" {
                            continue;
                        }
                        match item.def_id.as_local() {
                            Some(d) if ok_kind(d) => {
                                if strict {
                                    strict_methods.push((d, span));
                                }
                            }
                            _ => err(format!(
                                "the `Clone::clone` of `{}` must be a {} function of this crate (std's containers may clone their allocator)",
                                cty, kind
                            )),
                        }
                    }
                }
            }
        }
    }
    strict_methods
}

/// In a fip function, a call of std or vstd code instantiated with a user allocator: it may call
/// the allocator's methods, which must then be fip (`FipAllocator`, or `FipStrictAllocator` in a
/// strict function). Returns whether the call uses a user allocator.
fn check_allocator_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    at: &AllocTraits,
    strict: bool,
    callee: DefId,
    args: ty::GenericArgsRef<'tcx>,
    span: Span,
) -> bool {
    if !is_trusted_leaf_crate(tcx, callee) {
        return false;
    }
    let users = user_allocators(tcx, typing_env, at, args);
    for u in users.iter() {
        let (need, name) =
            if strict { (at.strict, FIP_STRICT_ALLOCATOR) } else { (at.fip, FIP_ALLOCATOR) };
        if !implements(tcx, typing_env, need, *u) {
            tcx.dcx().span_err(
                span,
                format!(
                    "-V alloc-check: a `#[verifier::fip{}]` function may use the allocator `{}` here (through `{}`, which may call its `allocate`) only if it implements `{}`",
                    if strict { "(strict)" } else { "" },
                    u,
                    tcx.def_path_str(callee),
                    name
                ),
            );
        }
    }
    !users.is_empty()
}

/// `#[verifier::fip]` (`Some(false)`) or `#[verifier::fip(strict)]` (`Some(true)`)
fn fip_kind_local(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<bool> {
    let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(def_id));
    parse_attrs_opt(attrs, None).iter().find_map(|a| match a {
        Attr::Fip(strict) => Some(*strict),
        _ => None,
    })
}

fn is_fip_local(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    fip_kind_local(tcx, def_id).is_some()
}

fn implements<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    marker: DefId,
    ty: Ty<'tcx>,
) -> bool {
    let ty = tcx.erase_and_anonymize_regions(ty);
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    infcx.type_implements_trait(marker, [ty], param_env).must_apply_modulo_regions()
}

/// Can dropping a value of type `ty` deallocate?
fn drop_may_deallocate<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    marker: Option<DefId>,
    ty: Ty<'tcx>,
) -> bool {
    if !ty.needs_drop(tcx, typing_env) {
        return false;
    }
    match marker {
        Some(m) => !implements(tcx, typing_env, m, ty),
        None => true,
    }
}

/// A marker impl of another crate was checked by the compilation of that crate if its crate was
/// verified (and compiled) with -V alloc-check: its imported .vir is marked as checked and was
/// produced together with the linked crate (`checked`, by name and SVH). Otherwise it is rejected.
fn dependency_impl_checked(
    tcx: TyCtxt<'_>,
    impl_def_id: DefId,
    checked: &[(String, u128)],
    marker: &str,
) {
    let krate = impl_def_id.krate;
    let name = tcx.crate_name(krate).to_string();
    let hash = tcx.crate_hash(krate).as_u128();
    if !checked.iter().any(|(n, h)| *n == name && *h == hash) {
        tcx.dcx().err(format!(
            "-V alloc-check: the `{}` impl `{}` is in the crate `{}`, which was not verified (and compiled) with -V alloc-check and imported with its library file, so the impl was not checked",
            marker,
            tcx.def_path_str(impl_def_id),
            name
        ));
    }
}

/// Marker rule: `unsafe impl NoDeallocDrop for X` is accepted only if dropping an `X` cannot
/// deallocate: `X` is not a `Box`, its own `Drop` (if any) is `#[verifier::fip]`, and dropping
/// each of its fields cannot deallocate (it has no drop glue or is `NoDeallocDrop`, with the
/// impl's own bounds). This crate's impls are checked here, and those of other crates when they were compiled.
fn check_marker_impls<'tcx>(tcx: TyCtxt<'tcx>, marker: DefId, checked: &[(String, u128)]) {
    for impl_def_id in tcx.all_impls(marker) {
        if !impl_def_id.is_local() && tcx.crate_name(impl_def_id.krate).as_str() != "vstd" {
            dependency_impl_checked(tcx, impl_def_id, checked, "NoDeallocDrop");
            continue;
        }
        let span = tcx.def_span(impl_def_id);
        let typing_env = TypingEnv::post_analysis(tcx, impl_def_id);
        let self_ty = tcx.type_of(impl_def_id).instantiate_identity().skip_normalization();
        if let Err(why) = check_no_dealloc_drop(tcx, typing_env, marker, self_ty) {
            tcx.dcx().span_err(
                span,
                format!(
                    "-V alloc-check: this `NoDeallocDrop` impl is not accepted: dropping a `{}` may deallocate ({})",
                    self_ty, why
                ),
            );
        }
    }
}

fn check_no_dealloc_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    marker: DefId,
    ty: Ty<'tcx>,
) -> Result<(), String> {
    if !ty.needs_drop(tcx, typing_env) {
        return Ok(());
    }
    let field_ok = |fty: Ty<'tcx>| -> Result<(), String> {
        if drop_may_deallocate(tcx, typing_env, Some(marker), fty) {
            Err(format!("a part of type `{}` may deallocate", fty))
        } else {
            Ok(())
        }
    };
    match ty.kind() {
        ty::Adt(adt, args) => {
            if adt.is_box() {
                return Err("it is a `Box`".to_string());
            }
            if let Some(dtor) = adt.destructor(tcx) {
                let fip = dtor.did.as_local().is_some_and(|d| is_fip_local(tcx, d));
                if !fip {
                    return Err("its `Drop::drop` is not `#[verifier::fip]`".to_string());
                }
            }
            for variant in adt.variants().iter() {
                for field in variant.fields.iter() {
                    field_ok(field.ty(tcx, args).skip_normalization())?;
                }
            }
            Ok(())
        }
        ty::Tuple(tys) => {
            for t in tys.iter() {
                field_ok(t)?;
            }
            Ok(())
        }
        ty::Array(t, _) | ty::Slice(t) => field_ok(*t),
        _ => Err("its drop glue is not known".to_string()),
    }
}

fn report<'tcx>(tcx: TyCtxt<'tcx>, span: Span, what: String) {
    tcx.dcx().span_err(
        span,
        format!(
            "-V alloc-check: a `#[verifier::fip]` function must not deallocate, but {} (a value whose drop cannot deallocate may be marked `vstd::alloc_check::NoDeallocDrop`)",
            what
        ),
    );
}

/// In a (non-strict) fip function, a call of another crate's function: the functions of this
/// crate that it may call back must be `#[verifier::fip]`
fn check_callbacks<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ext: &ExternalStrict,
    om: &OpMarkers,
    target: DefId,
    targs: ty::GenericArgsRef<'tcx>,
    span: Span,
) {
    let cb = callbacks(tcx, typing_env, target, targs);
    let err = |what: String| {
        tcx.dcx().span_err(
            span,
            format!(
                "-V alloc-check: a `#[verifier::fip]` function must not deallocate, but this call of `{}` may call {}",
                tcx.def_path_str(target),
                what
            ),
        );
    };
    for (d, why) in cb.local.iter() {
        if !d.as_local().is_some_and(|l| is_fip_local(tcx, l)) {
            err(format!(
                "`{}` (through {}), which is not `#[verifier::fip]`",
                tcx.def_path_str(*d),
                why
            ));
        }
    }
    for (d, why) in cb.foreign.iter() {
        if !ext.contains(tcx, *d) {
            err(format!(
                "`{}` (through {}), which is not known here to be `#[verifier::fip]`",
                tcx.def_path_str(*d),
                why
            ));
        }
    }
    for tr in cb.unknown.iter() {
        if om.marked(tcx, typing_env, *tr, false) {
            continue;
        }
        err(format!(
            "the methods of `{}: {}`, which are not known here (an operator trait's methods are known to be `#[verifier::fip]` through its marker, e.g. `vstd::alloc_check::FipOrd`)",
            tr.self_ty(),
            tcx.def_path_str(tr.def_id)
        ));
    }
}

/// The drops of one `#[verifier::fip]` function, on paths that return normally
fn check_fip_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    marker: Option<DefId>,
    at: Option<&AllocTraits>,
    ext: &ExternalStrict,
    om: &OpMarkers,
) {
    let strict = fip_kind_local(tcx, def_id) == Some(true);
    let typing_env = TypingEnv::post_analysis(tcx, def_id.to_def_id());
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body = body.borrow();
    let drop_trait = tcx.lang_items().drop_trait();
    let drop_in_place = tcx.lang_items().drop_glue_fn();
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let term = data.terminator();
        let span = term.source_info.span;
        match &term.kind {
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(&body.local_decls, tcx).ty;
                if drop_may_deallocate(tcx, typing_env, marker, ty) {
                    let hint = if ty.is_box() {
                        " (a `Box` is freed when it is dropped or when its contents are moved out of it; reuse it instead, e.g. `*b = ..`)"
                    } else {
                        ""
                    };
                    report(tcx, span, format!("a value of type `{}` is dropped here{}", ty, hint));
                }
            }
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                let Some((callee, args)) = func.const_fn_def() else { continue };
                if let Some(at) = at {
                    check_allocator_use(tcx, typing_env, at, strict, callee, args, span);
                }
                // (drop elaboration calls `Drop::drop` directly, e.g. for a `Box` whose contents
                // were moved out, which frees the box)
                let is_drop_method =
                    drop_trait.is_some() && tcx.trait_of_assoc(callee) == drop_trait;
                // another crate's code may call back into this crate's (a strict function's
                // callbacks are checked by `strict_edges`)
                if !strict && !is_drop_method && Some(callee) != drop_in_place {
                    if let Some((target, targs)) = call_target(tcx, typing_env, func) {
                        if !target.is_local() {
                            check_callbacks(tcx, typing_env, ext, om, target, targs, span);
                        }
                    }
                }
                if is_drop_method || Some(callee) == drop_in_place {
                    let ty = args.type_at(0);
                    let ty = if Some(callee) == drop_in_place {
                        match ty.kind() {
                            ty::RawPtr(t, _) => *t,
                            _ => ty,
                        }
                    } else {
                        ty
                    };
                    let local_fip = callee.as_local().is_some_and(|d| is_fip_local(tcx, d));
                    if !local_fip
                        && (ty.is_box() || drop_may_deallocate(tcx, typing_env, marker, ty))
                    {
                        report(
                            tcx,
                            span,
                            format!(
                                "a value of type `{}` is dropped here{}",
                                ty,
                                if ty.is_box() {
                                    " (a `Box` is freed when it is dropped or when its contents are moved out of it; reuse it instead, e.g. `*b = ..`)"
                                } else {
                                    ""
                                }
                            ),
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

/// The crates whose functions a `#[verifier::fip(strict)]` function may call (non-tail) as
/// leaves: std's and vstd's functions use bounded stack space, and reach the caller's code only
/// through the trait bounds of their type arguments, which `callbacks` follows (each function of
/// this crate found there is an edge of its own). (By name: under -V alloc-check, which fip
/// needs, rust_to_vir accepts a dependency with one of these names only if it is the real one.)
fn is_trusted_leaf_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let name = tcx.crate_name(def_id.krate);
    matches!(name.as_str(), "core" | "alloc" | "std" | "vstd" | "verus_builtin")
}

/// What a call of another crate's function may call back: the code of a generic function can
/// call the methods of its type arguments only through its trait bounds. So the callee's bounds,
/// instantiated with the call's type arguments (with their supertraits and the bounds of their
/// associated types), lead to the impls it may use; a std impl's own bounds lead further (`Vec<L>:
/// PartialEq` needs `L: PartialEq`). Every function of a selected impl is counted, whichever of
/// them the callee actually uses (a trait's provided methods call only the trait's own methods).
#[derive(Default)]
struct Callbacks<'tcx> {
    /// functions of this crate (impl methods, closures, function items), with the bound that
    /// leads to each
    local: Vec<(DefId, String)>,
    /// functions of crates other than std, vstd and this one
    foreign: Vec<(DefId, String)>,
    /// bounds whose impl is not known here (a type parameter, `dyn`, a function pointer)
    unknown: Vec<ty::TraitRef<'tcx>>,
}

/// Is `def_id` a function that a fip check need not follow as a callback: the hidden methods
/// that `derive(Eq)` generates (they only check, at compile time, that fields are `Eq`)
fn is_compile_time_only(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(tcx.item_name(def_id).as_str(), "assert_receiver_is_total_eq" | "assert_fields_are_eq")
}

/// The operator traits of `core` that vstd has markers for (`vstd::alloc_check::FipAdd`, ...):
/// for each, its name and its `Fip` and `FipStrict` markers
pub(crate) struct OpMarkers {
    ops: std::collections::HashMap<DefId, (&'static str, Option<DefId>, Option<DefId>)>,
}

impl OpMarkers {
    fn new(tcx: TyCtxt<'_>) -> Self {
        let mut ops = std::collections::HashMap::new();
        let traits: Vec<DefId> = tcx.all_traits_including_private().collect();
        for d in traits.iter() {
            if tcx.crate_name(d.krate).as_str() != "core" {
                continue;
            }
            let path = tcx.def_path_str(*d);
            if !(path.contains("::ops::") || path.contains("::cmp::")) {
                continue;
            }
            let name = tcx.item_name(*d);
            let Some(op) = vir::alloc_check::OP_TRAITS.iter().find(|n| **n == name.as_str()) else {
                continue;
            };
            let find = |m: String| {
                traits.iter().copied().find(|t| {
                    tcx.crate_name(t.krate).as_str() == "vstd" && tcx.def_path_str(*t) == m
                })
            };
            let fip = find(format!("vstd::alloc_check::Fip{}", op));
            let strict = find(format!("vstd::alloc_check::FipStrict{}", op));
            ops.insert(*d, (*op, fip, strict));
        }
        OpMarkers { ops }
    }

    /// Does the bound `trait_ref` (of an operator trait) hold through its `Fip` (`FipStrict`)
    /// marker?
    fn marked<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        typing_env: TypingEnv<'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
        strict: bool,
    ) -> bool {
        let Some((_, fip, st)) = self.ops.get(&trait_ref.def_id) else { return false };
        let Some(marker) = (if strict { *st } else { *fip }) else { return false };
        implements_args(tcx, typing_env, marker, trait_ref.args)
    }

    /// The functions of this crate that a strict function may reach through a strict marker of
    /// `op` (for any type): the `#[verifier::fip(strict)]` methods of this crate's impls of `op`
    /// and of its supertraits (an over-approximation: which type the marker is for is not known
    /// where the call is made)
    fn strict_methods(&self, tcx: TyCtxt<'_>, op: DefId) -> Vec<LocalDefId> {
        let mut traits = vec![op];
        for c in rustc_infer::traits::util::supertrait_def_ids(tcx, op) {
            if self.ops.contains_key(&c) && !traits.contains(&c) {
                traits.push(c);
            }
        }
        let mut out = Vec::new();
        for tr in traits {
            for imp in tcx.all_impls(tr) {
                let Some(_) = imp.as_local() else { continue };
                for item in tcx.associated_items(imp).in_definition_order() {
                    if let Some(l) = item.def_id.as_local() {
                        if item.is_fn() && fip_kind_local(tcx, l) == Some(true) {
                            out.push(l);
                        }
                    }
                }
            }
        }
        out
    }
}

fn implements_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    marker: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> bool {
    let args = tcx.erase_and_anonymize_regions(args);
    let (infcx, param_env) = tcx.infer_ctxt().build_with_typing_env(typing_env);
    infcx.type_implements_trait(marker, args.iter(), param_env).must_apply_modulo_regions()
}

fn callbacks<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> Callbacks<'tcx> {
    use rustc_middle::ty::{ClauseKind, Upcast};
    let mut out = Callbacks::default();
    let allocator_traits: Vec<DefId> = tcx
        .all_traits_including_private()
        .filter(|d| {
            tcx.crate_name(d.krate).as_str() == "core"
                && matches!(tcx.item_name(*d).as_str(), "Allocator" | "AllocatorClone")
        })
        .collect();
    let has_fns = |tr: DefId| {
        tcx.associated_items(tr)
            .in_definition_order()
            .any(|i| i.is_fn() && !is_compile_time_only(tcx, i.def_id))
    };
    let mut work: Vec<ty::Clause<'tcx>> = tcx
        .clauses_of(def_id)
        .instantiate(tcx, args)
        .clauses
        .into_iter()
        .map(|c| c.skip_norm_wip())
        .collect();
    let mut seen: std::collections::HashSet<ty::Clause<'tcx>> = std::collections::HashSet::new();
    let impl_fns = |impl_def_id: DefId| -> Vec<DefId> {
        tcx.associated_items(impl_def_id)
            .in_definition_order()
            .filter(|i| i.is_fn())
            .map(|i| i.def_id)
            .filter(|d| !is_compile_time_only(tcx, *d))
            .collect()
    };
    let mut steps = 0;
    while let Some(clause) = work.pop() {
        steps += 1;
        if steps > 10000 {
            break;
        }
        let clause = match tcx
            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(clause))
        {
            Ok(c) => c,
            Err(_) => tcx.erase_and_anonymize_regions(clause),
        };
        if !seen.insert(clause) {
            continue;
        }
        // supertraits
        for c in rustc_infer::traits::util::elaborate(tcx, [clause]).skip(1) {
            work.push(c);
        }
        let ClauseKind::Trait(tp) = clause.kind().skip_binder() else { continue };
        if tp.polarity != ty::ClausePolarity::Positive {
            continue;
        }
        let trait_ref = tp.trait_ref;
        let tr = trait_ref.def_id;
        if allocator_traits.contains(&tr) {
            // (a user allocator is checked by `check_allocator_use`)
            continue;
        }
        // the bounds of the trait's associated types (`I: IntoIterator` lets the callee call
        // `next` on `I::IntoIter`)
        for item in tcx.associated_items(tr).in_definition_order() {
            if item.is_type() {
                for c in tcx
                    .item_bounds(item.def_id)
                    .instantiate(tcx, trait_ref.args)
                    .skip_norm_wip()
                    .iter()
                {
                    work.push(c);
                }
            }
        }
        if !has_fns(tr) {
            continue;
        }
        let what = format!("`{}: {}`", trait_ref.self_ty(), tcx.def_path_str(tr));
        let self_ty = trait_ref.self_ty();
        if tcx.fn_trait_kind_from_def_id(tr).is_some() {
            match self_ty.kind() {
                ty::Closure(d, _) | ty::CoroutineClosure(d, _) if d.is_local() => {
                    out.local.push((*d, what));
                    continue;
                }
                ty::FnDef(d, fargs) => {
                    let Some(fargs) = fargs.no_bound_vars() else {
                        out.unknown.push(trait_ref);
                        continue;
                    };
                    if d.is_local() {
                        out.local.push((*d, what));
                    } else {
                        if !is_trusted_leaf_crate(tcx, *d) {
                            out.foreign.push((*d, what));
                        }
                        work.extend(
                            tcx.clauses_of(*d)
                                .instantiate(tcx, fargs)
                                .clauses
                                .into_iter()
                                .map(|c| c.skip_norm_wip()),
                        );
                    }
                    continue;
                }
                _ => {}
            }
        }
        match tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref)) {
            Ok(rustc_middle::traits::ImplSource::UserDefined(u)) => {
                if u.impl_def_id.is_local() {
                    for f in impl_fns(u.impl_def_id) {
                        out.local.push((f, what.clone()));
                    }
                } else {
                    if !is_trusted_leaf_crate(tcx, u.impl_def_id) {
                        for f in impl_fns(u.impl_def_id) {
                            out.foreign.push((f, what.clone()));
                        }
                    }
                    work.extend(
                        tcx.clauses_of(u.impl_def_id)
                            .instantiate(tcx, u.args)
                            .clauses
                            .into_iter()
                            .map(|c| c.skip_norm_wip()),
                    );
                }
            }
            Ok(rustc_middle::traits::ImplSource::Builtin(_, _)) => {
                // compiler-provided impls: `Clone` of tuples, arrays and closures clones the
                // parts; the others (`Sized`, `Copy`, `Fn` of function pointers, ...) run no user
                // code, except through `dyn` and function pointers
                let is_clone = Some(tr) == tcx.lang_items().clone_trait();
                let parts: Vec<Ty<'tcx>> = match self_ty.kind() {
                    ty::Dynamic(..) | ty::FnPtr(..) => {
                        out.unknown.push(trait_ref);
                        continue;
                    }
                    _ if !is_clone => vec![],
                    ty::Tuple(ts) => ts.iter().collect(),
                    ty::Array(t, _) | ty::Slice(t) => vec![*t],
                    ty::Closure(_, cargs) => cargs.as_closure().upvar_tys().iter().collect(),
                    _ => vec![],
                };
                for t in parts {
                    let tref = ty::TraitRef::new(tcx, tr, [t]);
                    work.push(tref.upcast(tcx));
                }
            }
            Ok(rustc_middle::traits::ImplSource::Param(_)) | Err(_) => {
                out.unknown.push(trait_ref);
            }
        }
    }
    out
}

/// The function (and its type arguments) that a call runs, if that is known here: the impl
/// method that a trait method call resolves to
fn call_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
) -> Option<(DefId, ty::GenericArgsRef<'tcx>)> {
    let (def_id, args) = func.const_fn_def()?;
    match ty::Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(instance)) => Some((instance.def_id(), instance.args)),
        // (a generic call of a trait method: its impl is not known here, which the checks of
        // generic calls handle)
        _ => None,
    }
}

/// A call (or a destructor run by a drop) of a strict fip function: the callee, and whether it
/// is a tail call (`become`)
struct StrictEdge {
    callee: LocalDefId,
    tail: bool,
    span: Span,
}

fn resolve_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
) -> Option<DefId> {
    let (def_id, args) = func.const_fn_def()?;
    match ty::Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(instance)) => Some(instance.def_id()),
        _ => None,
    }
}

/// The destructors that dropping a value of type `ty` runs (`out`), and the types in it whose drop
/// glue is not known here (`unknown`: type parameters, associated and opaque types, `dyn`). A
/// std type is assumed to drop exactly its type arguments (its fields may hide them behind raw
/// pointers: `Vec<T>`, `Box<T>`).
fn drop_glue_destructors<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    out: &mut Vec<DefId>,
    unknown: &mut Vec<Ty<'tcx>>,
    seen: &mut std::collections::HashSet<Ty<'tcx>>,
) {
    if !ty.needs_drop(tcx, typing_env) || !seen.insert(ty) {
        return;
    }
    match ty.kind() {
        ty::Adt(adt, args) => {
            if let Some(dtor) = adt.destructor(tcx) {
                out.push(dtor.did);
            }
            if adt.did().is_local() {
                for variant in adt.variants().iter() {
                    for field in variant.fields.iter() {
                        let fty = field.ty(tcx, args).skip_normalization();
                        drop_glue_destructors(tcx, typing_env, fty, out, unknown, seen);
                    }
                }
            } else {
                for t in args.types() {
                    drop_glue_destructors(tcx, typing_env, t, out, unknown, seen);
                }
            }
        }
        ty::Tuple(tys) => {
            for t in tys.iter() {
                drop_glue_destructors(tcx, typing_env, t, out, unknown, seen);
            }
        }
        ty::Array(t, _) | ty::Slice(t) => {
            drop_glue_destructors(tcx, typing_env, *t, out, unknown, seen)
        }
        ty::Closure(_, args) => {
            for t in args.as_closure().upvar_tys() {
                drop_glue_destructors(tcx, typing_env, t, out, unknown, seen);
            }
        }
        _ => unknown.push(ty),
    }
}

/// Does dropping a value of type `ty` run user code (a destructor outside std, or one not known
/// here)? Returns a description if so.
pub(crate) fn user_drop_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<String> {
    let (mut dtors, mut unknown) = (Vec::new(), Vec::new());
    drop_glue_destructors(
        tcx,
        typing_env,
        ty,
        &mut dtors,
        &mut unknown,
        &mut std::collections::HashSet::new(),
    );
    if let Some(u) = unknown.first() {
        return Some(format!("a `{}`, whose destructor is not known here", u));
    }
    dtors
        .iter()
        .find(|d| !is_trusted_leaf_crate(tcx, **d))
        .map(|d| format!("it runs `{}`", tcx.def_path_str(*d)))
}

fn strict_err<'tcx>(tcx: TyCtxt<'tcx>, span: Span, what: String) {
    tcx.dcx().span_err(
        span,
        format!(
            "-V alloc-check: a `#[verifier::fip(strict)]` function must use constant stack space, but {}",
            what
        ),
    );
}

/// The `#[verifier::fip(strict)]` functions of other crates that were verified and compiled with
/// -V alloc-check (by VIR path): their compilation checked that they, and everything they reach in
/// their own crate, use constant stack space. They can call back into this crate only through the
/// trait bounds of the type arguments a call gives them (a strict function's own calls go to
/// known functions, or to an operator trait's methods through a strict marker, which is such a
/// bound): `callbacks` follows those bounds to this crate's functions.
pub(crate) struct ExternalStrict {
    verus_items: crate::verus_items::VerusItems,
    paths: std::collections::HashSet<String>,
    /// the std functions (and vstd's) that vstd marks `#[verifier::alloc_check_skip_drops]`: they
    /// drop no value of their type arguments (`mem::swap`, `<[T]>::split_at_mut`)
    no_drop: std::collections::HashSet<String>,
}

impl ExternalStrict {
    fn drops_nothing<'tcx>(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
        !def_id.is_local()
            && !self.no_drop.is_empty()
            && crate::rust_to_vir_path::def_id_to_vir_path_option(tcx, &self.verus_items, def_id)
                .is_some_and(|p| self.no_drop.contains(&format!("{:?}", p)))
    }

    fn contains<'tcx>(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
        !def_id.is_local()
            && !self.paths.is_empty()
            && crate::rust_to_vir_path::def_id_to_vir_path_option(tcx, &self.verus_items, def_id)
                .is_some_and(|p| self.paths.contains(&format!("{:?}", p)))
    }
}

/// The calls of one strict fip function (on paths that return normally), checked to go to strict
/// fip functions, std/vstd or strict functions of other crates; with the functions of this crate
/// that those may call back, and the destructors that drops run, as edges
fn strict_edges<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    at: Option<&AllocTraits>,
    ext: &ExternalStrict,
    om: &OpMarkers,
) -> (Vec<StrictEdge>, bool) {
    let mut uses_allocator = false;
    let typing_env = TypingEnv::post_analysis(tcx, def_id.to_def_id());
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body = body.borrow();
    let mut edges = Vec::new();
    let add = |callee: DefId, tail: bool, span: Span, edges: &mut Vec<StrictEdge>| match callee
        .as_local()
    {
        Some(local) => {
            if fip_kind_local(tcx, local) == Some(true) {
                edges.push(StrictEdge { callee: local, tail, span });
            } else {
                strict_err(
                    tcx,
                    span,
                    format!(
                        "it calls `{}`, which is not `#[verifier::fip(strict)]`",
                        tcx.def_path_str(callee)
                    ),
                );
            }
        }
        None if is_trusted_leaf_crate(tcx, callee) => {}
        // (a strict function of another crate verified with -V alloc-check: a leaf, also as the
        // target of a tail call, whose own frame is then constant too)
        None if ext.contains(tcx, callee) => {}
        None => strict_err(
            tcx,
            span,
            format!(
                "it calls `{}` from another crate, whose stack use is not known here (another crate's function is known only if it is `#[verifier::fip(strict)]` and its crate was verified and compiled with -V alloc-check and imported with its library file)",
                tcx.def_path_str(callee)
            ),
        ),
    };
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup {
            continue;
        }
        let term = data.terminator();
        let span = term.source_info.span;
        match &term.kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                let tail = matches!(&term.kind, TerminatorKind::TailCall { .. });
                if let (Some(at), Some((callee, args))) = (at, func.const_fn_def()) {
                    // (also a strict function of another crate instantiated with a user
                    // allocator: it may call the allocator's methods, which may lead back here)
                    if !user_allocators(tcx, typing_env, at, args).is_empty()
                        && (is_trusted_leaf_crate(tcx, callee) || ext.contains(tcx, callee))
                    {
                        uses_allocator = true;
                    }
                }
                // std code may drop values of its type arguments (`Vec::<H>::clear`, `truncate`),
                // which runs their destructors from inside the call (unless vstd's specification
                // says that the function drops none of them)
                if let (Some((callee, args)), Some(_)) =
                    (func.const_fn_def(), resolve_callee(tcx, typing_env, func))
                {
                    // (a trait method's specification is that of the impl's method, so the
                    // resolved callee is looked up too)
                    let drops_nothing = ext.drops_nothing(tcx, callee)
                        || resolve_callee(tcx, typing_env, func)
                            .is_some_and(|c| ext.drops_nothing(tcx, c));
                    if is_trusted_leaf_crate(tcx, callee) && !drops_nothing {
                        let (mut dtors, mut unknown) = (Vec::new(), Vec::new());
                        let mut seen = std::collections::HashSet::new();
                        for t in args.types() {
                            drop_glue_destructors(
                                tcx,
                                typing_env,
                                t,
                                &mut dtors,
                                &mut unknown,
                                &mut seen,
                            );
                        }
                        for d in dtors {
                            add(d, false, span, &mut edges);
                        }
                        if let Some(u) = unknown.first() {
                            strict_err(
                                tcx,
                                span,
                                format!(
                                    "it calls `{}`, which may drop a value of type `{}`, whose destructor is not known here",
                                    tcx.def_path_str(callee),
                                    u
                                ),
                            );
                        }
                    }
                }
                // another crate's code may call back into this crate's (a non-tail call: the
                // callee's frame stays below)
                if let Some((target, targs)) = call_target(tcx, typing_env, func) {
                    let is_drop = func.const_fn_def().is_some_and(|(c, _)| {
                        Some(c) == tcx.lang_items().drop_glue_fn()
                            || (tcx.lang_items().drop_trait().is_some()
                                && tcx.trait_of_assoc(c) == tcx.lang_items().drop_trait())
                    });
                    if !target.is_local() && !is_drop {
                        let cb = callbacks(tcx, typing_env, target, targs);
                        for (d, why) in cb.local.iter() {
                            match d.as_local() {
                                Some(l) if fip_kind_local(tcx, l) == Some(true) => {
                                    edges.push(StrictEdge { callee: l, tail: false, span });
                                }
                                _ => strict_err(
                                    tcx,
                                    span,
                                    format!(
                                        "it calls `{}`, which may call `{}` (through {}), which is not `#[verifier::fip(strict)]`",
                                        tcx.def_path_str(target),
                                        tcx.def_path_str(*d),
                                        why
                                    ),
                                ),
                            }
                        }
                        for (d, why) in cb.foreign.iter() {
                            if !ext.contains(tcx, *d) {
                                strict_err(
                                    tcx,
                                    span,
                                    format!(
                                        "it calls `{}`, which may call `{}` (through {}), whose stack use is not known here",
                                        tcx.def_path_str(target),
                                        tcx.def_path_str(*d),
                                        why
                                    ),
                                );
                            }
                        }
                        for tr in cb.unknown.iter() {
                            if om.marked(tcx, typing_env, *tr, true) {
                                for m in om.strict_methods(tcx, tr.def_id) {
                                    edges.push(StrictEdge { callee: m, tail: false, span });
                                }
                                continue;
                            }
                            strict_err(
                                tcx,
                                span,
                                format!(
                                    "it calls `{}`, which may call the methods of `{}: {}`, which are not known here (an operator trait's methods are known to be `#[verifier::fip(strict)]` through its marker, e.g. `vstd::alloc_check::FipStrictOrd`)",
                                    tcx.def_path_str(target),
                                    tr.self_ty(),
                                    tcx.def_path_str(tr.def_id)
                                ),
                            );
                        }
                    }
                }
                // a generic call of an operator trait's method, through its strict marker (not
                // `Ord::{max, min, clamp}`, which drop a value whose destructor is not known)
                let marked_op = func.const_fn_def().and_then(|(callee, args)| {
                    let tr = tcx.trait_of_assoc(callee)?;
                    if !om.ops.contains_key(&tr)
                        || matches!(tcx.item_name(callee).as_str(), "max" | "min" | "clamp")
                    {
                        return None;
                    }
                    let n = tcx.generics_of(tr).count();
                    let trait_ref = ty::TraitRef::new_from_args(tcx, tr, tcx.mk_args(&args[..n]));
                    om.marked(tcx, typing_env, trait_ref, true).then_some(tr)
                });
                match resolve_callee(tcx, typing_env, func) {
                    Some(callee) => add(callee, tail, span, &mut edges),
                    None if marked_op.is_some() => {
                        for m in om.strict_methods(tcx, marked_op.unwrap()) {
                            edges.push(StrictEdge { callee: m, tail: false, span });
                        }
                    }
                    None => strict_err(
                        tcx,
                        span,
                        "it makes a call whose callee is not known here (a generic call, or a call of a function value)".to_string(),
                    ),
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(&body.local_decls, tcx).ty;
                let (mut dtors, mut unknown) = (Vec::new(), Vec::new());
                drop_glue_destructors(
                    tcx,
                    typing_env,
                    ty,
                    &mut dtors,
                    &mut unknown,
                    &mut std::collections::HashSet::new(),
                );
                for d in dtors {
                    add(d, false, span, &mut edges);
                }
                if let Some(u) = unknown.first() {
                    strict_err(
                        tcx,
                        span,
                        format!(
                            "it drops a value of type `{}`, whose destructor is not known here (a type parameter, an associated or opaque type, or `dyn`; a `Copy` bound rules out a destructor)",
                            u
                        ),
                    );
                }
            }
            _ => {}
        }
    }
    (edges, uses_allocator)
}

/// Constant stack space: a call that is not a tail call adds a frame, so no cycle of calls may
/// go through one (a cycle of tail calls only replaces frames). The calls that leave the strict
/// functions go to std/vstd, which do not call back.
///
/// A call of std code with a user allocator may call the allocator's (strict) methods, which
/// does not appear as an edge: so no function that such a method can reach may itself use a user
/// allocator (otherwise the allocator could call back into it).
fn check_strict_stack<'tcx>(
    tcx: TyCtxt<'tcx>,
    strict: &[LocalDefId],
    at: Option<&AllocTraits>,
    allocator_methods: &[(LocalDefId, Span)],
    ext: &ExternalStrict,
    om: &OpMarkers,
) {
    let mut uses_allocator: std::collections::HashSet<LocalDefId> =
        std::collections::HashSet::new();
    let graph: std::collections::HashMap<LocalDefId, Vec<StrictEdge>> = strict
        .iter()
        .map(|f| {
            let (edges, uses) = strict_edges(tcx, *f, at, ext, om);
            if uses {
                uses_allocator.insert(*f);
            }
            (*f, edges)
        })
        .collect();
    for (m, span) in allocator_methods.iter() {
        let mut seen = std::collections::HashSet::new();
        let mut work = vec![*m];
        while let Some(f) = work.pop() {
            if !seen.insert(f) {
                continue;
            }
            if uses_allocator.contains(&f) {
                tcx.dcx().span_err(
                    *span,
                    format!(
                        "-V alloc-check: this `FipStrictAllocator` impl is not accepted: its `{}` can reach `{}`, which uses a user allocator itself (the allocator could call back into it, growing the stack)",
                        tcx.def_path_str(m.to_def_id()),
                        tcx.def_path_str(f.to_def_id())
                    ),
                );
                break;
            }
            if let Some(es) = graph.get(&f) {
                work.extend(es.iter().map(|e| e.callee));
            }
        }
    }
    let reaches = |from: LocalDefId, to: LocalDefId| -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut work = vec![from];
        while let Some(f) = work.pop() {
            if f == to {
                return true;
            }
            if !seen.insert(f) {
                continue;
            }
            if let Some(es) = graph.get(&f) {
                work.extend(es.iter().map(|e| e.callee));
            }
        }
        false
    };
    for (f, edges) in graph.iter() {
        for e in edges.iter() {
            if !e.tail && reaches(e.callee, *f) {
                strict_err(
                    tcx,
                    e.span,
                    format!(
                        "this call of `{}` is not a tail call and can lead back to `{}` (recursion that is not through `become` grows the stack)",
                        tcx.def_path_str(e.callee.to_def_id()),
                        tcx.def_path_str(f.to_def_id())
                    ),
                );
            }
        }
    }
}

/// Checks every `#[verifier::fip]` function of the crate and every `NoDeallocDrop`,
/// `FipAllocator` and `FipStrictAllocator` impl; returns
/// whether there are fip functions. (The impls of other crates were checked when those crates
/// were compiled: `checked` lists the dependencies verified with -V alloc-check.)
pub(crate) fn check_fip_crate<'tcx>(
    tcx: TyCtxt<'tcx>,
    checked: &[(String, u128)],
    strict_fns: &[String],
    no_drop_fns: &[String],
) -> bool {
    let ext = ExternalStrict {
        verus_items: crate::verus_items::from_diagnostic_items(tcx),
        paths: strict_fns.iter().cloned().collect(),
        no_drop: no_drop_fns.iter().cloned().collect(),
    };
    let om = OpMarkers::new(tcx);
    let marker = tcx.all_traits_including_private().find(|d| tcx.def_path_str(*d) == MARKER);
    if let Some(m) = marker {
        check_marker_impls(tcx, m, checked);
    }
    let at = alloc_traits(tcx);
    let allocator_methods = match &at {
        Some(at) => check_fip_allocator_impls(tcx, at, checked),
        None => Vec::new(),
    };
    let mut any = false;
    let mut strict: Vec<LocalDefId> = Vec::new();
    for def_id in tcx.hir_body_owners() {
        if !matches!(
            tcx.def_kind(def_id),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            continue;
        }
        if !is_fip_local(tcx, def_id) {
            continue;
        }
        any = true;
        if fip_kind_local(tcx, def_id) == Some(true) {
            strict.push(def_id);
        }
        check_fip_body(tcx, def_id, marker, at.as_ref(), &ext, &om);
    }
    check_strict_stack(tcx, &strict, at.as_ref(), &allocator_methods, &ext, &om);
    any
}

/// `-V fip-lint`: a recursive call in tail position that is not a tail call. Rust does not
/// guarantee that it replaces the caller's frame (it does not at opt-level=0, nor when a drop is
/// pending after the call); `become` does. (Recursion modulo a constructor is found on VIR,
/// `vir::fip_lint`.)
pub(crate) fn lint_tail_calls<'tcx>(tcx: TyCtxt<'tcx>) {
    use rustc_middle::mir::{Operand, RETURN_PLACE, Rvalue, StatementKind};
    let fns: Vec<LocalDefId> = tcx
        .hir_body_owners()
        .filter(|d| {
            matches!(
                tcx.def_kind(*d),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            )
        })
        .collect();
    let mut graph: std::collections::HashMap<LocalDefId, Vec<LocalDefId>> =
        std::collections::HashMap::new();
    let mut candidates: Vec<(LocalDefId, LocalDefId, Span, Vec<String>)> = Vec::new();
    for f in fns.iter() {
        let typing_env = TypingEnv::post_analysis(tcx, f.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(*f);
        let body = body.borrow();
        let mut out = Vec::new();
        for (_bb, data) in body.basic_blocks.iter_enumerated() {
            if data.is_cleanup {
                continue;
            }
            let term = data.terminator();
            let (func, destination, target) = match &term.kind {
                TerminatorKind::Call { func, destination, target, .. } => {
                    (func, Some(*destination), *target)
                }
                TerminatorKind::TailCall { func, .. } => (func, None, None),
                _ => continue,
            };
            let Some(callee) = resolve_callee(tcx, typing_env, func).and_then(|d| d.as_local())
            else {
                continue;
            };
            out.push(callee);
            // Is the call in tail position: its result goes to the return place (directly, or
            // moved there), and only drops and jumps follow it before `return`?
            let Some(dest) = destination else { continue };
            if !dest.projection.is_empty() {
                continue;
            }
            let dest_local = dest.local;
            let mut pending: Vec<String> = Vec::new();
            let mut bb = target;
            let mut is_tail = false;
            let mut steps = 0;
            while let Some(b) = bb {
                steps += 1;
                if steps > 64 {
                    break;
                }
                let d = &body.basic_blocks[b];
                let stmts_ok = d.statements.iter().all(|st| match &st.kind {
                    StatementKind::StorageDead(_)
                    | StatementKind::StorageLive(_)
                    | StatementKind::Nop => true,
                    StatementKind::Assign(assign) => {
                        let (lhs, rhs) = &**assign;
                        lhs.local == RETURN_PLACE
                            && lhs.projection.is_empty()
                            && matches!(rhs, Rvalue::Use(Operand::Move(p), ..)
                                if p.local == dest_local && p.projection.is_empty())
                    }
                    _ => false,
                });
                if !stmts_ok {
                    break;
                }
                match &d.terminator().kind {
                    TerminatorKind::Goto { target } => bb = Some(*target),
                    TerminatorKind::Drop { place, target, .. } => {
                        let ty = place.ty(&body.local_decls, tcx).ty;
                        pending.push(format!("`{}`", ty));
                        bb = Some(*target);
                    }
                    TerminatorKind::Return => {
                        is_tail = true;
                        break;
                    }
                    _ => break,
                }
            }
            if is_tail {
                candidates.push((*f, callee, term.source_info.span, pending));
            }
        }
        graph.insert(*f, out);
    }
    let reaches = |from: LocalDefId, to: LocalDefId| -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut work = vec![from];
        while let Some(f) = work.pop() {
            if f == to {
                return true;
            }
            if !seen.insert(f) {
                continue;
            }
            if let Some(es) = graph.get(&f) {
                work.extend(es.iter().copied());
            }
        }
        false
    };
    let sig = |d: LocalDefId| {
        tcx.erase_and_anonymize_regions(
            tcx.fn_sig(d.to_def_id()).instantiate_identity().skip_normalization().skip_binder(),
        )
    };
    for (f, callee, span, pending) in candidates {
        if !reaches(callee, f) {
            continue;
        }
        let mut msg = format!(
            "-V fip-lint: this recursive call of `{}` is in tail position but is not a tail call, so it may not replace the frame of `{}` (Rust does not guarantee that at opt-level=0",
            tcx.def_path_str(callee.to_def_id()),
            tcx.def_path_str(f.to_def_id()),
        );
        if pending.is_empty() {
            msg.push(')');
        } else {
            msg.push_str(&format!(
                ", nor here, where a drop is pending after the call: {})",
                pending.join(", ")
            ));
        }
        msg.push_str("; `become` (`#![feature(explicit_tail_calls)]`) guarantees it");
        if !pending.is_empty() {
            msg.push_str(", dropping those values before the call");
        }
        if sig(f) != sig(callee) {
            msg.push_str(
                " (but `become` needs the callee to have the same signature as the caller)",
            );
        }
        tcx.dcx().span_warn(span, msg);
    }
}
