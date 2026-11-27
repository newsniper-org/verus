//! `.verus-hints`: how to check some obligations, kept out of the source.
//!
//! A hints file says only *how* an obligation is checked: the rlimit of a function, and which
//! `ensures` checks are a part of the query of their own (`isolate`, with its rlimit and solver).
//! It never says *what* is checked: no formula, no lemma, no `assume`. So a hint, applied or not,
//! cannot make a program verify that does not hold; at worst a proof runs out of its rlimit.
//!
//! Each entry is pinned to the code it was written for by a hash of that code's text (the
//! function's item, or the `ensures` clause), with the whitespace normalized. An entry that does
//! not match the code (stale hash, no hash, no such function or clause) is not applied: the
//! obligation is checked as the source alone says, with a warning. With `-V hints-locked`, such
//! an entry is an error instead.
//!
//! The hints are applied to the functions of this crate after the crate is exported, so another
//! crate never sees them, and before the verifier reads the crate (`Verifier::vir_crate`), in the
//! same form as the attributes they stand for (`#[verifier::rlimit(..)]`,
//! `#[verifier::tactic(isolate(..))]` on a function or an `ensures` clause), which they replace.

use crate::config::Args;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use vir::ast::{
    ExprX, Fun, Function, FunctionKind, IsolateBackend, IsolateSpec, Krate, KrateX, ProofNoteLabel,
    UnaryOpr, VirErr,
};
use vir::messages::{Message, MessageLevel, Span, ToAny};

/// The name of the hints file that Verus looks for
pub const HINTS_FILE_NAME: &str = ".verus-hints";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct HintsFile {
    #[serde(default)]
    hint: Vec<HintEntry>,
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct HintEntry {
    function: String,
    #[serde(default)]
    root: Option<String>,
    #[serde(default)]
    ensures: Option<i64>,
    #[serde(default)]
    proof_note: Option<String>,
    #[serde(default)]
    hash: Option<String>,
    #[serde(default)]
    rlimit: Option<RlimitValue>,
    #[serde(default)]
    isolate: Option<IsolateEntry>,
}

#[derive(Deserialize, Clone)]
#[serde(untagged)]
enum RlimitValue {
    Number(f64),
    Text(String),
}

#[derive(Deserialize, Clone)]
#[serde(deny_unknown_fields)]
struct IsolateEntry {
    #[serde(default)]
    rlimit: Option<RlimitValue>,
    #[serde(default)]
    backend: Option<String>,
}

/// The crate root file, if the crate is read from one
pub(crate) fn crate_root(tcx: TyCtxt<'_>) -> Option<PathBuf> {
    match &tcx.sess.io.input {
        rustc_session::config::Input::File(path) => Some(path.clone()),
        _ => None,
    }
}

/// The hints file for this crate, if any:
/// - none for a crate that is not verified (`--no-verify`, such as a dependency);
/// - `-V hints=<path>` for the crate being verified (with cargo, a primary package:
///   `explicit_applies`);
/// - else the first `.verus-hints` in the directory of the crate root file and its parents, up to
///   the nearest one with a `Cargo.toml` (with none above the root file, only its own directory).
pub(crate) fn hints_file(
    args: &Args,
    crate_root: Option<&Path>,
    explicit_applies: bool,
) -> Option<PathBuf> {
    if args.no_verify {
        return None;
    }
    if let Some(path) = &args.hints {
        if explicit_applies {
            return Some(PathBuf::from(path));
        }
    }
    let root = crate_root?;
    let root = std::fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
    let mut dirs: Vec<&Path> = vec![];
    let mut cargo = false;
    for d in root.parent()?.ancestors() {
        dirs.push(d);
        if d.join("Cargo.toml").is_file() {
            cargo = true;
            break;
        }
    }
    if !cargo {
        dirs.truncate(1);
    }
    dirs.into_iter().map(|d| d.join(HINTS_FILE_NAME)).find(|c| c.is_file())
}

/// FNV-1a (64 bits) of the text with its whitespace normalized: the hash that pins an entry to
/// the code it was written for (only to tell when the code changed; not a security measure)
fn code_hash(text: &str) -> String {
    let normalized = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut h: u64 = 0xcbf29ce484222325;
    for b in normalized.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("{:016x}", h)
}

fn parse_rlimit(value: &RlimitValue) -> Option<f32> {
    match value {
        RlimitValue::Number(n) if n.is_finite() && *n >= 0.0 => Some(*n as f32),
        RlimitValue::Text(t) if t == "infinity" => Some(f32::INFINITY),
        _ => None,
    }
}

fn rlimit_toml(value: &RlimitValue) -> String {
    match value {
        RlimitValue::Number(n) if n.fract() == 0.0 && n.abs() < 1e15 => format!("{}", *n as i64),
        RlimitValue::Number(n) => format!("{}", n),
        RlimitValue::Text(t) => toml_string(t),
    }
}

fn toml_string(s: &str) -> String {
    toml::Value::String(s.to_string()).to_string()
}

/// The entry for the current code (named `function`, with `hash`): what a warning shows to paste
/// into the hints file
fn entry_toml(entry: &HintEntry, function: &str, hash: &str) -> String {
    let mut lines = vec!["[[hint]]".to_string(), format!("function = {}", toml_string(function))];
    if let Some(root) = &entry.root {
        lines.push(format!("root = {}", toml_string(root)));
    }
    if let Some(n) = entry.ensures {
        lines.push(format!("ensures = {}", n));
    }
    if let Some(note) = &entry.proof_note {
        lines.push(format!("proof_note = {}", toml_string(note)));
    }
    lines.push(format!("hash = {}", toml_string(hash)));
    if let Some(r) = &entry.rlimit {
        lines.push(format!("rlimit = {}", rlimit_toml(r)));
    }
    if let Some(iso) = &entry.isolate {
        let mut opts = vec![];
        if let Some(r) = &iso.rlimit {
            opts.push(format!("rlimit = {}", rlimit_toml(r)));
        }
        if let Some(b) = &iso.backend {
            opts.push(format!("backend = {}", toml_string(b)));
        }
        if opts.is_empty() {
            lines.push("isolate = {}".to_string());
        } else {
            lines.push(format!("isolate = {{ {} }}", opts.join(", ")));
        }
    }
    lines.join("\n")
}

/// The text of the code at a span, if it is in a file of this crate. (For code that a
/// `macro_rules!` macro generates, this is the macro's text, not the arguments of its call.)
fn snippet(tcx: TyCtxt<'_>, span: rustc_span::Span) -> Option<String> {
    tcx.sess.source_map().span_to_snippet(span).ok()
}

/// The names of a function in a hints file: its path in the crate (`m::f`, `S::f`), also with
/// `crate::` or the crate's name in front; the first is the one that messages show
fn names_of(fun: &Fun) -> Vec<String> {
    let full = vir::ast_util::fun_as_friendly_rust_name(fun);
    match full.split_once("::") {
        Some((_, rest)) => vec![rest.to_string(), format!("crate::{rest}"), full.clone()],
        None => vec![full],
    }
}

/// The top-level label of an `ensures` clause (`proof_note`, or one that carries only `isolate`)
fn clause_label(e: &vir::ast::Expr) -> Option<&ProofNoteLabel> {
    match &e.x {
        ExprX::UnaryOpr(UnaryOpr::ProofNote(label), _) => Some(label),
        _ => None,
    }
}

/// What a hint is for, in the current code
struct Target {
    fun: Fun,
    /// the index of the function in the crate's functions
    fi: usize,
    /// the `ensures` clause (from 0), for a hint about a clause
    clause: Option<usize>,
    span: Span,
    /// the hash of the code
    hash: String,
    /// the name to show for the function (the one in the entry, or rustc's full path)
    name: String,
}

enum Resolved {
    Target(Target),
    /// the hint does not apply to this function (a warning, or an error with `-V hints-locked`)
    NotApplied(Message),
}

struct Ctx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    shown: &'a str,
    functions: &'a Vec<Function>,
    index: &'a HashMap<Fun, usize>,
    local_def: &'a HashMap<&'a Fun, rustc_span::def_id::LocalDefId>,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    fn bad(&self, n: usize, msg: String) -> VirErr {
        vir::messages::error_bare(format!("`{}`, hint {n}: {msg}", self.shown))
    }

    /// The target of an entry in the function `fun` (named `name`), with its hash
    fn resolve(
        &self,
        n: usize,
        entry: &HintEntry,
        isolate: bool,
        fun: &Fun,
        name: &str,
    ) -> Result<Resolved, VirErr> {
        let shown = self.shown;
        let Some(&fi) = self.index.get(fun) else {
            return Ok(Resolved::NotApplied(vir::messages::warning_bare(format!(
                "`{shown}`, hint {n}: `{name}` is not a function of this crate; the hint was not applied"
            ))));
        };
        let function = &self.functions[fi];
        if isolate && matches!(function.x.kind, FunctionKind::TraitMethodDecl { .. }) {
            return Err(self.bad(
                n,
                format!(
                    "`isolate` is not allowed for a trait method declaration, `{name}` (give the implementations hints)"
                ),
            ));
        }
        if function.x.body.is_none() {
            return Ok(Resolved::NotApplied(vir::messages::warning(
                &function.span,
                format!(
                    "`{shown}`, hint {n}: `{name}` has no body to check; the hint was not applied"
                ),
            )));
        }
        let ensures = &function.x.ensure.0;
        let clause: Option<usize> = match (&entry.ensures, &entry.proof_note) {
            (Some(k), _) => {
                let k = *k as usize;
                if k > ensures.len() {
                    let clauses = if ensures.len() == 1 { "clause" } else { "clauses" };
                    return Ok(Resolved::NotApplied(vir::messages::warning(
                        &function.span,
                        format!(
                            "`{shown}`, hint {n}: `{name}` has {} `ensures` {clauses}, not {k}; the hint was not applied",
                            ensures.len()
                        ),
                    )));
                }
                Some(k - 1)
            }
            (None, Some(note)) => {
                let found: Vec<usize> = ensures
                    .iter()
                    .enumerate()
                    .filter(|(_, e)| clause_label(e).map_or(false, |l| *l.text == *note))
                    .map(|(j, _)| j)
                    .collect();
                match found.len() {
                    0 => {
                        return Ok(Resolved::NotApplied(vir::messages::warning(
                            &function.span,
                            format!(
                                "`{shown}`, hint {n}: `{name}` has no `ensures` clause with the proof note \"{note}\"; the hint was not applied"
                            ),
                        )));
                    }
                    1 => Some(found[0]),
                    _ => {
                        return Err(self.bad(
                            n,
                            format!(
                                "more than one `ensures` clause of `{name}` has the proof note \"{note}\"; use `ensures = N`"
                            ),
                        ));
                    }
                }
            }
            (None, None) => None,
        };
        let (span, code) = match clause {
            Some(j) => {
                let ens = &ensures[j];
                let code = crate::spans::from_raw_span(&ens.span.raw_span)
                    .and_then(|s| snippet(self.tcx, s));
                (ens.span.clone(), code)
            }
            None => {
                let code = self.local_def.get(fun).and_then(|d| {
                    let hir_id = self.tcx.local_def_id_to_hir_id(*d);
                    snippet(self.tcx, self.tcx.hir_span_with_body(hir_id))
                });
                (function.span.clone(), code)
            }
        };
        let Some(code) = code else {
            return Ok(Resolved::NotApplied(vir::messages::warning(
                &span,
                format!(
                    "`{shown}`, hint {n}: the source of `{name}` is not available; the hint was not applied"
                ),
            )));
        };
        Ok(Resolved::Target(Target {
            fun: fun.clone(),
            fi,
            clause,
            span,
            hash: code_hash(&code),
            name: name.to_string(),
        }))
    }
}

/// Apply the entries of the hints file (`hints_file`) to this crate's functions in `krate`
pub(crate) fn apply_hints<'tcx>(
    tcx: TyCtxt<'tcx>,
    args: &Args,
    path: Option<&Path>,
    local_crate: &Krate,
    krate: Krate,
    def_id_to_fun: &HashMap<DefId, Option<Fun>>,
    diagnostics: &impl air::messages::Diagnostics,
) -> Result<Krate, VirErr> {
    let Some(path) = path else {
        return Ok(krate);
    };
    let shown = path.display().to_string();
    let text = std::fs::read_to_string(&path).map_err(|e| {
        vir::messages::error_bare(format!("cannot read the hints file `{shown}`: {e}"))
    })?;
    let file: HintsFile = toml::from_str(&text).map_err(|e| {
        vir::messages::error_bare(format!("the hints file `{shown}` is not valid: {e}"))
    })?;
    // (`root = ..` is relative to the directory of the hints file)
    let base = path.parent().map(|p| std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf()));
    let this_root = crate_root(tcx).map(|r| std::fs::canonicalize(&r).unwrap_or(r));

    // this crate's functions, by the names that a hints file may use: the path in the crate, and
    // rustc's full path (`<S as T>::f`), which tells apart methods of the same name
    let local: HashSet<&Fun> = local_crate.functions.iter().map(|f| &f.x.name).collect();
    let local_def: HashMap<&Fun, rustc_span::def_id::LocalDefId> =
        def_id_to_fun.iter().filter_map(|(d, f)| Some((f.as_ref()?, d.as_local()?))).collect();
    let full_name = |fun: &Fun| -> Option<String> {
        let d = local_def.get(fun)?;
        Some(rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(d.to_def_id())))
    };
    let mut by_name: HashMap<String, Vec<Fun>> = HashMap::new();
    for f in local_crate.functions.iter() {
        let mut names = names_of(&f.x.name);
        if let Some(q) = full_name(&f.x.name) {
            names.push(format!("crate::{q}"));
            names.push(q);
        }
        names.sort();
        names.dedup();
        for name in names {
            by_name.entry(name).or_default().push(f.x.name.clone());
        }
    }
    let mut functions: Vec<Function> = krate.functions.clone();
    let index: HashMap<Fun, usize> = functions
        .iter()
        .enumerate()
        .filter(|(_, f)| local.contains(&f.x.name))
        .map(|(i, f)| (f.x.name.clone(), i))
        .collect();

    let cvc5_encoding = matches!(args.smt_encoding, air::context::SmtEncoding::Cvc5);
    let mut targets: HashSet<(Fun, Option<usize>)> = HashSet::new();
    let mut not_applied: Vec<Message> = vec![];
    let mut updates: Vec<(Target, Option<f32>, Option<IsolateSpec>)> = vec![];
    {
        let ctx =
            Ctx { tcx, shown: &shown, functions: &functions, index: &index, local_def: &local_def };
        for (i, entry) in file.hint.iter().enumerate() {
            let n = i + 1;
            // entries that are malformed are errors, whether or not they match the code
            let clause_entry = entry.ensures.is_some() || entry.proof_note.is_some();
            if entry.ensures.is_some() && entry.proof_note.is_some() {
                return Err(ctx.bad(n, "give `ensures` or `proof_note`, not both".to_string()));
            }
            if clause_entry && entry.rlimit.is_some() {
                return Err(ctx.bad(
                    n,
                    "a hint for an `ensures` clause takes only `isolate` (an rlimit for the clause goes in `isolate = { rlimit = .. }`)".to_string(),
                ));
            }
            if clause_entry && entry.isolate.is_none() {
                return Err(
                    ctx.bad(n, "a hint for an `ensures` clause needs `isolate`".to_string())
                );
            }
            if !clause_entry && entry.rlimit.is_none() && entry.isolate.is_none() {
                return Err(ctx.bad(n, "the hint has neither `rlimit` nor `isolate`".to_string()));
            }
            if matches!(entry.ensures, Some(k) if k < 1) {
                return Err(ctx.bad(n, "`ensures` counts the clauses from 1".to_string()));
            }
            let rlimit_err = || {
                ctx.bad(
                    n,
                    "expected a number (at least 0) or \"infinity\" for `rlimit`".to_string(),
                )
            };
            let rlimit = match &entry.rlimit {
                None => None,
                Some(r) => Some(parse_rlimit(r).ok_or_else(rlimit_err)?),
            };
            let isolate = match &entry.isolate {
                None => None,
                Some(iso) => {
                    let rlimit = match &iso.rlimit {
                        None => None,
                        Some(r) => Some(parse_rlimit(r).ok_or_else(rlimit_err)?),
                    };
                    let backend = match iso.backend.as_deref() {
                        None => None,
                        Some("z3") => Some(IsolateBackend::Z3),
                        Some("cvc5") => Some(IsolateBackend::Cvc5),
                        Some(b) => {
                            return Err(ctx.bad(
                                n,
                                format!("unknown backend \"{b}\" (expected \"z3\" or \"cvc5\")"),
                            ));
                        }
                    };
                    if backend == Some(IsolateBackend::Cvc5) && !cvc5_encoding {
                        return Err(ctx.bad(
                            n,
                            "`backend = \"cvc5\"` needs the encoding for cvc5: run with `-V cvc5-smtlib` (Z3, with queries that cvc5 also reads) or `-V cvc5`".to_string(),
                        ));
                    }
                    Some(IsolateSpec { rlimit, backend })
                }
            };

            // an entry for another crate that shares the file (`root = "src/main.rs"`)
            if let Some(r) = &entry.root {
                let theirs = base.as_ref().map(|b| {
                    let p = b.join(r);
                    std::fs::canonicalize(&p).unwrap_or(p)
                });
                if theirs.is_none() || theirs != this_root {
                    continue;
                }
            }

            // the function: with several of that name, the one whose code the hash matches
            let funs = by_name.get(&entry.function).cloned().unwrap_or_default();
            let target = match funs.len() {
                0 => {
                    let last = entry.function.rsplit("::").next().unwrap_or(&entry.function);
                    let mut similar: Vec<String> = local_crate
                        .functions
                        .iter()
                        .map(|f| names_of(&f.x.name).swap_remove(0))
                        .filter(|name| name.rsplit("::").next() == Some(last))
                        .collect();
                    similar.sort();
                    similar.dedup();
                    let mut msg = vir::messages::warning_bare(format!(
                        "`{shown}`, hint {n}: there is no function `{}` in this crate; the hint was not applied",
                        entry.function
                    ));
                    if !similar.is_empty() {
                        msg = msg.help(format!("functions with that name: {}", similar.join(", ")));
                    }
                    if entry.root.is_none() {
                        msg = msg.help(
                            "if the hint is for another crate that shares the hints file, say which with `root = \"<its root file>\"`",
                        );
                    }
                    not_applied.push(msg);
                    continue;
                }
                1 => match ctx.resolve(n, entry, isolate.is_some(), &funs[0], &entry.function)? {
                    Resolved::NotApplied(msg) => {
                        not_applied.push(msg);
                        continue;
                    }
                    Resolved::Target(t) => t,
                },
                _ => {
                    // (a function that the hint cannot be for does not count)
                    let candidates: Vec<Target> = funs
                        .iter()
                        .filter_map(|f| {
                            let name = full_name(f).unwrap_or_else(|| entry.function.clone());
                            match ctx.resolve(n, entry, isolate.is_some(), f, &name) {
                                Ok(Resolved::Target(t)) => Some(t),
                                _ => None,
                            }
                        })
                        .collect();
                    let mut matching: Vec<Target> = candidates
                        .iter()
                        .filter(|t| entry.hash.as_deref() == Some(t.hash.as_str()))
                        .map(|t| Target {
                            fun: t.fun.clone(),
                            fi: t.fi,
                            clause: t.clause,
                            span: t.span.clone(),
                            hash: t.hash.clone(),
                            name: entry.function.clone(),
                        })
                        .collect();
                    if matching.len() == 1 {
                        matching.pop().unwrap()
                    } else {
                        let entries: Vec<String> = candidates
                            .iter()
                            .map(|t| entry_toml(entry, &t.name, &t.hash))
                            .collect();
                        let mut msg = vir::messages::warning_bare(format!(
                            "`{shown}`, hint {n}: `{}` names {} functions, and the hash does not pick one; the hint was not applied",
                            entry.function,
                            funs.len()
                        ));
                        if !entries.is_empty() {
                            msg = msg.help(format!(
                                "to pin the hint to one of them, replace it with one of:\n{}",
                                entries.join("\n\n")
                            ));
                        }
                        not_applied.push(msg);
                        continue;
                    }
                }
            };

            if !targets.insert((target.fun.clone(), target.clause)) {
                return Err(ctx.bad(
                    n,
                    match target.clause {
                        Some(j) => format!(
                            "another hint is for the same `ensures` clause of `{}` ({})",
                            target.name,
                            j + 1
                        ),
                        None => format!("another hint is for the same function, `{}`", target.name),
                    },
                ));
            }
            if entry.hash.as_deref() != Some(target.hash.as_str()) {
                let what = match target.clause {
                    Some(j) => format!("`ensures` clause {} of `{}`", j + 1, target.name),
                    None => format!("`{}`", target.name),
                };
                let why = match &entry.hash {
                    None => "it has no `hash` (which pins it to the code it is for)".to_string(),
                    Some(_) => format!("{what} has changed since it was written"),
                };
                not_applied.push(
                    vir::messages::warning(
                        &target.span,
                        format!("`{shown}`, hint {n}: the hint was not applied: {why}"),
                    )
                    .help(format!(
                        "if the hint is right for the current code, replace it with:\n{}",
                        entry_toml(entry, &entry.function, &target.hash)
                    )),
                );
                continue;
            }
            updates.push((target, rlimit, isolate));
        }
    }

    // apply them, in the form of the attributes that they stand for (which they replace)
    let applied = updates.len();
    for (target, rlimit, isolate) in updates {
        let function = &functions[target.fi];
        let mut fx = function.x.clone();
        match target.clause {
            Some(j) => {
                let ens = &fx.ensure.0[j];
                let new_ens = match &ens.x {
                    ExprX::UnaryOpr(UnaryOpr::ProofNote(label), inner) => {
                        let label = ProofNoteLabel { isolate, ..label.clone() };
                        ens.new_x(ExprX::UnaryOpr(UnaryOpr::ProofNote(label), inner.clone()))
                    }
                    _ => ens.new_x(ExprX::UnaryOpr(
                        UnaryOpr::ProofNote(ProofNoteLabel {
                            text: Arc::new(String::new()),
                            is_custom_err: false,
                            isolate,
                        }),
                        ens.clone(),
                    )),
                };
                let mut ens0 = (*fx.ensure.0).clone();
                ens0[j] = new_ens;
                fx.ensure = (Arc::new(ens0), fx.ensure.1.clone());
            }
            None => {
                let mut attrs = (*fx.attrs).clone();
                if rlimit.is_some() {
                    attrs.rlimit = rlimit;
                }
                if isolate.is_some() {
                    attrs.isolate_ensures = isolate;
                }
                fx.attrs = Arc::new(attrs);
            }
        }
        functions[target.fi] = function.new_x(fx);
    }

    let stale = not_applied.len();
    for msg in not_applied {
        let msg = if args.hints_locked {
            Arc::new(vir::messages::MessageX { level: MessageLevel::Error, ..(*msg).clone() })
        } else {
            msg
        };
        diagnostics.report(&msg.to_any());
    }
    if args.hints_locked && stale > 0 {
        return Err(vir::messages::error_bare(format!(
            "{stale} {} of `{shown}` did not apply to the code (`-V hints-locked`)",
            if stale == 1 { "hint" } else { "hints" }
        )));
    }
    if applied > 0 {
        diagnostics.report(
            &vir::messages::note_bare(format!(
                "{applied} {} from `{shown}` applied",
                if applied == 1 { "hint" } else { "hints" }
            ))
            .to_any(),
        );
    }
    Ok(Arc::new(KrateX { functions, ..(*krate).clone() }))
}
