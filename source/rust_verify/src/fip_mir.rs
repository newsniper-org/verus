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
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};
use rustc_span::Span;
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_trait_selection::infer::InferCtxtExt;

const MARKER: &str = "vstd::alloc_check::NoDeallocDrop";

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

/// Marker rule: `unsafe impl NoDeallocDrop for X` is accepted only if dropping an `X` cannot
/// deallocate: `X` is not a `Box`, its own `Drop` (if any) is `#[verifier::fip]`, and dropping
/// each of its fields cannot deallocate (it has no drop glue or is `NoDeallocDrop`, with the
/// impl's own bounds). Every impl in the program is checked, whichever crate it is in.
fn check_marker_impls<'tcx>(tcx: TyCtxt<'tcx>, marker: DefId) {
    for impl_def_id in tcx.all_impls(marker) {
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

/// The drops of one `#[verifier::fip]` function, on paths that return normally
fn check_fip_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId, marker: Option<DefId>) {
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
            TerminatorKind::Call { func, .. } => {
                let Some((callee, args)) = func.const_fn_def() else { continue };
                // (drop elaboration calls `Drop::drop` directly, e.g. for a `Box` whose contents
                // were moved out, which frees the box)
                let is_drop_method =
                    drop_trait.is_some() && tcx.trait_of_assoc(callee) == drop_trait;
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
/// leaves: std's and vstd's functions do not recurse into the caller's code (the calls that could,
/// through callbacks, are rejected by the verifier's fip checks), so they use bounded stack space
fn is_trusted_leaf_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let name = tcx.crate_name(def_id.krate);
    matches!(name.as_str(), "core" | "alloc" | "std" | "vstd" | "verus_builtin")
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

/// The local destructors that dropping a value of type `ty` runs
fn drop_glue_destructors<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    out: &mut Vec<DefId>,
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
            for variant in adt.variants().iter() {
                for field in variant.fields.iter() {
                    let fty = field.ty(tcx, args).skip_normalization();
                    drop_glue_destructors(tcx, typing_env, fty, out, seen);
                }
            }
        }
        ty::Tuple(tys) => {
            for t in tys.iter() {
                drop_glue_destructors(tcx, typing_env, t, out, seen);
            }
        }
        ty::Array(t, _) | ty::Slice(t) => drop_glue_destructors(tcx, typing_env, *t, out, seen),
        _ => {}
    }
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

/// The calls of one strict fip function (on paths that return normally), checked to go to
/// strict fip functions or to std/vstd
fn strict_edges<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Vec<StrictEdge> {
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
        None => strict_err(
            tcx,
            span,
            format!(
                "it calls `{}` from another crate, whose stack use is not known here",
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
                match resolve_callee(tcx, typing_env, func) {
                    Some(callee) => add(callee, tail, span, &mut edges),
                    None => strict_err(
                        tcx,
                        span,
                        "it makes a call whose callee is not known here (a generic call, or a call of a function value)".to_string(),
                    ),
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(&body.local_decls, tcx).ty;
                let mut dtors = Vec::new();
                drop_glue_destructors(
                    tcx,
                    typing_env,
                    ty,
                    &mut dtors,
                    &mut std::collections::HashSet::new(),
                );
                for d in dtors {
                    add(d, false, span, &mut edges);
                }
            }
            _ => {}
        }
    }
    edges
}

/// Constant stack space: a call that is not a tail call adds a frame, so no cycle of calls may
/// go through one (a cycle of tail calls only replaces frames). The calls that leave the strict
/// functions go to std/vstd, which do not call back.
fn check_strict_stack<'tcx>(tcx: TyCtxt<'tcx>, strict: &[LocalDefId]) {
    let graph: std::collections::HashMap<LocalDefId, Vec<StrictEdge>> =
        strict.iter().map(|f| (*f, strict_edges(tcx, *f))).collect();
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

/// Checks every `#[verifier::fip]` function of the crate and every `NoDeallocDrop` impl; returns
/// whether there are fip functions
pub(crate) fn check_fip_crate<'tcx>(tcx: TyCtxt<'tcx>) -> bool {
    let marker = tcx.all_traits_including_private().find(|d| tcx.def_path_str(*d) == MARKER);
    if let Some(m) = marker {
        check_marker_impls(tcx, m);
    }
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
        check_fip_body(tcx, def_id, marker);
    }
    check_strict_stack(tcx, &strict);
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
