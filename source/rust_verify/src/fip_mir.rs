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

/// The drops of one `#[verifier::fip]` function, on paths that return normally
fn check_fip_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    marker: Option<DefId>,
    at: Option<&AllocTraits>,
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
/// through callbacks, are rejected by the verifier's fip checks), so they use bounded stack space.
/// (By name: under -V alloc-check, which fip needs, rust_to_vir accepts a dependency with one of
/// these names only if it is the real one.)
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

/// The calls of one strict fip function (on paths that return normally), checked to go to
/// strict fip functions or to std/vstd
fn strict_edges<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    at: Option<&AllocTraits>,
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
                if let (Some(at), Some((callee, args))) = (at, func.const_fn_def()) {
                    if !user_allocators(tcx, typing_env, at, args).is_empty()
                        && is_trusted_leaf_crate(tcx, callee)
                    {
                        uses_allocator = true;
                    }
                }
                // std code may drop values of its type arguments (`Vec::<H>::clear`, `truncate`),
                // which runs their destructors from inside the call
                if let Some((callee, args)) = func.const_fn_def() {
                    if is_trusted_leaf_crate(tcx, callee) {
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
) {
    let mut uses_allocator: std::collections::HashSet<LocalDefId> =
        std::collections::HashSet::new();
    let graph: std::collections::HashMap<LocalDefId, Vec<StrictEdge>> = strict
        .iter()
        .map(|f| {
            let (edges, uses) = strict_edges(tcx, *f, at);
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
pub(crate) fn check_fip_crate<'tcx>(tcx: TyCtxt<'tcx>, checked: &[(String, u128)]) -> bool {
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
        check_fip_body(tcx, def_id, marker, at.as_ref());
    }
    check_strict_stack(tcx, &strict, at.as_ref(), &allocator_methods);
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
