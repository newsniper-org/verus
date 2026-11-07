//! The ghost allocator heap (see `vstd::alloc_heap`).
//!
//! Each exec and proof function body has a variable `alloc%heap` (the current heap of the
//! thread) and `alloc%heap_pre` (the heap when the function was called). A function whose
//! specification mentions the heap (`allocator_state(a)`, `old_allocator_state(a)`, ...) is
//! *heap-aware*: its requires, ensures and allocates bound take two hidden parameters, the heap
//! before and after the call (`alloc%heap_pre`, `alloc%heap_post`), and a call passes the current
//! heap and a fresh one, which becomes the current heap after the call. In the function's own
//! body, the heap after the call is the current heap at the point where the ensures are checked.
//!
//! The specification functions of `vstd::alloc_heap` that name the heap of the context are
//! replaced here (before SST) by these variables:
//! - `allocator_heap()`: in requires, `alloc%heap_pre`; in ensures, `alloc%heap_post`; in a body,
//!   `alloc%heap`; not allowed in `allocates`;
//! - `old_allocator_heap()`: `alloc%heap_pre`;
//! - `allocator_state(a)`, `old_allocator_state(a)` and `allocator_tracked(a)` likewise, as
//!   `allocator_state_in(h, a)` and `allocator_tracked_in(h, a)`.

use crate::ast::{
    CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, FunctionKind, FunctionX, Krate, Mode,
    Param, ParamX, Typ, TypX, VarIdent, VirErr,
};
use crate::messages::error;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub const HEAP_CUR: &str = "alloc%heap";
pub const HEAP_PRE: &str = "alloc%heap_pre";
pub const HEAP_POST: &str = "alloc%heap_post";

pub(crate) fn heap_cur() -> VarIdent {
    crate::ast_util::air_unique_var(HEAP_CUR)
}

pub(crate) fn heap_pre() -> VarIdent {
    crate::ast_util::air_unique_var(HEAP_PRE)
}

/// The heap when a closure was called (in the closure's own scope)
pub(crate) fn closure_heap_pre() -> VarIdent {
    crate::ast_util::air_unique_var("alloc%closure_heap_pre")
}

pub(crate) fn heap_post() -> VarIdent {
    crate::ast_util::air_unique_var(HEAP_POST)
}

/// The type of the heap arguments of `closure_req`/`closure_ens` (the heap before a call of a
/// closure, and after it): the heap type, or `int` when there is no vstd
pub(crate) fn closure_heap_typ(info: &Option<std::sync::Arc<HeapInfo>>) -> Typ {
    match info {
        Some(i) => i.typ.clone(),
        None => std::sync::Arc::new(TypX::Int(crate::ast::IntRange::Int)),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Special {
    Heap,
    OldHeap,
    State,
    OldState,
    Tracked,
}

fn special(fun: &Fun) -> Option<Special> {
    if fun.path.krate != crate::ast::CrateId::Vstd {
        return None;
    }
    match crate::ast_util::fun_as_friendly_rust_name(fun).as_str() {
        "vstd::alloc_heap::allocator_heap" => Some(Special::Heap),
        "vstd::alloc_heap::old_allocator_heap" => Some(Special::OldHeap),
        "vstd::alloc_heap::allocator_state" => Some(Special::State),
        "vstd::alloc_heap::old_allocator_state" => Some(Special::OldState),
        "vstd::alloc_heap::allocator_tracked" => Some(Special::Tracked),
        _ => None,
    }
}

/// What the heap machinery needs from the crate (None if vstd's `alloc_heap` is not there)
pub struct HeapInfo {
    /// The type `vstd::alloc_heap::AllocHeap`
    pub(crate) typ: Typ,
    /// The heap-aware functions
    pub(crate) aware: HashSet<Fun>,
    state_in: Fun,
    tracked_in: Fun,
    /// The effects of the exec functions with bodies
    pub(crate) effects: HashMap<Fun, Effect>,
    /// All functions of the crate (to classify calls)
    funs: HashMap<Fun, Function>,
    /// Datatypes that implement `vstd::alloc_heap::StatefulAllocator`
    pub(crate) stateful: HashSet<crate::ast::Dt>,
}

/// The `Allocator` methods that move an allocator's state
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum StatefulMethod {
    /// `allocate`, `allocate_zeroed`
    Allocate,
    /// `grow`, `grow_zeroed`
    Grow,
    /// `shrink`
    Shrink,
}

/// vstd's `stateful_{allocate,grow,shrink}_{cost,heap}` and `stateful_tracked`
pub(crate) fn stateful_fun(m: StatefulMethod, kind: &str) -> Fun {
    use crate::ast::CrateId;
    match (m, kind) {
        (_, "tracked") => crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_tracked"),
        (StatefulMethod::Allocate, "cost") => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_allocate_cost")
        }
        (StatefulMethod::Allocate, _) => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_allocate_heap")
        }
        (StatefulMethod::Grow, "cost") => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_grow_cost")
        }
        (StatefulMethod::Grow, _) => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_grow_heap")
        }
        (StatefulMethod::Shrink, "cost") => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_shrink_cost")
        }
        (StatefulMethod::Shrink, _) => {
            crate::fun!(CrateId::Vstd => "alloc_heap"; "stateful_shrink_heap")
        }
    }
}

/// Which state-moving `Allocator` method is this (by its friendly name)?
pub(crate) fn stateful_method(fun: &Fun) -> Option<StatefulMethod> {
    match crate::ast_util::fun_as_friendly_rust_name(fun).as_str() {
        "core::alloc::Allocator::allocate" | "core::alloc::Allocator::allocate_zeroed" => {
            Some(StatefulMethod::Allocate)
        }
        "core::alloc::Allocator::grow" | "core::alloc::Allocator::grow_zeroed" => {
            Some(StatefulMethod::Grow)
        }
        "core::alloc::Allocator::shrink" => Some(StatefulMethod::Shrink),
        _ => None,
    }
}

impl HeapInfo {
    /// For a call of a heap-aware `fun` with type arguments `typs`: is the heap its `ensures`
    /// describe the whole effect? Always for a verified function; for a trusted specification
    /// (std's), only if the type arguments other than its allocators cannot reach user code that
    /// changes the heap
    pub(crate) fn trusted_aware_call_exact(&self, fun: &Function, typs: &crate::ast::Typs) -> bool {
        // (only std's functions, specified by `assume_specification`, can run user code that
        // their specification does not describe)
        if fun.x.proxy.is_none() {
            return true;
        }
        let mut allocator_params: HashSet<crate::ast::Ident> = HashSet::new();
        for b in fun.x.typ_bounds.iter() {
            if let crate::ast::GenericBoundX::Trait(crate::ast::TraitId::Path(p), args) = &**b {
                if crate::ast_util::path_as_friendly_rust_name(p) == "core::alloc::Allocator" {
                    if let Some(t) = args.first() {
                        if let TypX::TypParam(x) = &**t {
                            allocator_params.insert(x.clone());
                        }
                    }
                }
            }
        }
        let others: Vec<Typ> = fun
            .x
            .typ_params
            .iter()
            .zip(typs.iter())
            .filter(|(x, _)| !allocator_params.contains(*x))
            .map(|(_, t)| t.clone())
            .collect();
        !typs_effect(&std::sync::Arc::new(others)).may_touch()
    }

    /// The `Self` type of a call to an `Allocator` method, if it is an allocator with a state
    pub(crate) fn stateful_self(&self, typs: &crate::ast::Typs) -> Option<Typ> {
        let mut t = typs.first()?;
        // (`&A` forwards every method to `A`, std 1.100)
        while let TypX::Decorate(crate::ast::TypDecoration::Ref, _, inner) = &**t {
            t = inner;
        }
        match &**t {
            TypX::Datatype(dt, _, _) if self.stateful.contains(dt) => Some(t.clone()),
            _ => None,
        }
    }
}

impl HeapInfo {
    /// May an exec call (not of a heap-aware function) change the heap?
    pub(crate) fn call_may_touch(
        &self,
        callee: &Fun,
        typs: &crate::ast::Typs,
        resolved: Option<&Fun>,
        dynamic: bool,
    ) -> bool {
        call_effect_with(&self.funs, &self.aware, &self.effects, callee, typs, resolved, dynamic)
            .may_touch()
    }
}

pub(crate) fn mentions_heap(expr: &Expr) -> bool {
    let mut found = false;
    let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(expr, &mut |_scope, e: &Expr| {
        if let ExprX::Call { target: CallTarget::Fun(_, fun, ..), .. } = &e.x {
            if special(fun).is_some() {
                found = true;
            }
        }
        Ok(())
    });
    found
}

fn mentions_old_heap(expr: &Expr) -> bool {
    let mut found = false;
    let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(expr, &mut |_scope, e: &Expr| {
        if let ExprX::Call { target: CallTarget::Fun(_, fun, ..), .. } = &e.x {
            if matches!(special(fun), Some(Special::OldHeap | Special::OldState)) {
                found = true;
            }
        }
        Ok(())
    });
    found
}

fn spec_mentions_heap(f: &FunctionX) -> bool {
    f.require.iter().any(mentions_heap)
        || f.ensure.0.iter().any(mentions_heap)
        || f.ensure.1.iter().any(mentions_heap)
        || f.allocates.as_ref().is_some_and(mentions_heap)
        || f.deallocates.as_ref().is_some_and(mentions_heap)
        || matches!(&f.unwind_spec, Some(crate::ast::UnwindSpec::NoUnwindWhen(e)) if mentions_heap(e))
}

/// A `StatefulAllocator` may replace the default `grow_*`/`shrink_*` (std's default bodies: one
/// `allocate` of the new layout) only for methods its `Allocator` impl defines (std's default
/// bodies are not verified)
pub(crate) fn check_stateful_overrides(krate: &Krate) -> Result<(), VirErr> {
    let sa = crate::path!(crate::ast::CrateId::Vstd => "alloc_heap", "StatefulAllocator");
    for imp in krate.trait_impls.iter() {
        if imp.x.trait_path != sa {
            continue;
        }
        let Some(self_typ) = imp.x.trait_typ_args.first() else { continue };
        let alloc_impl = krate.trait_impls.iter().find(|i| {
            crate::ast_util::path_as_friendly_rust_name(&i.x.trait_path) == "core::alloc::Allocator"
                && i.x
                    .trait_typ_args
                    .first()
                    .is_some_and(|t| crate::ast_util::types_equal(t, self_typ))
        });
        let defines = |impl_path: &crate::ast::Path, name: &str| {
            krate.functions.iter().any(|f| match &f.x.kind {
                FunctionKind::TraitMethodImpl { method, impl_path: p, inherit_body_from: None, .. } => {
                    p == impl_path
                        && matches!(method.path.last_segment(), crate::ast::Segment::V(x, _) if x.as_str() == name)
                }
                _ => false,
            })
        };
        let has = |name: &str| alloc_impl.is_some_and(|ai| defines(&ai.x.impl_path, name));
        for (spec_fns, methods) in [
            (["grow_cost_at", "grow_next"], vec!["grow", "grow_zeroed"]),
            (["shrink_cost_at", "shrink_next"], vec!["shrink"]),
        ] {
            for f in spec_fns {
                if defines(&imp.x.impl_path, f) && !methods.iter().all(|m| has(m)) {
                    return Err(error(
                        &imp.span,
                        format!(
                            "this `StatefulAllocator` defines `{}`, but its `Allocator` impl does not define {} (std's default bodies, which Verus does not check, make one `allocate` with the new layout: the default `{}`)",
                            f,
                            methods
                                .iter()
                                .map(|m| format!("`{}`", m))
                                .collect::<Vec<_>>()
                                .join(" and "),
                            f
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// A trait method impl whose own specification mentions the heap needs its trait declaration to
/// (the hidden parameters come from the declaration)
pub(crate) fn check_impls_follow_decls(krate: &Krate) -> Result<(), VirErr> {
    let decl_aware: HashSet<Fun> = krate
        .functions
        .iter()
        .filter(|f| {
            matches!(f.x.kind, FunctionKind::TraitMethodDecl { .. }) && spec_mentions_heap(&f.x)
        })
        .map(|f| f.x.name.clone())
        .collect();
    for f in krate.functions.iter() {
        if let FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if spec_mentions_heap(&f.x)
                && !decl_aware.contains(method)
                && krate.functions.iter().any(|g| &g.x.name == method)
            {
                return Err(error(
                    &f.span,
                    "a trait method impl may mention the allocator heap in its specification only if its trait method declaration does",
                ));
            }
        }
    }
    Ok(())
}

/// `Drop::drop` and `Allocator::deallocate` run where Verus does not see them (a drop), so their
/// bodies must not change the heap (a lower bound in it would then be stale)
pub(crate) fn check_hidden_calls_preserve(info: &HeapInfo, krate: &Krate) -> Result<(), VirErr> {
    for f in krate.functions.iter() {
        let what = if f.x.attrs.is_drop {
            "Drop::drop"
        } else if let FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if crate::ast_util::fun_as_friendly_rust_name(method)
                == "core::alloc::Allocator::deallocate"
            {
                "Allocator::deallocate"
            } else {
                continue;
            }
        } else {
            continue;
        };
        if f.x.body.is_some()
            && (info.effects.get(&f.x.name).is_some_and(|e| e.may_touch())
                || info.aware.contains(&f.x.name))
        {
            return Err(error(
                &f.span,
                format!(
                    "this `{}` may change the allocator heap (allocate from, or step, an allocator with a state), but it runs where Verus does not see it (when a value is dropped); an allocator's `deallocate` may only raise its authoritative state (`AllocAuth::raise`)",
                    what
                ),
            ));
        }
    }
    Ok(())
}

/// The exec functions of `krate` (with bodies) whose calls may change the heap (for export:
/// the others get `heap_effect_params`). None if the crate has no heap (no vstd).
pub fn exported_effects(krate: &Krate) -> Option<HashMap<Fun, Vec<crate::ast::Ident>>> {
    heap_info(krate).map(|i| {
        i.effects
            .into_iter()
            .filter_map(|(f, e)| match e {
                Effect::Always => None,
                Effect::IfParams(ps) => Some((f, ps.into_iter().collect())),
            })
            .collect()
    })
}

pub(crate) fn heap_info(krate: &Krate) -> Option<HeapInfo> {
    let find = |name: &str| {
        krate.functions.iter().find(|f| {
            f.x.name.path.krate == crate::ast::CrateId::Vstd
                && crate::ast_util::fun_as_friendly_rust_name(&f.x.name) == name
        })
    };
    let typ = find("vstd::alloc_heap::allocator_heap")?.x.outer_ret.x.typ.clone();
    let state_in = crate::fun!(crate::ast::CrateId::Vstd => "alloc_heap"; "allocator_state_in");
    let tracked_in = crate::fun!(crate::ast::CrateId::Vstd => "alloc_heap"; "allocator_tracked_in");
    let mut aware: HashSet<Fun> = HashSet::new();
    for f in krate.functions.iter() {
        if matches!(f.x.mode, Mode::Exec | Mode::Proof) && spec_mentions_heap(&f.x) {
            aware.insert(f.x.name.clone());
        }
    }
    // A call of a closure value (`f(x)`, through vstd's exec_nonstatic_call) takes the heap: the
    // closure's specification may mention it
    aware.insert(crate::def::nonstatic_call_fun(false));
    // A trait method impl takes the hidden parameters of its trait method (it inherits its
    // specification)
    for f in krate.functions.iter() {
        if let FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if aware.contains(method) {
                aware.insert(f.x.name.clone());
            }
        }
    }
    let effects = function_effects(krate, &aware);
    let funs = krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    let sa = crate::path!(crate::ast::CrateId::Vstd => "alloc_heap", "StatefulAllocator");
    let mut stateful = HashSet::new();
    for imp in krate.trait_impls.iter() {
        if imp.x.trait_path == sa {
            if let Some(t) = imp.x.trait_typ_args.first() {
                if let TypX::Datatype(dt, _, _) = &**t {
                    stateful.insert(dt.clone());
                }
            }
        }
    }
    Some(HeapInfo { typ, aware, state_in, tracked_in, effects, funs, stateful })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// requires, unwind condition: the heap before the call
    Pre,
    /// ensures: the heap after the call
    Post,
    /// allocates, deallocates_when: `old_` forms only
    OldOnly,
    /// a body: the current heap
    Body,
    /// anywhere else (spec function bodies, decreases, masks): not allowed
    None,
}

fn rewrite(info: &HeapInfo, expr: &Expr, role: Role) -> Result<Expr, VirErr> {
    crate::ast_visitor::map_expr_visitor(expr, &|e: &Expr| {
        let ExprX::Call {
            target: CallTarget::Fun(kind, fun, typs, impl_paths, attrs), args, ..
        } = &e.x
        else {
            return Ok(e.clone());
        };
        let Some(sp) = special(fun) else {
            return Ok(e.clone());
        };
        let is_old = matches!(sp, Special::OldHeap | Special::OldState);
        let var = match (role, is_old) {
            (Role::None, _) => {
                return Err(error(
                    &e.span,
                    "the allocator heap (`allocator_state`, `old_allocator_state`, ...) can only be used in the requires, ensures, allocates bound and body of an exec or proof function",
                ));
            }
            (Role::OldOnly, false) => {
                return Err(error(
                    &e.span,
                    "an `allocates` bound is evaluated when the function is called: use `old_allocator_state(a)` (or `old_allocator_heap()`)",
                ));
            }
            (_, true) | (Role::Pre, false) => heap_pre(),
            (Role::Post, false) => heap_post(),
            (Role::Body, false) => heap_cur(),
        };
        let heap = crate::ast::SpannedTyped::new(&e.span, &info.typ, ExprX::Var(var));
        match sp {
            Special::Heap | Special::OldHeap => Ok(heap),
            Special::State | Special::OldState | Special::Tracked => {
                let name = if sp == Special::Tracked {
                    info.tracked_in.clone()
                } else {
                    info.state_in.clone()
                };
                let mut new_args = vec![heap];
                new_args.extend(args.iter().cloned());
                let target = CallTarget::Fun(
                    kind.clone(),
                    name,
                    typs.clone(),
                    impl_paths.clone(),
                    attrs.clone(),
                );
                Ok(e.new_x(ExprX::Call {
                    target,
                    args: Arc::new(new_args),
                    post_args: None,
                    body: None,
                }))
            }
        }
    })
}

/// Replace the heap specification functions in `expr` by the given heaps: plain forms by `post`,
/// `old_` forms by `pre` (a closure's specification: see ast_simplify)
pub(crate) fn rewrite_with(
    info: &HeapInfo,
    expr: &Expr,
    pre: &Expr,
    post: &Expr,
) -> Result<Expr, VirErr> {
    crate::ast_visitor::map_expr_visitor(expr, &|e: &Expr| {
        let ExprX::Call { target: CallTarget::Fun(kind, fun, typs, impl_paths, attrs), args, .. } =
            &e.x
        else {
            return Ok(e.clone());
        };
        let Some(sp) = special(fun) else {
            return Ok(e.clone());
        };
        let heap = if matches!(sp, Special::OldHeap | Special::OldState) { pre } else { post };
        let heap = crate::ast::SpannedTyped::new(&e.span, &info.typ, heap.x.clone());
        match sp {
            Special::Heap | Special::OldHeap => Ok(heap),
            Special::State | Special::OldState | Special::Tracked => {
                let name =
                    if sp == Special::Tracked { info.tracked_in.clone() } else { info.state_in.clone() };
                let mut new_args = vec![heap];
                new_args.extend(args.iter().cloned());
                Ok(e.new_x(ExprX::Call {
                    target: CallTarget::Fun(
                        kind.clone(),
                        name,
                        typs.clone(),
                        impl_paths.clone(),
                        attrs.clone(),
                    ),
                    args: Arc::new(new_args),
                    post_args: None,
                    body: None,
                }))
            }
        }
    })
}

fn rewrite_all(
    info: &HeapInfo,
    es: &crate::ast::Exprs,
    role: Role,
) -> Result<crate::ast::Exprs, VirErr> {
    let mut v = Vec::new();
    for e in es.iter() {
        v.push(rewrite(info, e, role)?);
    }
    Ok(Arc::new(v))
}

/// Replace the heap specification functions in `function` by the heap variables, and give a
/// heap-aware function its hidden parameters
pub(crate) fn prepare_function(info: &HeapInfo, function: &Function) -> Result<Function, VirErr> {
    let f = &function.x;
    let exec_or_proof = matches!(f.mode, Mode::Exec | Mode::Proof);
    let aware = info.aware.contains(&f.name);
    let needs = aware
        || (exec_or_proof && f.body.as_ref().is_some_and(mentions_heap))
        || (!exec_or_proof && f.body.as_ref().is_some_and(mentions_heap))
        || f.decrease.iter().any(mentions_heap);
    if !needs {
        return Ok(function.clone());
    }
    let (spec_role, post_role, alloc_role, body_role) = if exec_or_proof {
        (Role::Pre, Role::Post, Role::OldOnly, Role::Body)
    } else {
        (Role::None, Role::None, Role::None, Role::None)
    };
    let mut fx = f.clone();
    if f.name == crate::def::nonstatic_call_fun(false) {
        // `call_requires(f, args)` at the heap before the call, `call_ensures(f, args, r)` at the
        // heaps before and after it
        let pre = crate::ast::SpannedTyped::new(&function.span, &info.typ, ExprX::Var(heap_pre()));
        let post =
            crate::ast::SpannedTyped::new(&function.span, &info.typ, ExprX::Var(heap_post()));
        let heap_args = |e: &Expr| -> Result<Expr, VirErr> {
            crate::ast_visitor::map_expr_visitor(e, &|x: &Expr| match &x.x {
                ExprX::Call {
                    target: CallTarget::BuiltinSpecFun(bsf, typs, impl_paths),
                    args,
                    post_args,
                    body,
                } if matches!(
                    bsf,
                    crate::ast::BuiltinSpecFun::ClosureReq | crate::ast::BuiltinSpecFun::ClosureEns
                ) =>
                {
                    let (bsf2, extra) = match bsf {
                        crate::ast::BuiltinSpecFun::ClosureReq => {
                            (crate::ast::BuiltinSpecFun::ClosureReqHeap, vec![pre.clone()])
                        }
                        _ => (
                            crate::ast::BuiltinSpecFun::ClosureEnsHeap,
                            vec![pre.clone(), post.clone()],
                        ),
                    };
                    let mut a = (**args).clone();
                    a.extend(extra);
                    Ok(x.new_x(ExprX::Call {
                        target: CallTarget::BuiltinSpecFun(bsf2, typs.clone(), impl_paths.clone()),
                        args: Arc::new(a),
                        post_args: post_args.clone(),
                        body: body.clone(),
                    }))
                }
                _ => Ok(x.clone()),
            })
        };
        fx.require = Arc::new(f.require.iter().map(heap_args).collect::<Result<Vec<_>, _>>()?);
        fx.ensure = (
            Arc::new(f.ensure.0.iter().map(heap_args).collect::<Result<Vec<_>, _>>()?),
            f.ensure.1.clone(),
        );
        let mut params = (*f.params).clone();
        for name in [heap_pre(), heap_post()] {
            params.push(crate::def::Spanned::new(
                function.span.clone(),
                ParamX { name, typ: info.typ.clone(), mode: Mode::Spec, user_mut: false, unwrapped_info: None },
            ));
        }
        fx.params = Arc::new(params);
        return Ok(function.new_x(fx));
    }
    fx.require = rewrite_all(info, &f.require, spec_role)?;
    fx.ensure =
        (rewrite_all(info, &f.ensure.0, post_role)?, rewrite_all(info, &f.ensure.1, post_role)?);
    fx.decrease = rewrite_all(info, &f.decrease, Role::None)?;
    if let Some(e) = &f.allocates {
        fx.allocates = Some(rewrite(info, e, alloc_role)?);
    }
    if let Some(e) = &f.deallocates {
        fx.deallocates = Some(rewrite(info, e, alloc_role)?);
    }
    if let Some(crate::ast::UnwindSpec::NoUnwindWhen(e)) = &f.unwind_spec {
        fx.unwind_spec = Some(crate::ast::UnwindSpec::NoUnwindWhen(rewrite(info, e, spec_role)?));
    }
    if let Some(b) = &f.body {
        // A closure runs later, with the heap of then: in its body and its own specification,
        // plain forms mean the heap at that point in the closure (in its `ensures`: when it
        // returns), `old_` forms the heap when it was called (alloc%closure_heap_pre, declared with
        // the closure's own `alloc%heap` in ast_to_sst). Its `allocates` cannot mention the heap.
        let mut bad: Option<crate::messages::Span> = None;
        let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(b, &mut |_s, e: &Expr| {
            if let ExprX::NonSpecClosure { allocates, .. } = &e.x {
                if bad.is_none() && allocates.as_ref().is_some_and(mentions_heap) {
                    bad = Some(e.span.clone());
                }
            }
            Ok(())
        });
        if let Some(span) = bad {
            return Err(error(&span, "a closure's `allocates` cannot mention the allocator heap yet"));
        }
        let cur = crate::ast::SpannedTyped::new(&b.span, &info.typ, ExprX::Var(heap_cur()));
        let cpre =
            crate::ast::SpannedTyped::new(&b.span, &info.typ, ExprX::Var(closure_heap_pre()));
        let b = crate::ast_visitor::map_expr_visitor(b, &|e: &Expr| match &e.x {
            ExprX::NonSpecClosure {
                params,
                proof_fn_modes,
                body,
                requires,
                ensures,
                mask_spec,
                allocates,
                ret,
                external_spec,
            } => {
                let rw = |x: &Expr| rewrite_with(info, x, &cpre, &cur);
                let rws = |xs: &crate::ast::Exprs| -> Result<crate::ast::Exprs, VirErr> {
                    Ok(Arc::new(xs.iter().map(|x| rw(x)).collect::<Result<Vec<_>, _>>()?))
                };
                Ok(e.new_x(ExprX::NonSpecClosure {
                    params: params.clone(),
                    proof_fn_modes: proof_fn_modes.clone(),
                    body: rw(body)?,
                    requires: rws(requires)?,
                    ensures: rws(ensures)?,
                    mask_spec: mask_spec.clone(),
                    allocates: allocates.clone(),
                    ret: ret.clone(),
                    external_spec: external_spec.clone(),
                }))
            }
            _ => Ok(e.clone()),
        })?;
        let b = &b;
        fx.body = Some(rewrite(info, b, body_role)?);
    }
    if aware {
        let mk = |name: VarIdent| -> Param {
            crate::def::Spanned::new(
                function.span.clone(),
                ParamX {
                    name,
                    typ: info.typ.clone(),
                    mode: Mode::Spec,
                    user_mut: false,
                    unwrapped_info: None,
                },
            )
        };
        let mut params = (*f.params).clone();
        params.push(mk(heap_pre()));
        params.push(mk(heap_post()));
        fx.params = Arc::new(params);
    }
    Ok(function.new_x(fx))
}

/// Crates whose functions only reach an allocator's methods through their type arguments
/// (the standard library and vstd)
fn trusted_crate(fun: &Fun) -> bool {
    match &fun.path.krate {
        crate::ast::CrateId::Core | crate::ast::CrateId::Alloc | crate::ast::CrateId::Vstd => true,
        crate::ast::CrateId::Id(name, _) => &**name == "std",
        crate::ast::CrateId::Internal => true,
    }
}

fn trusted_dt(dt: &crate::ast::Dt) -> bool {
    match dt {
        crate::ast::Dt::Tuple(_) => true,
        crate::ast::Dt::Path(p) => match &p.krate {
            crate::ast::CrateId::Core | crate::ast::CrateId::Alloc | crate::ast::CrateId::Vstd => {
                true
            }
            crate::ast::CrateId::Id(name, _) => &**name == "std",
            crate::ast::CrateId::Internal => true,
        },
    }
}

/// May code of a trusted crate, instantiated with these type arguments, change the heap? It can
/// only reach user code (an allocator, a trait impl, a closure) through them.
/// Whether calling a function may change the heap: always, or only if one of these type
/// parameters (of the function the effect is about) is instantiated with a type through which
/// code may reach an allocator with a state (an empty set: never)
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum Effect {
    Always,
    IfParams(std::collections::BTreeSet<crate::ast::Ident>),
}

impl Effect {
    fn none() -> Self {
        Effect::IfParams(std::collections::BTreeSet::new())
    }

    fn join(self, other: Effect) -> Effect {
        match (self, other) {
            (Effect::Always, _) | (_, Effect::Always) => Effect::Always,
            (Effect::IfParams(mut a), Effect::IfParams(b)) => {
                a.extend(b);
                Effect::IfParams(a)
            }
        }
    }

    pub(crate) fn may_touch(&self) -> bool {
        !matches!(self, Effect::IfParams(p) if p.is_empty())
    }

    /// The effect of a callee with this effect (over its type parameters `callee_params`),
    /// instantiated with `typs`, over the caller's type parameters
    fn instantiate(&self, callee_params: &crate::ast::Idents, typs: &crate::ast::Typs) -> Effect {
        match self {
            Effect::Always => Effect::Always,
            Effect::IfParams(ps) => {
                let mut e = Effect::none();
                for p in ps.iter() {
                    match callee_params.iter().position(|q| q == p) {
                        Some(i) if i < typs.len() => {
                            e = e.join(typ_effect(&typs[i]));
                        }
                        _ => return Effect::Always,
                    }
                }
                e
            }
        }
    }
}

/// The effect of trusted code instantiated with `typ`: it reaches user code (which may change the
/// heap) only through the type
fn typ_effect(typ: &Typ) -> Effect {
    let mut e = Effect::none();
    let _ = crate::ast_visitor::typ_visitor_check::<(), _>(typ, &mut |t: &Typ| {
        match &**t {
            TypX::TypParam(x) => {
                e = std::mem::replace(&mut e, Effect::Always)
                    .join(Effect::IfParams([x.clone()].into_iter().collect()));
            }
            TypX::Projection { .. }
            | TypX::AnonymousClosure(..)
            | TypX::FnDef(..)
            | TypX::Dyn(..)
            | TypX::Opaque { .. } => e = Effect::Always,
            TypX::Datatype(dt, _, _) if !trusted_dt(dt) => e = Effect::Always,
            _ => {}
        }
        Ok(())
    });
    e
}

fn typs_effect(typs: &crate::ast::Typs) -> Effect {
    typs.iter().fold(Effect::none(), |e, t| e.join(typ_effect(t)))
}

/// The effects of the exec functions with bodies in `krate`
pub(crate) fn function_effects(krate: &Krate, aware: &HashSet<Fun>) -> HashMap<Fun, Effect> {
    let funs: HashMap<Fun, Function> =
        krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    // calls of each exec body: (callee, type args, resolved callee)
    let mut calls: HashMap<Fun, Vec<(Fun, crate::ast::Typs, Option<Fun>, bool)>> = HashMap::new();
    let mut effects: HashMap<Fun, Effect> = HashMap::new();
    for f in krate.functions.iter() {
        if f.x.mode != Mode::Exec {
            continue;
        }
        let Some(body) = &f.x.body else { continue };
        let mut cs = Vec::new();
        let mut direct = false;
        let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_s, e: &Expr| {
            match &e.x {
                ExprX::Call { target: CallTarget::Fun(kind, fun, typs, ..), .. } => {
                    let (resolved, dynamic) = match kind {
                        CallTargetKind::DynamicResolved { resolved, .. } => {
                            (Some(resolved.clone()), false)
                        }
                        CallTargetKind::Dynamic | CallTargetKind::ExternalTraitDefault => {
                            (None, true)
                        }
                        _ => (None, false),
                    };
                    cs.push((fun.clone(), typs.clone(), resolved, dynamic));
                }
                ExprX::Call {
                    target: CallTarget::FnSpec(..) | CallTarget::BuiltinSpecFun(..),
                    ..
                } => {}
                ExprX::Call { .. } => direct = true,
                _ => {}
            }
            Ok(())
        });
        effects.insert(f.x.name.clone(), if direct { Effect::Always } else { Effect::none() });
        calls.insert(f.x.name.clone(), cs);
    }
    // fixed point (effects only grow)
    loop {
        let mut changed = false;
        for (f, cs) in calls.iter() {
            let mut e = effects[f].clone();
            for (callee, typs, resolved, dynamic) in cs.iter() {
                let ce = call_effect_with(
                    &funs,
                    aware,
                    &effects,
                    callee,
                    typs,
                    resolved.as_ref(),
                    *dynamic,
                );
                e = e.join(ce);
            }
            if e != effects[f] {
                effects.insert(f.clone(), e);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    effects
}

/// The effect of a call, over the caller's type parameters
fn call_effect_with(
    funs: &HashMap<Fun, Function>,
    aware: &HashSet<Fun>,
    effects: &HashMap<Fun, Effect>,
    callee: &Fun,
    typs: &crate::ast::Typs,
    resolved: Option<&Fun>,
    dynamic: bool,
) -> Effect {
    let target = resolved.unwrap_or(callee);
    if aware.contains(callee) || resolved.is_some_and(|r| aware.contains(r)) {
        // (a trusted specification, like `Vec::push`'s, describes the change, which it can make
        // only through its type arguments; a verified heap-aware function may change anything)
        let trusted = funs.get(target).is_some_and(|f| {
            f.x.proxy.is_some() || (f.x.attrs.is_external_body && f.x.body.is_none())
        }) || trusted_crate(target);
        return if trusted { typs_effect(typs) } else { Effect::Always };
    }
    let Some(func) = funs.get(target) else {
        // not in the crate (pruned): only trusted crates are known
        return if trusted_crate(target) { typs_effect(typs) } else { Effect::Always };
    };
    if func.x.mode != Mode::Exec {
        // a proof function that is not heap-aware leaves the heap as it was (checked)
        return Effect::none();
    }
    if dynamic && resolved.is_none() {
        // (the impl is the one of the instantiation's type, which is among `typs`; an impl for a
        // trusted type is trusted, and reaches user code only through its type arguments)
        return typs_effect(typs);
    }
    let callee_typs = if resolved.is_some() { None } else { Some(&func.x.typ_params) };
    let instantiate = |e: &Effect| match callee_typs {
        Some(ps) => e.instantiate(ps, typs),
        // (a resolved impl's type parameters are not the call's type arguments)
        None => {
            if e.may_touch() {
                Effect::Always
            } else {
                Effect::none()
            }
        }
    };
    if func.x.body.is_some() && !trusted_crate(target) {
        return match effects.get(target) {
            Some(e) => instantiate(e),
            None => Effect::Always,
        };
    }
    if func.x.attrs.is_external_body && func.x.body.is_none() || func.x.proxy.is_some() {
        // trusted, like its `allocates` bound: it reaches user code only through its type
        // arguments
        return typs_effect(typs);
    }
    if let Some(ps) = &func.x.attrs.heap_effect_params {
        // (computed by the crate that defined it)
        return instantiate(&Effect::IfParams(ps.iter().cloned().collect()));
    }
    if trusted_crate(target) {
        // (a trusted function reaches user code through its type arguments, or through `dyn`
        // values among its parameters)
        let dyn_param = func.x.params.iter().any(|p| {
            let mut d = false;
            let _ = crate::ast_visitor::typ_visitor_check::<(), _>(&p.x.typ, &mut |t: &Typ| {
                if matches!(&**t, TypX::Dyn(..)) {
                    d = true;
                }
                Ok(())
            });
            d
        });
        return if dyn_param { Effect::Always } else { typs_effect(typs) };
    }
    // a verified function of another crate: unknown
    Effect::Always
}
