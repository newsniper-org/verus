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

pub(crate) fn heap_post() -> VarIdent {
    crate::ast_util::air_unique_var(HEAP_POST)
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
    /// The exec functions with bodies whose calls may change the heap
    pub(crate) touching: HashSet<Fun>,
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
        call_may_touch_with(
            &self.funs,
            &self.aware,
            &self.touching,
            callee,
            typs,
            resolved,
            dynamic,
        )
    }
}

fn mentions_heap(expr: &Expr) -> bool {
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
            && (info.touching.contains(&f.x.name) || info.aware.contains(&f.x.name))
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
/// the others get `heap_preserving`). None if the crate has no heap (no vstd).
pub fn exported_touching(krate: &Krate) -> Option<HashSet<Fun>> {
    heap_info(krate).map(|i| i.touching)
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
    // A trait method impl takes the hidden parameters of its trait method (it inherits its
    // specification)
    for f in krate.functions.iter() {
        if let FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if aware.contains(method) {
                aware.insert(f.x.name.clone());
            }
        }
    }
    let touching = touching_funs(krate, &aware);
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
    Some(HeapInfo { typ, aware, state_in, tracked_in, touching, funs, stateful })
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
        // A closure body runs later, with the heap of then: it may read the current heap, but not
        // the heap when the enclosing function was called, and its own specification cannot
        // mention the heap yet
        let mut bad: Option<(crate::messages::Span, &str)> = None;
        let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(b, &mut |_s, e: &Expr| {
            if let ExprX::NonSpecClosure { body, requires, ensures, allocates, .. } = &e.x {
                if bad.is_none()
                    && (requires.iter().any(mentions_heap)
                        || ensures.iter().any(mentions_heap)
                        || allocates.as_ref().is_some_and(mentions_heap))
                {
                    bad = Some((
                        e.span.clone(),
                        "a closure's specification cannot mention the allocator heap yet",
                    ));
                }
                if bad.is_none() && mentions_old_heap(body) {
                    bad = Some((
                        body.span.clone(),
                        "a closure body cannot use `old_allocator_state` (or `old_allocator_heap`): it runs later",
                    ));
                }
            }
            Ok(())
        });
        if let Some((span, msg)) = bad {
            return Err(error(&span, msg));
        }
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
fn typs_may_touch(typs: &crate::ast::Typs) -> bool {
    let mut touch = false;
    for t in typs.iter() {
        let _ = crate::ast_visitor::typ_visitor_check::<(), _>(t, &mut |t: &Typ| {
            match &**t {
                TypX::TypParam(_)
                | TypX::Projection { .. }
                | TypX::AnonymousClosure(..)
                | TypX::FnDef(..)
                | TypX::Dyn(..)
                | TypX::Opaque { .. } => touch = true,
                TypX::Datatype(dt, _, _) if !trusted_dt(dt) => touch = true,
                _ => {}
            }
            Ok(())
        });
    }
    touch
}

/// The exec functions with bodies in `krate` whose calls may change the heap
pub(crate) fn touching_funs(krate: &Krate, aware: &HashSet<Fun>) -> HashSet<Fun> {
    let funs: HashMap<Fun, Function> =
        krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect();
    // calls of each exec body: (callee, type args, resolved callee)
    let mut calls: HashMap<Fun, Vec<(Fun, crate::ast::Typs, Option<Fun>, bool)>> = HashMap::new();
    let mut touching: HashSet<Fun> = HashSet::new();
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
        if direct {
            touching.insert(f.x.name.clone());
        }
        calls.insert(f.x.name.clone(), cs);
    }
    // fixed point
    loop {
        let mut changed = false;
        for (f, cs) in calls.iter() {
            if touching.contains(f) {
                continue;
            }
            let t = cs.iter().any(|(callee, typs, resolved, dynamic)| {
                call_may_touch_with(
                    &funs,
                    aware,
                    &touching,
                    callee,
                    typs,
                    resolved.as_ref(),
                    *dynamic,
                )
            });
            if t {
                touching.insert(f.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    touching
}

fn call_may_touch_with(
    funs: &HashMap<Fun, Function>,
    aware: &HashSet<Fun>,
    touching: &HashSet<Fun>,
    callee: &Fun,
    typs: &crate::ast::Typs,
    resolved: Option<&Fun>,
    dynamic: bool,
) -> bool {
    if aware.contains(callee) || resolved.is_some_and(|r| aware.contains(r)) {
        return true;
    }
    let target = resolved.unwrap_or(callee);
    let Some(func) = funs.get(target) else {
        // not in the crate (pruned): only trusted crates are known
        return !trusted_crate(target) || typs_may_touch(typs);
    };
    if func.x.mode != Mode::Exec {
        // a proof function that is not heap-aware leaves the heap as it was (checked)
        return false;
    }
    if dynamic && resolved.is_none() {
        return true;
    }
    if func.x.body.is_some() && !trusted_crate(target) {
        return touching.contains(target);
    }
    if func.x.attrs.is_external_body && func.x.body.is_none() || func.x.proxy.is_some() {
        // trusted, like its `allocates` bound: it reaches user code only through its type
        // arguments
        return typs_may_touch(typs);
    }
    if func.x.attrs.heap_preserving {
        // (computed by the crate that defined it)
        return false;
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
        return dyn_param || typs_may_touch(typs);
    }
    // a verified function of another crate: unknown
    true
}
