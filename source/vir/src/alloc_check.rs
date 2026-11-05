//! `-V alloc-check`: rules that make the allocation counter sound with respect to things that do
//! not appear as calls in VIR.
//!
//! Implicit drops (end of scope, temporaries, reassignment, container drop glue, unwinding) leave
//! no trace in VIR, so their allocations cannot be counted where they happen. Instead, every
//! `Drop::drop` that a checked function may run must itself be bounded by `allocates 0`; then each
//! implicit drop contributes exactly 0 and the counter stays sound without knowing where drops
//! happen. What is needed is only the set of types the function may drop, which this module
//! over-approximates from the types of the function's parameters and of every expression in its
//! body (this includes temporaries, whose types are the return types of calls).

use crate::ast::{
    Constant, CrateId, Datatype, Dt, ExprX, Function, GenericBoundX, GenericBounds, Ident, Krate,
    Path, Primitive, TraitId, Typ, TypDecoration, TypX, VirErr,
};
use crate::context::Ctx;
use crate::messages::{Span, error};
use std::collections::{HashMap, HashSet};

/// Crates whose own `Drop` implementations are trusted not to allocate
/// (the std containers: dropping them only drops their contents).
fn is_trusted_std_crate(krate: &CrateId) -> bool {
    match krate {
        CrateId::Core | CrateId::Alloc => true,
        CrateId::Id(name, _) => name.as_str() == "std",
        CrateId::Internal | CrateId::Vstd => false,
    }
}

/// std datatypes that have their own `Drop` impl and whose drop is trusted to only drop their
/// contents (their type arguments) and free memory. Any other std type with a `Drop` impl (e.g.
/// `BufWriter`, whose drop flushes and may allocate) is rejected.
const TRUSTED_STD_DROPS: &[&str] = &[
    "alloc::vec::Vec",
    "alloc::vec::into_iter::IntoIter",
    "alloc::collections::vec_deque::VecDeque",
    "alloc::collections::vec_deque::into_iter::IntoIter",
    "alloc::collections::linked_list::LinkedList",
    "alloc::collections::binary_heap::BinaryHeap",
    "alloc::collections::btree::map::BTreeMap",
    "alloc::collections::btree::map::IntoIter",
    "alloc::collections::btree::set::BTreeSet",
    "alloc::rc::Weak",
    "alloc::sync::Weak",
    "core::cell::Ref",
    "core::cell::RefMut",
];

/// std datatypes without a `Drop` of their own whose drop glue only drops their type arguments
/// (and frees memory): their hidden fields are trusted even when a user crate (not vstd) declares
/// them with `external_type_specification`. Other std types are trusted only as vstd declares them.
const TRUSTED_STD_OPAQUE: &[&str] = &[
    "core::cell::Cell",
    "core::cell::RefCell",
    "core::cell::UnsafeCell",
    "core::cell::OnceCell",
    "core::mem::manually_drop::ManuallyDrop",
    "core::marker::PhantomData",
    "alloc::string::String",
    "std::sync::poison::mutex::Mutex",
    "std::sync::poison::rwlock::RwLock",
    "std::collections::hash::map::HashMap",
    "std::collections::hash::set::HashSet",
    "std::collections::hash::map::IntoIter",
    "std::collections::hash::set::IntoIter",
];

/// std datatypes whose last type parameter is an allocator. Only the global allocator is
/// supported: a user allocator's `deallocate` (run by the drop glue) and `clone` (run by the
/// container's `clone`) are unbounded user code.
const STD_ALLOCATOR_PARAM_TYPES: &[&str] = &[
    "alloc::vec::Vec",
    "alloc::vec::into_iter::IntoIter",
    "alloc::collections::vec_deque::VecDeque",
    "alloc::collections::vec_deque::into_iter::IntoIter",
    "alloc::collections::linked_list::LinkedList",
    "alloc::collections::binary_heap::BinaryHeap",
    "alloc::collections::btree::map::BTreeMap",
    "alloc::collections::btree::set::BTreeSet",
    "alloc::rc::Rc",
    "alloc::rc::Weak",
    "alloc::sync::Arc",
    "alloc::sync::Weak",
];

/// vstd opaque types whose drop glue may drop values not visible in their type arguments
/// (`JoinHandle` holds a joined thread's result, which may be an erased panic payload)
const UNTRUSTED_VSTD_OPAQUE: &[&str] = &["vstd::thread::JoinHandle"];

fn is_global_allocator(typ: &Typ) -> bool {
    match &**typ {
        TypX::Datatype(Dt::Path(path), _, _) => {
            crate::ast_util::path_as_friendly_rust_name(path) == "alloc::alloc::Global"
        }
        TypX::Decorate(_, _, t) => is_global_allocator(t),
        _ => false,
    }
}

pub(crate) fn is_literal_zero(e: &crate::ast::Expr) -> bool {
    match &e.x {
        ExprX::Const(Constant::Int(i)) => *i == num_bigint::BigInt::from(0),
        _ => false,
    }
}

/// `vstd::alloc_check::AllocFreeDrop`: types whose drop glue performs no allocation
fn is_alloc_free_drop_trait(path: &Path) -> bool {
    crate::ast_util::path_as_friendly_rust_name(path) == "vstd::alloc_check::AllocFreeDrop"
}

/// `Copy` types have no drop glue at all
fn is_copy_trait(path: &Path) -> bool {
    crate::ast_util::path_as_friendly_rust_name(path) == "core::marker::Copy"
}

/// Type parameters whose drop is known not to allocate, from `T: AllocFreeDrop` or `T: Copy`
fn alloc_free_typ_params(bounds: &GenericBounds) -> HashSet<Ident> {
    let mut params = HashSet::new();
    for bound in bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), args) = &**bound {
            if is_alloc_free_drop_trait(path) || is_copy_trait(path) {
                if let Some(self_typ) = args.first() {
                    if let TypX::TypParam(x) = &**self_typ {
                        params.insert(x.clone());
                    }
                }
            }
        }
        // a const generic parameter is a value, with no drop glue
        if let GenericBoundX::ConstTyp(t, _) = &**bound {
            if let TypX::TypParam(x) = &**t {
                params.insert(x.clone());
            }
        }
    }
    params
}

struct DropGlueCheck<'a> {
    datatypes: &'a HashMap<Dt, Datatype>,
    drop_table: &'a HashMap<Dt, (Span, bool)>,
    /// Datatypes with a `Copy` impl (they have no drop glue)
    copy_datatypes: &'a HashSet<Dt>,
    alloc_free_params: HashSet<Ident>,
    /// Types already checked, keyed by their debug form (TypX is not Eq)
    visited: HashSet<String>,
    /// Datatypes currently being expanded, with how many times each is on the stack: a
    /// non-regular type (`struct N<T>(Option<Box<N<(T, T)>>>)`) keeps re-entering the same
    /// datatype with ever new arguments, so its field types never repeat; it is rejected
    on_stack: HashMap<Dt, (Vec<Typ>, usize)>,
    /// Current nesting depth of the walk (bounded so that the verifier's stack cannot overflow)
    depth: usize,
}

/// Maximum nesting depth of the drop-glue walk
const MAX_DROP_GLUE_DEPTH: usize = 512;

/// How often one datatype may be re-entered (with different arguments) while expanding itself
const MAX_DROP_GLUE_REENTRY: usize = 8;
/// Maximum size (number of type nodes) of a type the drop rule examines
const MAX_DROP_GLUE_TYP_SIZE: usize = 4096;

impl<'a> DropGlueCheck<'a> {
    fn new(
        datatypes: &'a HashMap<Dt, Datatype>,
        drop_table: &'a HashMap<Dt, (Span, bool)>,
        copy_datatypes: &'a HashSet<Dt>,
        bounds: &GenericBounds,
    ) -> Self {
        DropGlueCheck {
            datatypes,
            drop_table,
            copy_datatypes,
            alloc_free_params: alloc_free_typ_params(bounds),
            visited: HashSet::new(),
            on_stack: HashMap::new(),
            depth: 0,
        }
    }

    /// Does `dt`'s definition reach `dt` again through its fields (only such a datatype can
    /// expand forever, e.g. non-regularly; `Option<Option<..>>` re-enters `Option` only through
    /// its arguments)?
    fn is_recursive_datatype(&self, dt: &Dt) -> bool {
        let mut seen: HashSet<Dt> = HashSet::new();
        let mut work: Vec<Dt> = vec![dt.clone()];
        while let Some(d) = work.pop() {
            let Some(datatype) = self.datatypes.get(&d) else { continue };
            for variant in datatype.x.variants.iter() {
                for field in variant.fields.iter() {
                    let found_self =
                        crate::ast_visitor::typ_visitor_check::<(), _>(&field.a.0, &mut |t| {
                            if let TypX::Datatype(d2 @ Dt::Path(_), _, _) = &**t {
                                if d2 == dt {
                                    return Err(());
                                }
                                if seen.insert(d2.clone()) {
                                    work.push(d2.clone());
                                }
                            }
                            Ok(())
                        })
                        .is_err();
                    if found_self {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// (the type itself is not printed: it may be huge)
    fn too_deep(span: &Span) -> VirErr {
        error(
            span,
            "cannot bound the allocations of dropping a value here: its drop glue is nested too deeply to check (is a type non-regular?)",
        )
    }

    fn unsupported(&self, span: &Span, typ: &Typ, why: &str) -> VirErr {
        error(
            span,
            format!(
                "cannot bound the allocations of dropping a value of type `{}`: {}",
                crate::ast_util::typ_to_diagnostic_str(typ),
                why
            ),
        )
    }

    fn check_datatype_drop(
        &self,
        span: &Span,
        typ: &Typ,
        dt: &Dt,
        datatype: &Datatype,
    ) -> Result<(), VirErr> {
        if !datatype.x.destructor {
            return Ok(());
        }
        match self.drop_table.get(dt) {
            Some((_, true)) => Ok(()),
            Some((drop_span, false)) => Err(error(
                span,
                format!(
                    "a value of type `{}` may be dropped here, but its `Drop::drop` is not bounded by `allocates 0`",
                    crate::ast_util::typ_to_diagnostic_str(typ)
                ),
            )
            .secondary_span(drop_span)),
            None => match dt {
                Dt::Path(path)
                    if is_trusted_std_crate(&path.krate)
                        && datatype.x.proxy.is_some()
                        && TRUSTED_STD_DROPS
                            .contains(&crate::ast_util::path_as_friendly_rust_name(path).as_str()) =>
                {
                    Ok(())
                }
                Dt::Path(path) if is_trusted_std_crate(&path.krate) => Err(self.unsupported(
                    span,
                    typ,
                    "its std `Drop` implementation is not known to be free of allocations",
                )),
                _ => Err(self.unsupported(span, typ, "its `Drop` implementation is not visible")),
            },
        }
    }

    fn check(&mut self, span: &Span, typ: &Typ) -> Result<(), VirErr> {
        let head = match &**typ {
            TypX::Datatype(dt @ Dt::Path(_), _, _) if self.is_recursive_datatype(dt) => {
                Some(dt.clone())
            }
            _ => None,
        };
        if self.depth >= MAX_DROP_GLUE_DEPTH {
            return Err(Self::too_deep(span));
        }
        // Re-entering a recursive datatype with a type that is part of the enclosing instance
        // (`List<List<u8>>` inside `List<List<List<u8>>>`) shrinks and is fine; re-entering it with
        // a type that is not (`N<(T, T)>` inside `N<T>`) is how a non-regular type grows
        let mut grew = false;
        if let Some(dt) = &head {
            let (stack, growth) = self.on_stack.entry(dt.clone()).or_insert((vec![], 0));
            if let Some(enclosing) = stack.last() {
                let is_part = crate::ast_visitor::typ_visitor_check::<(), _>(enclosing, &mut |t| {
                    if crate::ast_util::types_equal(t, typ) { Err(()) } else { Ok(()) }
                })
                .is_err();
                if !is_part {
                    if *growth >= MAX_DROP_GLUE_REENTRY {
                        return Err(Self::too_deep(span));
                    }
                    *growth += 1;
                    grew = true;
                }
            }
            stack.push(typ.clone());
        }
        self.depth += 1;
        let r = self.check_inner(span, typ);
        self.depth -= 1;
        if let Some(dt) = &head {
            let (stack, growth) = self.on_stack.get_mut(dt).unwrap();
            stack.pop();
            if grew {
                *growth -= 1;
            }
        }
        r
    }

    fn check_inner(&mut self, span: &Span, typ: &Typ) -> Result<(), VirErr> {
        // (a non-regular type can also grow exponentially, `N<(T, T)>`, so bound the size of
        // what is printed as a key as well as the depth)
        let mut size = 0usize;
        let too_big = crate::ast_visitor::typ_visitor_check::<(), _>(typ, &mut |_| {
            size += 1;
            if size > MAX_DROP_GLUE_TYP_SIZE { Err(()) } else { Ok(()) }
        })
        .is_err();
        if too_big {
            return Err(Self::too_deep(span));
        }
        if !self.visited.insert(format!("{:?}", typ)) {
            return Ok(());
        }
        match &**typ {
            TypX::Bool
            | TypX::Int(_)
            | TypX::Real
            | TypX::Float(_)
            | TypX::SpecFn(..)
            | TypX::FnDef(..)
            | TypX::TypeId
            | TypX::ConstInt(_)
            | TypX::ConstBool(_)
            | TypX::MutRef(_) => Ok(()),
            TypX::Decorate(
                TypDecoration::Ref | TypDecoration::ConstPtr | TypDecoration::Never,
                _,
                _,
            ) => Ok(()),
            // Ghost and tracked values do not exist at run time
            TypX::Decorate(TypDecoration::Ghost | TypDecoration::Tracked, _, _) => Ok(()),
            // Dropping these drops the contents (for Rc/Arc, when the last reference goes away)
            TypX::Decorate(TypDecoration::Box | TypDecoration::Rc | TypDecoration::Arc, arg, t) => {
                if let Some(arg) = arg {
                    if !is_global_allocator(&arg.allocator_typ) {
                        return Err(self.unsupported(
                            span,
                            typ,
                            "custom allocators (`allocator_api`) are not supported yet: only the global allocator is (a custom allocator's `deallocate` and `clone` would need bounds)",
                        ));
                    }
                }
                self.check(span, t)
            }
            TypX::Boxed(t) => self.check(span, t),
            TypX::Primitive(Primitive::Ptr | Primitive::Global | Primitive::StrSlice, _) => Ok(()),
            TypX::Primitive(Primitive::Array | Primitive::Slice, ts) => {
                for t in ts.iter() {
                    self.check(span, t)?;
                }
                Ok(())
            }
            TypX::Datatype(dt @ Dt::Tuple(_), args, _) => {
                let _ = dt;
                for t in args.iter() {
                    self.check(span, t)?;
                }
                Ok(())
            }
            // A closure type is also represented as an (opaque) internal datatype; its drop glue
            // drops its captures, which are collected like for `TypX::AnonymousClosure` below
            TypX::Datatype(Dt::Path(path), _, _) if crate::def::is_closure_type_path(path) => {
                Ok(())
            }
            TypX::Datatype(dt, args, _) => {
                let Some(datatype) = self.datatypes.get(dt) else {
                    return Err(self.unsupported(span, typ, "its definition is not visible"));
                };
                let datatype = datatype.clone();
                if let Dt::Path(path) = dt {
                    let name = crate::ast_util::path_as_friendly_rust_name(path);
                    // a type argument for a parameter bounded by `Allocator` (`HashMap<K, V, S, A>`)
                    let allocator_param_not_global =
                        datatype.x.typ_params.iter().zip(args.iter()).any(|((x, _), a)| {
                            datatype.x.typ_bounds.iter().any(|b| match &**b {
                                GenericBoundX::Trait(TraitId::Path(tp), targs) => {
                                    crate::ast_util::path_as_friendly_rust_name(tp)
                                        == "core::alloc::Allocator"
                                        && targs.first().is_some_and(
                                            |t| matches!(&**t, TypX::TypParam(y) if y == x),
                                        )
                                }
                                _ => false,
                            }) && !is_global_allocator(a)
                        });
                    if allocator_param_not_global
                        || STD_ALLOCATOR_PARAM_TYPES.contains(&name.as_str())
                            && !args.last().is_some_and(is_global_allocator)
                    {
                        return Err(self.unsupported(
                            span,
                            typ,
                            "custom allocators (`allocator_api`) are not supported yet: only the global allocator is (a custom allocator's `deallocate` and `clone` would need bounds)",
                        ));
                    }
                }
                self.check_datatype_drop(span, typ, dt, &datatype)?;
                let has_visible_fields = datatype.x.variants.iter().any(|v| !v.fields.is_empty());
                let dt_name = match dt {
                    Dt::Path(p) => crate::ast_util::path_as_friendly_rust_name(p),
                    Dt::Tuple(_) => String::new(),
                };
                // A std type's contents are trusted to be its type arguments only if vstd (the
                // audited trusted base) declares it; a user's own `external_type_specification`
                // of a std type (`LineWriter`, `io::Error`) may hide fields with allocating drops
                // (a std type is only known through an `external_type_specification`; one with no
                // proxy at all comes from a crate that merely calls itself std/core/alloc)
                let trusted_std = matches!(dt, Dt::Path(p) if is_trusted_std_crate(&p.krate))
                    && datatype.x.proxy.as_ref().is_some_and(|px| {
                        px.x.is_vstd_path()
                            || TRUSTED_STD_OPAQUE.contains(&dt_name.as_str())
                            || TRUSTED_STD_DROPS.contains(&dt_name.as_str())
                    });
                // A datatype whose fields are hidden: `external_body`, or one whose variants were
                // removed by pruning because its fields are not visible from here
                let opaque = datatype.x.variants.is_empty()
                    || matches!(datatype.x.transparency, crate::ast::DatatypeTransparency::Never);
                if has_visible_fields {
                    let substs: HashMap<Ident, Typ> = datatype
                        .x
                        .typ_params
                        .iter()
                        .map(|(x, _)| x.clone())
                        .zip(args.iter().cloned())
                        .collect();
                    for variant in datatype.x.variants.iter() {
                        for field in variant.fields.iter() {
                            let field_typ = crate::sst_util::subst_typ(&substs, &field.a.0);
                            self.check(span, &field_typ)?;
                        }
                    }
                } else if !trusted_std
                    && (datatype.x.destructor
                        || (opaque
                            && !(matches!(dt, Dt::Path(p) if p.is_vstd_path())
                                && datatype
                                    .x
                                    .proxy
                                    .as_ref()
                                    .map_or(true, |px| px.x.is_vstd_path())
                                && !UNTRUSTED_VSTD_OPAQUE.contains(&dt_name.as_str()))
                            && !self.copy_datatypes.contains(dt)))
                {
                    // An opaque (`external_body`) type hides its fields, so its drop glue may run
                    // a `Drop::drop` of a field type even if it has no `Drop` impl of its own.
                    // Only a `Copy` type is known to have no drop glue. (vstd's opaque types are
                    // part of the trusted base, like std's: their contents are their type
                    // arguments, checked below.)
                    return Err(self.unsupported(span, typ, "its fields are not visible"));
                }
                // An opaque container (e.g. Vec<T>) drops values of its type arguments
                for t in args.iter() {
                    self.check(span, t)?;
                }
                Ok(())
            }
            TypX::TypParam(x) if self.alloc_free_params.contains(x) => Ok(()),
            TypX::TypParam(x) => Err(self.unsupported(
                span,
                typ,
                &format!(
                    "add the bound `{}: vstd::alloc_check::AllocFreeDrop` (or `{}: Copy`)",
                    x, x
                ),
            )),
            TypX::Projection { .. } | TypX::PointeeMetadata(_) => {
                Err(self.unsupported(span, typ, "projected types are not supported yet"))
            }
            TypX::Dyn(..) => {
                Err(self.unsupported(span, typ, "the drop of a `dyn` value cannot be bounded yet"))
            }
            TypX::Opaque { .. } => Err(self.unsupported(
                span,
                typ,
                "the drop of an opaque `impl Trait` value cannot be bounded yet",
            )),
            // Dropping a closure drops its captures, which are variables of the function that
            // creates it: their types are the types of the variable uses inside the closure
            // body, which `collect_expr_typs` includes (and a closure's parameters and return
            // type are collected there too).
            TypX::AnonymousClosure(..) => Ok(()),
            _ => Err(self.unsupported(span, typ, "this kind of type is not supported yet")),
        }
    }
}

/// Drop rule: every `Drop::drop` that `function` may run must be bounded by `allocates 0`.
pub(crate) fn check_drop_glue(ctx: &Ctx, function: &Function) -> Result<(), VirErr> {
    let mut checker = DropGlueCheck::new(
        &ctx.global.alloc_datatypes,
        &ctx.global.drop_impl_alloc_zero,
        &ctx.global.copy_datatypes,
        &function.x.typ_bounds,
    );
    for param in function.x.params.iter() {
        checker.check(&param.span, &param.x.typ)?;
    }
    checker.check(&function.x.outer_ret.span, &function.x.outer_ret.x.typ)?;
    if let Some(body) = &function.x.body {
        for (span, typ) in collect_expr_typs(ctx, body)? {
            checker.check(&span, &typ)?;
        }
    }
    Ok(())
}

/// The types of every sub-expression of `expr`, and of the parameters and return value of every
/// closure inside it.
fn collect_expr_typs(ctx: &Ctx, expr: &crate::ast::Expr) -> Result<Vec<(Span, Typ)>, VirErr> {
    // (expressions, places such as a captured variable that is only borrowed, and closure
    // parameter/return types; a place has the type of the value it denotes)
    let typs: std::cell::RefCell<Vec<(Span, Typ)>> = std::cell::RefCell::new(Vec::new());
    crate::ast_visitor::ast_visitor_check_with_scope_map::<VirErr, _, _, _, _, _, _>(
        expr,
        &mut crate::ast_visitor::VisitorScopeMap::new(),
        &mut (),
        &mut |_, _, e| {
            typs.borrow_mut().push((e.span.clone(), e.typ.clone()));
            // A std function used as a value (`opt.map(Vec::clear)`, `let f = Vec::truncate`) may
            // be called later by code that only sees an `F`; like a direct call, it may drop
            // values behind its `&mut` parameters, so their referent types count as droppable.
            let mut t = &e.typ;
            while let TypX::Decorate(_, _, inner) = &**t {
                t = inner;
            }
            if let TypX::FnDef(fun, typ_args, _) = &**t {
                if let Some(g) = ctx.func_map.get(fun) {
                    if g.x.proxy.is_some() {
                        let substs: HashMap<Ident, Typ> =
                            g.x.typ_params.iter().cloned().zip(typ_args.iter().cloned()).collect();
                        for p in g.x.params.iter() {
                            let pt = crate::sst_util::subst_typ(&substs, &p.x.typ);
                            let mut pt_inner = &pt;
                            while let TypX::Decorate(_, _, inner) = &**pt_inner {
                                pt_inner = inner;
                            }
                            if let TypX::MutRef(inner) = &**pt_inner {
                                typs.borrow_mut().push((e.span.clone(), inner.clone()));
                            }
                        }
                    }
                }
            }
            // A std function (one given a specification, which says nothing about drops) that
            // receives `&mut C` may drop values inside `C` (`Vec::clear`, `truncate`,
            // `HashMap::clear`, ...), so the referent's type counts as droppable.
            if let ExprX::Call {
                target: crate::ast::CallTarget::Fun(kind, fun, ..), args, ..
            } = &e.x
            {
                let mut funs: Vec<&crate::ast::Fun> = vec![fun];
                if let crate::ast::CallTargetKind::DynamicResolved { resolved, .. } = kind {
                    funs.push(resolved);
                }
                let std_callee = funs
                    .iter()
                    .any(|f| ctx.func_map.get(*f).map_or(false, |g| g.x.proxy.is_some()));
                if std_callee {
                    for a in args.iter() {
                        let mut t = &a.typ;
                        while let TypX::Decorate(_, _, inner) = &**t {
                            t = inner;
                        }
                        if let TypX::MutRef(inner) = &**t {
                            typs.borrow_mut().push((a.span.clone(), inner.clone()));
                        }
                    }
                }
            }
            if let ExprX::NonSpecClosure { params, ret, .. } = &e.x {
                for p in params.iter() {
                    typs.borrow_mut().push((e.span.clone(), p.a.clone()));
                }
                typs.borrow_mut().push((e.span.clone(), ret.a.clone()));
            }
            Ok(())
        },
        &mut |_, _, _| Ok(()),
        &mut |_, _, _| Ok(()),
        &mut |_, _, _, _| Ok(()),
        &mut |_, _, p| {
            // only a whole local variable is owned (a field place may sit behind a reference)
            if matches!(&p.x, crate::ast::PlaceX::Local(_)) {
                typs.borrow_mut().push((p.span.clone(), p.typ.clone()));
            }
            Ok(())
        },
    )?;
    Ok(typs.into_inner())
}

/// A closure with an `allocates` bound is checked like a function with one: drops it may run
/// must be allocation-free (and, in strict mode, the bound is only a claim about normal returns,
/// which a closure cannot back with `no_unwind`, so strict mode rejects it).
pub(crate) fn check_closures_with_bounds(ctx: &Ctx, function: &Function) -> Result<(), VirErr> {
    let Some(body) = &function.x.body else { return Ok(()) };
    let mut closures: Vec<(Span, crate::ast::Expr)> = Vec::new();
    crate::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_scope, e| {
        if let ExprX::NonSpecClosure { allocates: Some(_), .. } = &e.x {
            closures.push((e.span.clone(), e.clone()));
        }
        Ok(())
    })?;
    for (span, closure) in closures {
        if ctx.global.alloc_check_strict {
            return Err(error(
                &span,
                "with -V alloc-check-strict, a closure cannot have an `allocates` bound (it cannot be `no_unwind`)",
            ));
        }
        let mut checker = DropGlueCheck::new(
            &ctx.global.alloc_datatypes,
            &ctx.global.drop_impl_alloc_zero,
            &ctx.global.copy_datatypes,
            &function.x.typ_bounds,
        );
        for (span, typ) in collect_expr_typs(ctx, &closure)? {
            checker.check(&span, &typ)?;
        }
    }
    Ok(())
}

/// Marker rule: `impl AllocFreeDrop for X` is accepted only if dropping an `X` cannot allocate,
/// i.e. X's drop glue passes the drop rule (with the impl's own bounds on its type parameters).
/// Impls from imported crates (including vstd's impls for std types) are checked too.
pub(crate) fn check_alloc_free_drop_impls(
    krate: &Krate,
    drop_table: &HashMap<Dt, (Span, bool)>,
    copy_datatypes: &HashSet<Dt>,
) -> Result<(), VirErr> {
    let datatypes: HashMap<Dt, Datatype> =
        krate.datatypes.iter().map(|d| (d.x.name.clone(), d.clone())).collect();
    for imp in krate.trait_impls.iter() {
        if !is_alloc_free_drop_trait(&imp.x.trait_path) {
            continue;
        }
        let Some(self_typ) = imp.x.trait_typ_args.first() else { continue };
        let mut checker =
            DropGlueCheck::new(&datatypes, drop_table, copy_datatypes, &imp.x.typ_bounds);
        checker.check(&imp.span, self_typ).map_err(|e| {
            e.help(
                "an `AllocFreeDrop` impl is only accepted when dropping the type cannot allocate",
            )
        })?;
    }
    Ok(())
}

/// A function whose `allocates` bound is justified by its body (or, for a trait method
/// declaration, by its impls) must come from a crate that was
/// verified with -V alloc-check; otherwise the bound was never checked and cannot be trusted.
/// (Bounds on `external_body` functions and `assume_specification`s have no body and are trusted
/// by definition.)
pub(crate) fn check_imported_bounds_were_checked(krate: &Krate) -> Result<(), VirErr> {
    let decl_has_bound: HashSet<&crate::ast::Fun> =
        krate.functions.iter().filter(|f| f.x.allocates.is_some()).map(|f| &f.x.name).collect();
    for f in krate.functions.iter() {
        // (an imported function has no body any more, so look at how it was declared)
        if f.x.attrs.is_external_body || f.x.proxy.is_some() || f.x.attrs.alloc_checked_crate {
            continue;
        }
        // An implementation of a method whose declaration has a bound must stay within it, which
        // only a crate verified with -V alloc-check has shown.
        let impl_of_bounded_decl = match &f.x.kind {
            crate::ast::FunctionKind::TraitMethodImpl { method, .. } => {
                decl_has_bound.contains(method)
            }
            _ => false,
        };
        if f.x.allocates.is_some() || impl_of_bounded_decl {
            return Err(error(
                &f.span,
                format!(
                    "`{}` has an `allocates` bound{}, but its crate was not verified with -V alloc-check, so the bound was not checked",
                    crate::ast_util::fun_as_friendly_rust_name(&f.x.name),
                    if f.x.allocates.is_some() { "" } else { " from its trait declaration" }
                ),
            ));
        }
    }
    Ok(())
}

/// An impl's own `allocates` bound becomes the axiom `call_allocates == own`, while its trait
/// method declaration's bound becomes `requires ==> call_allocates <= decl`. For a verified impl,
/// `own <= decl` is checked on entry (under the requires); an impl without a verified body
/// (`external_body`, `assume_specification`) is never checked, so its own bound could contradict
/// the declaration's and make `false` provable. Such an impl must not state its own bound: it then
/// has the declaration's bound, which is trusted like the rest of its specification. (A literal
/// `allocates 0` is allowed: both bounds are clamped at 0, so it cannot exceed the declaration's.)
pub(crate) fn check_unverified_impls_of_bounded_decls(krate: &Krate) -> Result<(), VirErr> {
    let decl_has_bound: HashSet<&crate::ast::Fun> =
        krate.functions.iter().filter(|f| f.x.allocates.is_some()).map(|f| &f.x.name).collect();
    for f in krate.functions.iter() {
        let crate::ast::FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind else { continue };
        let Some(own) = &f.x.allocates else { continue };
        if !decl_has_bound.contains(method) {
            continue;
        }
        // `call_allocates == 0` cannot contradict `call_allocates <= decl`: both bounds are
        // clamped at 0
        if is_literal_zero(own) {
            continue;
        }
        if f.x.attrs.is_external_body || f.x.proxy.is_some() {
            return Err(error(
                &f.span,
                format!(
                    "`{}` implements a trait method that has an `allocates` bound, so without a verified body it cannot state its own bound (remove it to use the trait method's bound)",
                    crate::ast_util::fun_as_friendly_rust_name(&f.x.name),
                ),
            ));
        }
    }
    Ok(())
}

/// Datatypes that implement `Copy` (and so have no drop glue)
pub(crate) fn copy_datatypes(krate: &Krate) -> HashSet<Dt> {
    let mut set = HashSet::new();
    for imp in krate.trait_impls.iter() {
        if !is_copy_trait(&imp.x.trait_path) {
            continue;
        }
        // Only an impl for every instantiation (`impl<A: Copy, ..> Copy for W<A, ..>`, as
        // `derive(Copy)` produces) shows that every `W<..>` is free of drop glue: an impl for
        // one instantiation says nothing about the others, and rustc only accepts a generic
        // impl if the fields are `Copy` whenever the bounds hold. (Values of the type arguments
        // are checked separately.)
        let Some(self_typ) = imp.x.trait_typ_args.first() else { continue };
        let TypX::Datatype(dt, args, _) = &**self_typ else { continue };
        let mut params: HashSet<Ident> = HashSet::new();
        let fully_generic = args.iter().all(|a| match &**a {
            TypX::TypParam(x) => params.insert(x.clone()),
            _ => false,
        });
        let only_copy_bounds = imp.x.typ_bounds.iter().all(|b| match &**b {
            GenericBoundX::Trait(TraitId::Path(path), targs) => {
                is_copy_trait(path)
                    && targs.first().is_some_and(|t| matches!(&**t, TypX::TypParam(_)))
            }
            GenericBoundX::Trait(TraitId::Sizedness(_), _) => true,
            _ => false,
        });
        if fully_generic && only_copy_bounds {
            set.insert(dt.clone());
        }
    }
    set
}

const FMT_TRAITS: [&str; 9] = [
    "core::fmt::Binary",
    "core::fmt::Debug",
    "core::fmt::Display",
    "core::fmt::LowerExp",
    "core::fmt::LowerHex",
    "core::fmt::Octal",
    "core::fmt::Pointer",
    "core::fmt::UpperExp",
    "core::fmt::UpperHex",
];

/// The cost of formatting an argument is taken from its `fmt` bound at an arbitrary `Formatter`
/// (vstd `fmt_witness_formatter`), which is only sound if no `fmt` bound depends on the
/// `Formatter`. Reject any that does.
pub(crate) fn check_fmt_impl_bounds(krate: &Krate) -> Result<(), VirErr> {
    for f in krate.functions.iter() {
        let Some(allocates) = &f.x.allocates else { continue };
        let trait_path = match &f.x.kind {
            crate::ast::FunctionKind::TraitMethodImpl { trait_path, .. }
            | crate::ast::FunctionKind::ForeignTraitMethodImpl { trait_path, .. } => trait_path,
            _ => continue,
        };
        let trait_name = crate::ast_util::path_as_friendly_rust_name(trait_path);
        if !FMT_TRAITS.contains(&trait_name.as_str()) || f.x.params.len() != 2 {
            continue;
        }
        let formatter = &f.x.params[1].x.name;
        // The formatter may be passed on to another `fmt` (a forwarding impl's bound is
        // `call_allocates(<U as Display>::fmt, (&self.0, f))`): that callee's bound does not depend
        // on its formatter either, by this same rule. Every other use is rejected.
        let allocates =
            &crate::ast_visitor::map_expr_visitor(allocates, &scrub_fmt_formatter_args)?;
        let mut uses_formatter =
            crate::ast_util::referenced_vars_expr(allocates).contains(formatter);
        crate::ast_visitor::expr_visitor_check(allocates, &mut |_, e: &crate::ast::Expr| {
            if matches!(&e.x, ExprX::VarAt(x, _) if x == formatter) {
                uses_formatter = true;
            }
            Ok::<(), VirErr>(())
        })?;
        if uses_formatter {
            return Err(error(
                &allocates.span,
                format!(
                    "the `allocates` bound of `{trait_name}::fmt` cannot depend on the `Formatter`"
                ),
            ));
        }
    }
    Ok(())
}

/// In `call_allocates(<_ as FmtTrait>::fmt, (a, b))`, replace the formatter argument `b`
fn scrub_fmt_formatter_args(e: &crate::ast::Expr) -> Result<crate::ast::Expr, VirErr> {
    use crate::ast::{BuiltinSpecFun, CallTarget};
    let ExprX::Call {
        target: CallTarget::BuiltinSpecFun(BuiltinSpecFun::ClosureAlloc, typs, impl_paths),
        args,
        post_args,
        body,
    } = &e.x
    else {
        return Ok(e.clone());
    };
    let is_fmt_method = match typs.first().map(|t| &**t) {
        Some(TypX::FnDef(fun, _, _)) => {
            let name = crate::ast_util::fun_as_friendly_rust_name(fun);
            FMT_TRAITS.iter().any(|tr| name == format!("{tr}::fmt"))
        }
        _ => false,
    };
    if !is_fmt_method || args.len() != 2 {
        return Ok(e.clone());
    }
    let ExprX::Ctor(dt @ Dt::Tuple(2), variant, binders, None) = &args[1].x else {
        return Ok(e.clone());
    };
    let mut binders = (**binders).clone();
    let Some(last) = binders.get_mut(1) else { return Ok(e.clone()) };
    let dummy = crate::ast_util::mk_bool(&last.a.span, true);
    *last = std::sync::Arc::new(air::ast::BinderX { name: last.name.clone(), a: dummy });
    let tuple =
        args[1].new_x(ExprX::Ctor(dt.clone(), variant.clone(), std::sync::Arc::new(binders), None));
    Ok(e.new_x(ExprX::Call {
        target: CallTarget::BuiltinSpecFun(
            BuiltinSpecFun::ClosureAlloc,
            typs.clone(),
            impl_paths.clone(),
        ),
        args: std::sync::Arc::new(vec![args[0].clone(), tuple]),
        post_args: post_args.clone(),
        body: body.clone(),
    }))
}

/// Decode the template bytes that rustc 1.99.1 passes to `core::fmt::Arguments::new` (see the
/// "Internal representation" comment on `Arguments` in `core/src/fmt/mod.rs`, and the
/// interpreter loop in `core::fmt::write`), returning how many times each of the `num_args`
/// arguments is formatted. An argument read only as a dynamic width or precision is not
/// formatted. Returns `None` for any byte sequence that is not a valid template; the caller then
/// assumes nothing, which is sound (the cost stays unknown).
///
/// The format is internal to rustc and may change with the toolchain; the tests below and the
/// end-to-end test in `rust_verify_test/tests/allocates.rs` fail if it does.
pub fn fmt_template_counts(bytes: &[u8], num_args: usize) -> Option<Vec<u64>> {
    let u16_at = |i: usize| -> Option<usize> {
        Some(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]) as usize)
    };
    let mut counts = vec![0u64; num_args];
    let mut i = 0;
    let mut next_arg = 0usize;
    loop {
        let n = *bytes.get(i)?;
        i += 1;
        if n == 0 {
            return if i == bytes.len() { Some(counts) } else { None };
        } else if n < 0x80 {
            i += n as usize;
        } else if n == 0x80 {
            i += 2 + u16_at(i)?;
        } else if n < 0xC0 {
            return None;
        } else {
            if n & 1 != 0 {
                i += 4; // flags
            }
            if n & 2 != 0 {
                i += 2; // width (or the index of a dynamic width argument)
            }
            if n & 4 != 0 {
                i += 2; // precision (or the index of a dynamic precision argument)
            }
            if n & 8 != 0 {
                next_arg = u16_at(i)?;
                i += 2;
            }
            *counts.get_mut(next_arg)? += 1;
            next_arg += 1;
        }
        if i > bytes.len() {
            return None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::fmt_template_counts;

    // Byte sequences produced by rustc 1.99.1 (`-Zunpretty=hir`)
    #[test]
    fn fmt_template_rustc_1_99_1() {
        // "{}"
        assert_eq!(fmt_template_counts(b"\xc0\x00", 1), Some(vec![1]));
        // "{0}{0}"
        assert_eq!(fmt_template_counts(b"\xc0\xc8\x00\x00\x00", 1), Some(vec![2]));
        // "a{}b{:>w$}{s}{:?}" with args (s, 3u8, 4u8, w, s): s, 3u8 (width = arg 2), s, 4u8
        // where the args array is [display(s), display(3u8), from_usize(w), display(s), debug(4u8)]
        assert_eq!(
            fmt_template_counts(b"\x01a\xc0\x01b\xd3 \x00\x00(\x02\x00\xc8\x03\x00\xc0\x00", 5),
            Some(vec![1, 1, 0, 1, 1])
        );
        // a literal piece of 200 bytes uses the 0x80 form
        let mut long = vec![0x80u8, 200, 0];
        long.extend(std::iter::repeat(b'x').take(200));
        long.extend([0xc0, 0x00]);
        assert_eq!(fmt_template_counts(&long, 1), Some(vec![1]));
        // malformed: no end, reserved first byte, argument out of range, trailing bytes
        assert_eq!(fmt_template_counts(b"\xc0", 1), None);
        assert_eq!(fmt_template_counts(b"\x90\x00", 1), None);
        assert_eq!(fmt_template_counts(b"\xc0\xc0\x00", 1), None);
        assert_eq!(fmt_template_counts(b"\xc0\x00\x00", 1), None);
    }
}

/// Does `expr` mention `call_allocates` (the `ClosureAlloc` builtin)?
pub(crate) fn mentions_call_allocates(expr: &crate::ast::Expr) -> bool {
    let mut found = false;
    let _ = crate::ast_visitor::expr_visitor_check::<VirErr, _>(expr, &mut |_scope, e| {
        if let ExprX::Call {
            target:
                crate::ast::CallTarget::BuiltinSpecFun(crate::ast::BuiltinSpecFun::ClosureAlloc, ..),
            ..
        } = &e.x
        {
            found = true;
        }
        Ok(())
    });
    found
}

/// `forall xs. body` => `forall xs. (g1 && ... && gn) ==> body` (unchanged if there are no guards)
pub(crate) fn guard_forall_body(
    expr: &crate::ast::Expr,
    guards: &Vec<crate::ast::Expr>,
) -> crate::ast::Expr {
    if guards.is_empty() {
        return expr.clone();
    }
    match &expr.x {
        ExprX::Quant(quant, binders, body) => {
            let guard = crate::ast_util::conjoin(&expr.span, guards);
            let body = crate::ast_util::mk_implies(&expr.span, &guard, body);
            expr.new_x(ExprX::Quant(*quant, binders.clone(), body))
        }
        _ => panic!("fndef_axiom should be forall"),
    }
}

/// `allocated()` is the current function's counter. In a closure's `requires`/`ensures`/
/// `allocates` it would be read against the enclosing function's counter (where the closure's
/// specification is assumed), not the closure's own, so it is rejected there.
pub(crate) fn check_allocated_not_in_closure_specs(function: &Function) -> Result<(), VirErr> {
    let Some(body) = &function.x.body else { return Ok(()) };
    let mut specs: Vec<crate::ast::Expr> = Vec::new();
    crate::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_scope, e| {
        if let ExprX::NonSpecClosure { requires, ensures, allocates, .. } = &e.x {
            specs.extend(requires.iter().cloned());
            specs.extend(ensures.iter().cloned());
            specs.extend(allocates.iter().cloned());
        }
        Ok(())
    })?;
    for spec in specs.iter() {
        crate::ast_visitor::expr_visitor_check::<VirErr, _>(spec, &mut |_scope, e| {
            if let ExprX::Call {
                target:
                    crate::ast::CallTarget::BuiltinSpecFun(crate::ast::BuiltinSpecFun::Allocated, ..),
                ..
            } = &e.x
            {
                return Err(error(
                    &e.span,
                    "`allocated()` cannot be used in a closure's `requires`, `ensures` or `allocates`",
                ));
            }
            Ok(())
        })?;
    }
    Ok(())
}

/// For each datatype with a (visible) `Drop` impl: the impl's span and whether its `drop` is
/// bounded by `allocates 0`
pub(crate) fn drop_impl_table(krate: &Krate) -> HashMap<Dt, (Span, bool)> {
    let mut table: HashMap<Dt, (Span, bool)> = HashMap::new();
    for f in krate.functions.iter() {
        if !f.x.attrs.is_drop {
            continue;
        }
        // `Drop` is a foreign trait, so its impl methods may have been demoted to static
        // functions; identify the datatype from the `&mut self` parameter instead.
        let self_dt = f.x.params.first().and_then(|p| {
            let mut t = &p.x.typ;
            loop {
                match &**t {
                    TypX::MutRef(inner) | TypX::Decorate(_, _, inner) => t = inner,
                    TypX::Datatype(dt, _, _) => return Some(dt.clone()),
                    _ => return None,
                }
            }
        });
        if let Some(dt) = self_dt {
            // `allocates 0` counts only if it was checked (or is trusted by design): a `drop` from
            // a crate verified without -V alloc-check may say `allocates 0` and still allocate
            let zero = f.x.allocates.as_ref().is_some_and(|e| is_literal_zero(e))
                && (f.x.attrs.alloc_checked_crate
                    || f.x.attrs.is_external_body
                    || f.x.proxy.is_some());
            table.insert(dt, (f.span.clone(), zero));
        }
    }
    table
}

/// -V alloc-check checks that need the whole merged crate, before it is pruned to what this
/// crate reaches: an impl from an imported crate can be reached through another crate's
/// generic function (`use_it::<T>` instantiated here) without appearing in the pruned crate.
/// - every impl of a trait method whose declaration has an `allocates` bound must come from a
///   crate verified with -V alloc-check (or be `external_body`/`assume_specification`, trusted);
/// - every `impl AllocFreeDrop` must pass the drop rule.
pub fn check_merged_krate(krate: &Krate) -> Result<(), VirErr> {
    let decl_has_bound: HashSet<&crate::ast::Fun> =
        krate.functions.iter().filter(|f| f.x.allocates.is_some()).map(|f| &f.x.name).collect();
    for f in krate.functions.iter() {
        if f.x.attrs.is_external_body || f.x.proxy.is_some() || f.x.attrs.alloc_checked_crate {
            continue;
        }
        if let crate::ast::FunctionKind::TraitMethodImpl { method, .. } = &f.x.kind {
            if decl_has_bound.contains(method) {
                return Err(error(
                    &f.span,
                    format!(
                        "`{}` implements a trait method with an `allocates` bound, but its crate was not verified with -V alloc-check, so the bound was not checked",
                        crate::ast_util::fun_as_friendly_rust_name(&f.x.name),
                    ),
                ));
            }
        }
    }
    let table = drop_impl_table(krate);
    let copies = copy_datatypes(krate);
    check_alloc_free_drop_impls(krate, &table, &copies)
}

/// For a std function (with a proxy `assume_specification`) that has `&mut` parameters: the type
/// parameters mentioned in their referent types, as `AllocFreeDrop` bound expressions. The
/// second result is false if such bounds are needed but `AllocFreeDrop` is not available.
pub(crate) fn proxy_mut_ref_drop_guards(
    ctx: &Ctx,
    function: &Function,
) -> (Vec<crate::ast::Expr>, bool) {
    // (a trait method declaration's axiom is only an upper bound that each impl is checked
    // against; the concern here is a concrete std function whose spec ignores the drops it does)
    if function.x.proxy.is_none()
        || matches!(function.x.kind, crate::ast::FunctionKind::TraitMethodDecl { .. })
    {
        return (vec![], true);
    }
    // (const generic parameters are values, not types with drop glue)
    let const_params: HashSet<Ident> = function
        .x
        .typ_bounds
        .iter()
        .filter_map(|b| match &**b {
            GenericBoundX::ConstTyp(t, _) => match &**t {
                TypX::TypParam(x) => Some(x.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let mut params: Vec<Ident> = Vec::new();
    for p in function.x.params.iter() {
        let mut t = &p.x.typ;
        while let TypX::Decorate(_, _, inner) = &**t {
            t = inner;
        }
        if let TypX::MutRef(inner) = &**t {
            let _ = crate::ast_visitor::typ_visitor_check::<(), _>(inner, &mut |ty| {
                if let TypX::TypParam(x) = &**ty {
                    if !params.contains(x) && !const_params.contains(x) {
                        params.push(x.clone());
                    }
                }
                Ok(())
            });
        }
    }
    if params.is_empty() {
        return (vec![], true);
    }
    let afd = crate::path!(CrateId::Vstd => "alloc_check", "AllocFreeDrop");
    if !ctx.trait_map.contains_key(&afd) {
        return (vec![], false);
    }
    let bool_typ = std::sync::Arc::new(TypX::Bool);
    let guards = params
        .into_iter()
        .map(|x| {
            let op = crate::ast::NullaryOpr::TraitBound(
                TraitId::Path(afd.clone()),
                std::sync::Arc::new(vec![std::sync::Arc::new(TypX::TypParam(x))]),
            );
            crate::ast::SpannedTyped::new(&function.span, &bool_typ, ExprX::NullaryOpr(op))
        })
        .collect();
    (guards, true)
}
