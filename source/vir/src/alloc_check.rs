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
    }
    params
}

struct DropGlueCheck<'a> {
    datatypes: &'a HashMap<Dt, Datatype>,
    drop_table: &'a HashMap<Dt, (Span, bool)>,
    alloc_free_params: HashSet<Ident>,
    /// Types already checked, keyed by their debug form (TypX is not Eq)
    visited: HashSet<String>,
}

impl<'a> DropGlueCheck<'a> {
    fn new(
        datatypes: &'a HashMap<Dt, Datatype>,
        drop_table: &'a HashMap<Dt, (Span, bool)>,
        bounds: &GenericBounds,
    ) -> Self {
        DropGlueCheck {
            datatypes,
            drop_table,
            alloc_free_params: alloc_free_typ_params(bounds),
            visited: HashSet::new(),
        }
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
                Dt::Path(path) if is_trusted_std_crate(&path.krate) => Ok(()),
                _ => Err(self.unsupported(span, typ, "its `Drop` implementation is not visible")),
            },
        }
    }

    fn check(&mut self, span: &Span, typ: &Typ) -> Result<(), VirErr> {
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
            TypX::Decorate(TypDecoration::Box | TypDecoration::Rc | TypDecoration::Arc, _, t) => {
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
            TypX::Datatype(dt, args, _) => {
                let Some(datatype) = self.datatypes.get(dt) else {
                    return Err(self.unsupported(span, typ, "its definition is not visible"));
                };
                let datatype = datatype.clone();
                self.check_datatype_drop(span, typ, dt, &datatype)?;
                let has_visible_fields = datatype.x.variants.iter().any(|v| !v.fields.is_empty());
                let trusted_std = matches!(dt, Dt::Path(p) if is_trusted_std_crate(&p.krate));
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
                } else if !trusted_std && datatype.x.destructor {
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
        &ctx.datatype_map,
        &ctx.global.drop_impl_alloc_zero,
        &function.x.typ_bounds,
    );
    for param in function.x.params.iter() {
        checker.check(&param.span, &param.x.typ)?;
    }
    checker.check(&function.x.outer_ret.span, &function.x.outer_ret.x.typ)?;
    if let Some(body) = &function.x.body {
        for (span, typ) in collect_expr_typs(body)? {
            checker.check(&span, &typ)?;
        }
    }
    Ok(())
}

/// The types of every sub-expression of `expr`, and of the parameters and return value of every
/// closure inside it.
fn collect_expr_typs(expr: &crate::ast::Expr) -> Result<Vec<(Span, Typ)>, VirErr> {
    // (expressions, places such as a captured variable that is only borrowed, and closure
    // parameter/return types; a place has the type of the value it denotes)
    let typs: std::cell::RefCell<Vec<(Span, Typ)>> = std::cell::RefCell::new(Vec::new());
    crate::ast_visitor::ast_visitor_check_with_scope_map::<VirErr, _, _, _, _, _, _>(
        expr,
        &mut crate::ast_visitor::VisitorScopeMap::new(),
        &mut (),
        &mut |_, _, e| {
            typs.borrow_mut().push((e.span.clone(), e.typ.clone()));
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
            &ctx.datatype_map,
            &ctx.global.drop_impl_alloc_zero,
            &function.x.typ_bounds,
        );
        for (span, typ) in collect_expr_typs(&closure)? {
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
) -> Result<(), VirErr> {
    let datatypes: HashMap<Dt, Datatype> =
        krate.datatypes.iter().map(|d| (d.x.name.clone(), d.clone())).collect();
    for imp in krate.trait_impls.iter() {
        if !is_alloc_free_drop_trait(&imp.x.trait_path) {
            continue;
        }
        let Some(self_typ) = imp.x.trait_typ_args.first() else { continue };
        let mut checker = DropGlueCheck::new(&datatypes, drop_table, &imp.x.typ_bounds);
        checker.check(&imp.span, self_typ).map_err(|e| {
            e.help(
                "an `AllocFreeDrop` impl is only accepted when dropping the type cannot allocate",
            )
        })?;
    }
    Ok(())
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
