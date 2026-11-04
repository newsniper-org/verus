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
            TypX::AnonymousClosure(..) => Err(self.unsupported(
                span,
                typ,
                "the drop of a closure (and its captures) cannot be bounded yet",
            )),
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
        let mut typs: Vec<(Span, Typ)> = Vec::new();
        crate::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_scope, e| {
            typs.push((e.span.clone(), e.typ.clone()));
            Ok(())
        })?;
        for (span, typ) in typs {
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
