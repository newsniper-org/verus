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
    Constant, CrateId, Datatype, Dt, ExprX, Function, Ident, Primitive, Typ, TypDecoration, TypX,
    VirErr,
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

struct DropGlueCheck<'a> {
    ctx: &'a Ctx,
    /// Types already checked, keyed by their debug form (TypX is not Eq)
    visited: HashSet<String>,
}

impl<'a> DropGlueCheck<'a> {
    fn new(ctx: &'a Ctx) -> Self {
        DropGlueCheck { ctx, visited: HashSet::new() }
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
        match self.ctx.global.drop_impl_alloc_zero.get(dt) {
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
                let Some(datatype) = self.ctx.datatype_map.get(dt) else {
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
            TypX::TypParam(x) => Err(self.unsupported(
                span,
                typ,
                &format!("the drop of type parameter `{}` cannot be bounded yet", x),
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
    let mut checker = DropGlueCheck::new(ctx);
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
