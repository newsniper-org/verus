use crate::context::BodyCtxt;
use crate::verus_items::RustItem;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, Expr, ExprX, FunctionX, Mode, Place, PlaceX, SpannedTyped, VirErr, VirErrAs,
};
use vir::messages::WarningAllow;

/// Traits with special handling
#[derive(Clone, Copy, Debug)]
pub enum SpecialTrait {
    Clone,
    //PartialEq,
}

/// What to do for a given automatically-derived trait impl
#[derive(Debug, Clone, Copy)]
pub enum AutomaticDeriveAction {
    Special(SpecialTrait),
    VerifyAsIs,
    /// Ignore, optionally providing a warning
    Ignore,
}

pub fn get_action(rust_item: Option<RustItem>) -> AutomaticDeriveAction {
    match rust_item {
        Some(RustItem::PartialEq | RustItem::Eq) => AutomaticDeriveAction::Ignore,
        Some(RustItem::Clone) => AutomaticDeriveAction::Special(SpecialTrait::Clone),

        Some(RustItem::Copy) => AutomaticDeriveAction::VerifyAsIs,

        Some(RustItem::Hash)
        | Some(RustItem::Default)
        | Some(RustItem::Debug)
        | Some(RustItem::Ord)
        | Some(RustItem::PartialOrd) => AutomaticDeriveAction::Ignore,

        Some(_) | None => AutomaticDeriveAction::VerifyAsIs,
    }
}

pub fn is_automatically_derived(attrs: &[rustc_hir::Attribute]) -> bool {
    for attr in attrs.iter() {
        match attr {
            rustc_hir::Attribute::Unparsed(item) => match &item.path.segments[..] {
                [segment] => {
                    if segment.as_str() == "automatically_derived" {
                        return true;
                    }
                }
                _ => {}
            },
            rustc_hir::Attribute::Parsed(rustc_hir::attrs::AttributeKind::AutomaticallyDerived) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// -V alloc-check: how far a derived `clone` is in place
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum DerivedCloneLevel {
    /// `allocates 0`
    Fbip,
    /// `allocates 0`, `#[verifier::fip]`
    Fip,
    /// `allocates 0`, `#[verifier::fip(strict)]`
    Strict,
}

/// -V alloc-check: if `def_id` is the `clone` of a derived `Clone` impl, how far it is in place.
/// * Its body is `*self` (`#[derive(Clone)]` writes that when the same `#[derive(..)]` has `Copy`
///   and the type has no type parameters, and for unions; it then also implements `TrivialClone`,
///   so std copies slices of the type bitwise): strict.
/// * A struct, whose body clones field by field: the lowest level over the fields' types of the
///   `Clone` markers (`FipStrictClone`, `FipClone`, `FbipClone`) that hold where the impl is
///   (none if a field's type has none), and at most `Fip` if a field's type has a type parameter.
///
/// VIR gives the function `allocates 0` and the attributes of its level, and the MIR check
/// (`fip_mir`) checks it as a function with those attributes: both still check its body, so this
/// is not trusted (a wrong level here makes a check fail, not pass).
pub(crate) fn derived_clone_level(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_span::def_id::LocalDefId,
) -> Option<DerivedCloneLevel> {
    use rustc_hir::{ExprKind, QPath, UnOp, def::Res};
    if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::AssocFn)
        || tcx.item_name(def_id.to_def_id()).as_str() != "clone"
    {
        return None;
    }
    let imp = tcx.impl_of_assoc(def_id.to_def_id()).and_then(|d| d.as_local())?;
    let trait_ref = tcx.impl_opt_trait_ref(imp)?;
    if Some(trait_ref.skip_binder().def_id) != tcx.lang_items().clone_trait() {
        return None;
    }
    if !is_automatically_derived(tcx.hir_attrs(tcx.local_def_id_to_hir_id(imp))) {
        return None;
    }
    let body = tcx.hir_body_owned_by(def_id);
    let copy_form = (|| {
        let [param] = body.params else { return false };
        let ExprKind::Block(block, None) = &body.value.kind else { return false };
        let Some(tail) = block.expr else { return false };
        let ExprKind::Unary(UnOp::Deref, inner) = &tail.kind else { return false };
        let ExprKind::Path(QPath::Resolved(None, path)) = &inner.kind else { return false };
        matches!(path.res, Res::Local(id) if id == param.pat.hir_id)
    })();
    if copy_form {
        return Some(DerivedCloneLevel::Strict);
    }
    let rustc_middle::ty::TyKind::Adt(adt, args) =
        tcx.type_of(imp).instantiate_identity().skip_normalization().kind()
    else {
        return None;
    };
    if !adt.is_struct() {
        return None;
    }
    let find = |name: &str| {
        let path = format!("vstd::alloc_check::{}", name);
        tcx.all_traits_including_private().find(|d| {
            format!("{}{}", tcx.crate_name(d.krate), tcx.def_path(*d).to_string_no_crate_verbose())
                == path
        })
    };
    let markers = [
        (DerivedCloneLevel::Strict, find("FipStrictClone")?),
        (DerivedCloneLevel::Fip, find("FipClone")?),
        (DerivedCloneLevel::Fbip, find("FbipClone")?),
    ];
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id.to_def_id());
    let (infcx, param_env) = {
        use rustc_infer::infer::TyCtxtInferExt;
        tcx.infer_ctxt().build_with_typing_env(typing_env)
    };
    let mut level = DerivedCloneLevel::Strict;
    for field in adt.non_enum_variant().fields.iter() {
        let ty = tcx.erase_and_anonymize_regions(field.ty(tcx, args).skip_normalization());
        // (the clone of a field whose type has a type parameter is a call through a marker,
        // which the strict stack check takes to reach any strict `clone` of the crate, this one
        // included: not strict)
        {
            use rustc_middle::ty::TypeVisitableExt;
            if ty.has_param() {
                level = level.min(DerivedCloneLevel::Fip);
            }
        }
        let field_level = markers.iter().find_map(|(l, m)| {
            use rustc_trait_selection::infer::InferCtxtExt;
            infcx
                .type_implements_trait(*m, [ty], param_env)
                .must_apply_modulo_regions()
                .then_some(*l)
        })?;
        level = level.min(field_level);
    }
    Some(level)
}

/// -V alloc-check: give a derived `clone` `allocates 0` and the attributes of its level (see
/// `derived_clone_level`)
fn add_derived_clone_level<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    fn_id: rustc_span::def_id::DefId,
    span: Span,
    functionx: &mut FunctionX,
) {
    if !bctx.ctxt.cmd_line_args.alloc_check || functionx.allocates.is_some() {
        return;
    }
    let Some(level) = fn_id.as_local().and_then(|l| derived_clone_level(bctx.ctxt.tcx, l)) else {
        return;
    };
    functionx.allocates =
        Some(vir::ast_util::mk_int_lit_from_usize(&bctx.ctxt.spans.to_air_span(span), 0));
    let mut attrs = (*functionx.attrs).clone();
    attrs.fip = level >= DerivedCloneLevel::Fip;
    attrs.fip_strict = level >= DerivedCloneLevel::Strict;
    functionx.attrs = Arc::new(attrs);
}

pub fn modify_derived_item<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    action: AutomaticDeriveAction,
    function: &mut FunctionX,
) -> Result<(), VirErr> {
    let AutomaticDeriveAction::Special(special) = action else {
        return Ok(());
    };
    match special {
        SpecialTrait::Clone => {
            if function.name.path.last_segment().is_name("clone") {
                return clone_add_post_condition(bctx, id, inputs, span, function);
            }
        }
    }
    Ok(())
}

fn clone_add_post_condition<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    mut id: rustc_span::def_id::DefId,
    inputs: &Vec<rustc_middle::ty::Ty>,
    span: Span,
    functionx: &mut FunctionX,
) -> Result<(), VirErr> {
    let fn_id = id;
    if inputs.len() >= 1 {
        use rustc_middle::ty::{AdtDef, TyKind};
        if let TyKind::Ref(_, t, _) = inputs[0].kind() {
            if let TyKind::Adt(AdtDef(adt_def_data), _) = t.kind() {
                // It's more convenient to put verifier::allow on the datatype than on the function
                id = adt_def_data.did;
            }
        }
    }
    let warn = |msg: &str| {
        crate::attributes::warning_maybe(
            bctx.ctxt.tcx,
            id,
            span,
            &WarningAllow::AutoderiveCloneWithoutSpec,
            || msg,
            |msg| bctx.ctxt.diagnostics.borrow_mut().push(VirErrAs::Warning(msg)),
        );
    };
    let warn_unexpected = || {
        warn(
            "autoderive Clone impl does not take the form Verus expects; continuing, but without adding a specification for the derived Clone impl",
        )
    };
    let warn_unsupported = || {
        warn(
            "Verus does not currently support autoderive Clone impl when the clone is not a copy; continuing, but without adding a specification for the derived Clone impl",
        )
    };

    let Some(body) = &functionx.body else {
        return Ok(());
    };

    let uses_copy;
    let self_var;

    match &body.x {
        ExprX::Block(_stmts, Some(last_expr)) => match &last_expr.x {
            ExprX::ReadPlace(pl, _) => match &pl.x {
                PlaceX::Local(id) if &*id.0 == "self" => {
                    uses_copy = true;
                    self_var = Some(last_expr.clone());
                }
                _ => {
                    warn_unexpected();
                    return Ok(());
                }
            },
            ExprX::Ctor { .. } => {
                uses_copy = false;
                self_var = None;
            }
            _ => {
                warn_unexpected();
                return Ok(());
            }
        },
        _ => {
            warn_unexpected();
            return Ok(());
        }
    }

    if functionx.ensure.0.len() != 0 {
        warn_unexpected();
        return Ok(());
    }

    // -V alloc-check: `*self`, or field-by-field clones that allocate nothing
    add_derived_clone_level(bctx, fn_id, span, functionx);

    if uses_copy {
        // Add `ensures ret == self`
        let self_var = self_var.unwrap();
        let ret_var = SpannedTyped::new(
            &self_var.span,
            &self_var.typ,
            ExprX::Var(functionx.inner_ret.x.name.clone()),
        );
        let eq_expr = SpannedTyped::new(
            &self_var.span,
            &vir::ast_util::bool_typ(),
            ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_var.clone(), self_var.clone()),
        );

        let eq_expr = cleanup_span_ids(bctx, span, &eq_expr);
        functionx.ensure.0 = Arc::new(vec![eq_expr]);
    } else {
        warn_unsupported();
    }

    Ok(())
}

/// Give each node a unique ID. This inserts 'None' for every var into the local_hir_vir_ids
/// list, so it's only safe for pure expressions (e.g., in asserts or signatures).
fn cleanup_span_ids<'tcx>(bctx: &BodyCtxt<'tcx>, span: Span, expr: &Expr) -> Expr {
    vir::ast_visitor::map_expr_place_visitor(
        expr,
        &|e: &Expr| {
            let e = bctx.ctxt.spans.spanned_typed_new(span, &e.typ, e.x.clone());
            if matches!(&e.x, ExprX::Var(..) | ExprX::VarAt(..)) {
                let mut erasure_info = bctx.erasure_info.borrow_mut();
                erasure_info.local_hir_vir_ids.push((None, e.span.id));
            }
            Ok(e)
        },
        &|p: &Place| {
            let p = bctx.ctxt.spans.spanned_typed_new(span, &p.typ, p.x.clone());
            if matches!(&p.x, PlaceX::Local(..)) {
                let mut erasure_info = bctx.erasure_info.borrow_mut();
                erasure_info.local_hir_vir_ids.push((None, p.span.id));
            }
            Ok(p)
        },
    )
    .unwrap()
}
