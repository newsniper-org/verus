//! The step `induct(x)` of a `by(tactic)` script (without `from(..)` and without blocks), on a
//! `nat` or on a value of a datatype. The macro (builtin_macros/src/tactic.rs) cannot see the type
//! of `x`, so it writes
//!
//! ```text
//! let p = tactic_motive(x, G);
//! tactic_induct(p, x, { assert forall|x| tactic_induct_hyp(p, x) implies #[trigger] p(x) by { CASE } });
//! ```
//!
//! and the builtins are lowered here:
//! - `tactic_motive(x, G)` is the closure `|x'| G[x'/x]`, the goal as a function of `x`;
//! - the `assert forall` is turned into the cases of the induction, each with its own copy of the
//!   proof `CASE` and with the hypothesis for the type of `x`, each asserted;
//!   - on a `nat`: `x == 0`, and `x > 0 && p((x - 1) as nat)`; then vstd's
//!     `tactic::lemma_induct_nat(p, x)`, whose `requires` are the two cases;
//!   - on a value of a datatype: one case per variant, with `p(x->V.f)` for each field `f` of the
//!     variant whose type is the datatype (or a `Box` of it); then the principle lemma of the
//!     datatype, which rust_verify generates for the function (`lemma_stubs`, `lemma_function`):
//!
//! ```text
//! proof fn tactic_induct%f%..%T(p: spec_fn(T) -> bool, x: T)
//!     requires forall|y: T| hyp(p, y) ==> #[trigger] p(y)
//!     ensures p(x)
//!     decreases x
//! { if x is V { tactic_induct%f%..%T(p, x->V.f); .. } .. }
//! ```
//!
//! Nothing here is trusted. The cases are asserted (their proofs checked), and the principle lemma
//! is an ordinary proof function, verified with the function that uses it (its owning module is
//! that function's, and `--verify-function` includes it with that function: `user_filter.rs`).

use crate::context::{BodyCtxt, Context};
use crate::rust_to_vir_expr::expr_to_vir_consume;
use crate::util::err_span;
use crate::verus_items::{AssertItem, VerusItem};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{Expr, ExprKind, Node, QPath};
use rustc_middle::ty::{Ty, TyKind};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use std::sync::Arc;
use vir::ast::{
    AutospecUsage, BodyVisibility, CallTarget, CallTargetAttrs, CallTargetKind, Constant, Dt,
    ExprX, FieldOpr, Fun, FunctionAttrsX, FunctionKind, FunctionStubX, FunctionX, GenericBoundX,
    Ident, IntRange, ItemKind, LogicalOp, Mode, Opaqueness, ParamX, PlaceX, StmtX, TraitId, Typ,
    TypX, Typs, UnaryOp, UnaryOpr, VarBinderX, VarIdent, VariantCheck, VirErr, Visibility,
};

type VExpr = vir::ast::Expr;

/// A principle lemma that the `induct` steps of a function need (found when the function's stub
/// is made, before any body is lowered: the set of functions is fixed then)
pub(crate) struct TacticInductLemma {
    pub(crate) stub: vir::ast::FunctionStub,
    pub(crate) adt: DefId,
    pub(crate) span: Span,
}

/// The shape of a datatype for induction: its variants, and in each the fields whose type is the
/// datatype itself (or a `Box` of it)
struct DtShape {
    dt: Dt,
    typ_params: vir::ast::TypPositives,
    typ_bounds: vir::ast::GenericBounds,
    is_enum: bool,
    name: String,
    variants: Vec<(Ident, Vec<(Ident, Typ)>)>,
}

/// Is the datatype one that `induct` can work on, and what is its shape? `Err` is the reason it
/// cannot (a message to follow "`induct`: ")
fn dt_shape<'tcx>(ctxt: &Context<'tcx>, span: Span, adt_did: DefId) -> Result<DtShape, String> {
    let tcx = ctxt.tcx;
    let adt = tcx.adt_def(adt_did);
    let name = tcx.def_path_str(adt_did);
    if adt.is_union() {
        return Err(format!("`{name}` is a union"));
    }
    let ty = tcx.type_of(adt_did).instantiate_identity().skip_normalization();
    let typ = ctxt.mid_ty_to_vir(adt_did, span, &ty, None).map_err(|e| e.note.clone())?;
    let dt = match &*typ {
        TypX::Datatype(dt @ Dt::Path(_), _, _) => dt.clone(),
        _ => return Err(format!("`{name}` is not a datatype")),
    };
    let (typ_params, typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_no_polarity(
        tcx,
        &ctxt.verus_items,
        span,
        None,
        adt_did,
        None,
    )
    .map_err(|e| e.note.clone())?;
    for bound in typ_bounds.iter() {
        if !matches!(&**bound, GenericBoundX::Trait(TraitId::Sizedness(_), _)) {
            return Err(format!(
                "`{name}` has a type parameter with a trait bound or a const parameter, which is not supported yet"
            ));
        }
    }
    let mut variants = vec![];
    for variant in adt.variants().iter() {
        let mut rec_fields = vec![];
        for field in variant.fields.iter() {
            let field_ty = tcx.type_of(field.did).instantiate_identity().skip_normalization();
            let rec = field_ty == ty || (field_ty.is_box() && field_ty.boxed_ty() == Some(ty));
            if rec {
                let field_typ = ctxt
                    .mid_ty_to_vir(adt_did, span, &field_ty, None)
                    .map_err(|e| e.note.clone())?;
                rec_fields.push((vir::def::field_ident_from_rust(field.name.as_str()), field_typ));
            }
        }
        variants.push((Arc::new(variant.name.to_string()), rec_fields));
    }
    let typ_params = Arc::new(
        typ_params.iter().map(|x| (x.clone(), vir::ast::AcceptRecursiveType::Accept)).collect(),
    );
    Ok(DtShape { dt, typ_params, typ_bounds, is_enum: adt.is_enum(), name, variants })
}

/// Are the datatype and all its fields visible in the module of `from` (a function)? The
/// hypotheses and the principle lemma read the fields there
fn check_visible<'tcx>(ctxt: &Context<'tcx>, adt_did: DefId, from: DefId) -> Result<(), String> {
    let tcx = ctxt.tcx;
    let Some(local) = from.as_local() else { return Ok(()) };
    let module = tcx.parent_module_from_def_id(local).to_def_id();
    let name = tcx.def_path_str(adt_did);
    if !tcx.visibility(adt_did).is_accessible_from(module, tcx) {
        return Err(format!("`{name}` is not visible here"));
    }
    for variant in tcx.adt_def(adt_did).variants().iter() {
        for field in variant.fields.iter() {
            if !field.vis.is_accessible_from(module, tcx) {
                return Err(format!(
                    "the field `{}` of `{name}` is not visible here (induction reads the fields of each variant)",
                    field.name
                ));
            }
        }
    }
    Ok(())
}

fn mk(ctxt: &Context, span: Span, typ: &Typ, x: ExprX) -> VExpr {
    ctxt.spanned_typed_new(span, typ, x)
}

fn bool_typ() -> Typ {
    Arc::new(TypX::Bool)
}

/// `p(arg)`
fn apply(ctxt: &Context, span: Span, p: VExpr, arg: VExpr) -> VExpr {
    mk(
        ctxt,
        span,
        &bool_typ(),
        ExprX::Call {
            target: CallTarget::FnSpec(p),
            args: Arc::new(vec![arg]),
            post_args: None,
            body: None,
        },
    )
}

fn and(ctxt: &Context, span: Span, a: VExpr, b: VExpr) -> VExpr {
    mk(ctxt, span, &bool_typ(), ExprX::Logical(LogicalOp::And, a, b))
}

fn is_variant(ctxt: &Context, span: Span, shape: &DtShape, variant: &Ident, y: VExpr) -> VExpr {
    mk(
        ctxt,
        span,
        &bool_typ(),
        ExprX::UnaryOpr(
            UnaryOpr::IsVariant { datatype: shape.dt.clone(), variant: variant.clone() },
            y,
        ),
    )
}

/// `y->V.f` (with the field's type for the datatype's type arguments `typ_args`)
fn field(
    ctxt: &Context,
    span: Span,
    shape: &DtShape,
    typ_args: &Typs,
    variant: &Ident,
    (f, ftyp): &(Ident, Typ),
    y: VExpr,
) -> VExpr {
    let ftyp = vir::sst_util::subst_typ_for_datatype(&shape.typ_params, typ_args, ftyp);
    mk(
        ctxt,
        span,
        &ftyp,
        ExprX::UnaryOpr(
            UnaryOpr::Field(FieldOpr {
                datatype: shape.dt.clone(),
                variant: variant.clone(),
                field: f.clone(),
                get_variant: true,
                check: VariantCheck::None,
            }),
            y,
        ),
    )
}

/// The hypothesis of the case `y` of the induction: for each variant `V` that has fields of the
/// datatype's type, `y is V ==> p(y->V.f) && ..` (without the test for a struct)
fn hyp(
    ctxt: &Context,
    span: Span,
    shape: &DtShape,
    typ_args: &Typs,
    p: &dyn Fn() -> VExpr,
    y: &dyn Fn() -> VExpr,
) -> VExpr {
    let mut conj: Option<VExpr> = None;
    for (variant, fields) in shape.variants.iter() {
        let mut facts: Option<VExpr> = None;
        for f in fields.iter() {
            let fact = apply(ctxt, span, p(), field(ctxt, span, shape, typ_args, variant, f, y()));
            facts = Some(match facts {
                None => fact,
                Some(prev) => and(ctxt, span, prev, fact),
            });
        }
        let Some(facts) = facts else { continue };
        let case = if shape.is_enum {
            mk(
                ctxt,
                span,
                &bool_typ(),
                ExprX::Logical(
                    LogicalOp::Implies,
                    is_variant(ctxt, span, shape, variant, y()),
                    facts,
                ),
            )
        } else {
            facts
        };
        conj = Some(match conj {
            None => case,
            Some(prev) => and(ctxt, span, prev, case),
        });
    }
    conj.unwrap_or_else(|| mk(ctxt, span, &bool_typ(), ExprX::Const(Constant::Bool(true))))
}

fn call(ctxt: &Context, span: Span, fun: Fun, typ_args: Typs, args: Vec<VExpr>) -> VExpr {
    mk(
        ctxt,
        span,
        &vir::ast_util::unit_typ(),
        ExprX::Call {
            target: CallTarget::Fun(
                CallTargetKind::Static,
                fun,
                typ_args,
                Arc::new(vec![]),
                CallTargetAttrs {
                    autospec: AutospecUsage::Final,
                    const_var: false,
                    assume_external_allowed: false,
                    trusted_call: false,
                    into_forward: None,
                },
            ),
            args: Arc::new(args),
            post_args: None,
            body: None,
        },
    )
}

fn stmt(ctxt: &Context, span: Span, e: VExpr) -> vir::ast::Stmt {
    ctxt.spanned_new(span, StmtX::Expr(e))
}

/// The ADT of a variable's declared type, from the HIR (no type-checking: the stubs are made
/// before the crate is type-checked): a parameter of the function, or a `let`, closure or `forall`
/// parameter whose type is written
/// (also through `Ghost(x)`/`Tracked(x)` parameters and `let ghost`/`let tracked`, which the
/// macro writes as an untyped `let x;` assigned from a typed variable)
fn binding_adt<'tcx>(
    ctxt: &Context<'tcx>,
    fn_def_id: DefId,
    body: &'tcx rustc_hir::Body<'tcx>,
    hid: rustc_hir::HirId,
    depth: usize,
) -> Option<DefId> {
    let tcx = ctxt.tcx;
    let adt_of_ty = |ty: Ty<'tcx>| match ty.kind() {
        TyKind::Adt(adt, args) => {
            use crate::verus_items::BuiltinTypeItem;
            match ctxt.verus_items.id_to_name.get(&adt.did()) {
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Ghost | BuiltinTypeItem::Tracked)) => {
                    match args.type_at(0).kind() {
                        TyKind::Adt(adt, _) => Some(adt.did()),
                        _ => None,
                    }
                }
                _ => Some(adt.did()),
            }
        }
        _ => None,
    };
    let hir_ty_adt = |ty: &rustc_hir::Ty<'tcx>| -> Option<DefId> {
        let rustc_hir::TyKind::Path(QPath::Resolved(None, path)) = &ty.kind else { return None };
        match path.res {
            Res::Def(DefKind::Enum | DefKind::Struct, did) => Some(did),
            Res::Def(DefKind::TyAlias, did) => {
                adt_of_ty(tcx.type_of(did).instantiate_identity().skip_normalization())
            }
            Res::SelfTyAlias { alias_to, .. } => {
                adt_of_ty(tcx.type_of(alias_to).instantiate_identity().skip_normalization())
            }
            _ => None,
        }
    };
    for (i, param) in body.params.iter().enumerate() {
        if param.pat.hir_id == hid {
            let sig = tcx.fn_sig(fn_def_id).instantiate_identity().skip_binder();
            return sig.inputs().get(i).and_then(|ty| adt_of_ty(*ty));
        }
    }
    for (_, node) in tcx.hir_parent_iter(hid) {
        match node {
            Node::LetStmt(l) => {
                if l.pat.hir_id != hid {
                    return None;
                }
                if let Some(t) = l.ty {
                    return hir_ty_adt(t);
                }
                if l.init.is_some() || depth >= 3 {
                    return None;
                }
                // `let x;` then `x = y` (or `y.view()`, `y.get()`): the type of `y`
                let from = assigned_from(ctxt, body, hid)?;
                return binding_adt(ctxt, fn_def_id, body, from, depth + 1);
            }
            Node::Expr(Expr { kind: ExprKind::Closure(c), .. }) => {
                let cbody = tcx.hir_body(c.body);
                for (i, param) in cbody.params.iter().enumerate() {
                    if param.pat.hir_id == hid {
                        return c.fn_decl.inputs.get(i).and_then(|t| hir_ty_adt(t));
                    }
                }
                return None;
            }
            Node::Param(_) | Node::Pat(_) => {}
            _ => return None,
        }
    }
    None
}

/// The variable `y` of the first assignment `x = y` (or `x = y.view()`, `x = y.get()`) in the body
fn assigned_from<'tcx>(
    ctxt: &Context<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    x: rustc_hir::HirId,
) -> Option<rustc_hir::HirId> {
    struct Finder<'a, 'tcx> {
        ctxt: &'a Context<'tcx>,
        x: rustc_hir::HirId,
        from: Option<rustc_hir::HirId>,
    }
    fn local_of(e: &Expr) -> Option<rustc_hir::HirId> {
        match &e.kind {
            ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
                Res::Local(h) => Some(h),
                _ => None,
            },
            _ => None,
        }
    }
    impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for Finder<'a, 'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;
        fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
            self.ctxt.tcx
        }
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self.from.is_some() {
                return;
            }
            if let ExprKind::Assign(lhs, rhs, _) = &e.kind {
                if local_of(lhs) == Some(self.x) {
                    let rhs = match &rhs.kind {
                        ExprKind::MethodCall(seg, recv, [], _)
                            if seg.ident.name.as_str() == "view"
                                || seg.ident.name.as_str() == "get" =>
                        {
                            *recv
                        }
                        _ => *rhs,
                    };
                    self.from = local_of(rhs).filter(|h| *h != self.x);
                    return;
                }
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }
    let mut finder = Finder { ctxt, x, from: None };
    rustc_hir::intravisit::Visitor::visit_body(&mut finder, body);
    finder.from
}

/// The stubs of the principle lemmas that the `induct` steps in the body of the function `parent`
/// need: one per datatype (found from the declared type of the variable; `induct_to_vir` reports
/// an `induct` on a datatype whose lemma is missing)
pub(crate) fn lemma_stubs<'tcx>(
    ctxt: &Context<'tcx>,
    fn_def_id: DefId,
    body_id: &rustc_hir::BodyId,
    parent: &FunctionStubX,
) -> Vec<TacticInductLemma> {
    let Some(module) = &parent.owning_module else { return vec![] };
    let tcx = ctxt.tcx;
    let body = tcx.hir_body(*body_id);
    struct Finder<'a, 'tcx> {
        ctxt: &'a Context<'tcx>,
        found: Vec<(&'tcx Expr<'tcx>, Span)>,
    }
    impl<'a, 'tcx> rustc_hir::intravisit::Visitor<'tcx> for Finder<'a, 'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;
        fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
            self.ctxt.tcx
        }
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Call(f, args) = &e.kind {
                if let ExprKind::Path(QPath::Resolved(None, path)) = &f.kind {
                    if let Res::Def(_, did) = path.res {
                        if args.len() == 3
                            && matches!(
                                self.ctxt.verus_items.id_to_name.get(&did),
                                Some(VerusItem::Assert(AssertItem::TacticInduct))
                            )
                        {
                            self.found.push((&args[1], e.span));
                        }
                    }
                }
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }
    let mut finder = Finder { ctxt, found: vec![] };
    rustc_hir::intravisit::Visitor::visit_body(&mut finder, body);
    let parent_fun = Arc::new(vir::ast::FunX { path: parent.name.path.clone() });
    let mut lemmas: Vec<TacticInductLemma> = vec![];
    for (x, span) in finder.found {
        let ExprKind::Path(QPath::Resolved(None, path)) = &x.kind else { continue };
        let Res::Local(hid) = path.res else { continue };
        let Some(adt_did) = binding_adt(ctxt, fn_def_id, body, hid, 0) else { continue };
        if ctxt.verus_items.id_to_name.contains_key(&adt_did)
            || lemmas.iter().any(|l| l.adt == adt_did)
        {
            continue;
        }
        let adt = tcx.adt_def(adt_did);
        if adt.is_box() || adt.is_union() {
            continue;
        }
        // (a datatype that `induct` cannot work on gets no lemma; `induct_to_vir` reports why)
        let Ok(shape) = dt_shape(ctxt, span, adt_did) else { continue };
        let Dt::Path(dt_path) = &shape.dt else { continue };
        let t = Arc::new(TypX::Datatype(
            shape.dt.clone(),
            Arc::new(
                shape.typ_params.iter().map(|(x, _)| Arc::new(TypX::TypParam(x.clone()))).collect(),
            ),
            Arc::new(vec![]),
        ));
        let p_typ = Arc::new(TypX::SpecFn(Arc::new(vec![t.clone()]), bool_typ()));
        let param = |name: &str, typ: &Typ| {
            ctxt.spanned_new(
                span,
                ParamX {
                    name: lemma_param(name),
                    typ: typ.clone(),
                    mode: Mode::Spec,
                    unwrapped_info: None,
                    user_mut: false,
                },
            )
        };
        let vis = Visibility { restricted_to: Some(module.clone()) };
        let stub = ctxt.spanned_new(
            span,
            FunctionStubX {
                name: vir::def::tactic_induct_lemma_name(&parent_fun, dt_path),
                proxy: None,
                kind: FunctionKind::Static,
                visibility: vis.clone(),
                body_visibility: BodyVisibility::Visibility(vis.clone()),
                opaqueness: Opaqueness::Opaque,
                owning_module: Some(module.clone()),
                mode: Mode::Proof,
                typ_params: Arc::new(shape.typ_params.iter().map(|(x, _)| x.clone()).collect()),
                typ_bounds: shape.typ_bounds.clone(),
                params: Arc::new(vec![param("p", &p_typ), param("x", &t)]),
                outer_ret: ctxt.spanned_new(
                    span,
                    ParamX {
                        name: vir::ast_util::air_unique_var(vir::def::RETURN_VALUE),
                        typ: vir::ast_util::unit_typ(),
                        mode: Mode::Proof,
                        unwrapped_info: None,
                        user_mut: false,
                    },
                ),
                item_kind: ItemKind::Function,
                attrs: Arc::new(FunctionAttrsX {
                    uses_ghost_blocks: true,
                    alloc_checked_crate: ctxt.cmd_line_args.alloc_check,
                    ..Default::default()
                }),
                decreases_len: 1,
                returns: false,
            },
        );
        lemmas.push(TacticInductLemma { stub, adt: adt_did, span });
    }
    lemmas
}

fn lemma_param(name: &str) -> VarIdent {
    VarIdent(Arc::new(name.to_string()), vir::ast::VarIdentDisambiguate::NoBodyParam)
}

/// The principle lemma (its body, requires, ensures and decreases), for a stub of `lemma_stubs`
pub(crate) fn lemma_function<'tcx>(
    ctxt: &Context<'tcx>,
    lemma: &TacticInductLemma,
) -> Result<vir::ast::Function, VirErr> {
    let span = lemma.span;
    let shape = match dt_shape(ctxt, span, lemma.adt) {
        Ok(shape) => shape,
        Err(msg) => return err_span(span, format!("`induct`: {msg}")),
    };
    let stub = &lemma.stub.x;
    let p_typ = stub.params[0].x.typ.clone();
    let t = stub.params[1].x.typ.clone();
    let typ_args: Typs = match &*t {
        TypX::Datatype(_, args, _) => args.clone(),
        _ => return err_span(span, "`induct`: internal error: the lemma's parameter"),
    };
    let p = || mk(ctxt, span, &p_typ, ExprX::Var(lemma_param("p")));
    let x = || mk(ctxt, span, &t, ExprX::Var(lemma_param("x")));
    let y_name = VarIdent(
        Arc::new("y".to_string()),
        vir::ast::VarIdentDisambiguate::VirTemp(ctxt.spans.get_next_span_id()),
    );
    let y = || mk(ctxt, span, &t, ExprX::Var(y_name.clone()));
    // requires forall|y: T| hyp(p, y) ==> #[trigger] p(y)
    let trigger = mk(
        ctxt,
        span,
        &bool_typ(),
        ExprX::Unary(
            UnaryOp::Trigger(vir::ast::TriggerAnnotation::Trigger(None)),
            apply(ctxt, span, p(), y()),
        ),
    );
    let body = mk(
        ctxt,
        span,
        &bool_typ(),
        ExprX::Logical(LogicalOp::Implies, hyp(ctxt, span, &shape, &typ_args, &p, &y), trigger),
    );
    let require = mk(
        ctxt,
        span,
        &bool_typ(),
        ExprX::Quant(
            vir::ast::Quant { quant: air::ast::Quant::Forall },
            Arc::new(vec![Arc::new(VarBinderX { name: y_name.clone(), a: t.clone() })]),
            body,
        ),
    );
    let ensure = apply(ctxt, span, p(), x());
    // the body: the lemma for each field of the datatype's type, in its variant
    let mut stmts = vec![];
    for (variant, fields) in shape.variants.iter() {
        if fields.is_empty() {
            continue;
        }
        let calls: Vec<vir::ast::Stmt> = fields
            .iter()
            .map(|f| {
                let arg = field(ctxt, span, &shape, &typ_args, variant, f, x());
                stmt(
                    ctxt,
                    span,
                    call(ctxt, span, stub.name.clone(), typ_args.clone(), vec![p(), arg]),
                )
            })
            .collect();
        let block = mk(ctxt, span, &vir::ast_util::unit_typ(), ExprX::Block(Arc::new(calls), None));
        let e = if shape.is_enum {
            mk(
                ctxt,
                span,
                &vir::ast_util::unit_typ(),
                ExprX::If(is_variant(ctxt, span, &shape, variant, x()), block, None),
            )
        } else {
            block
        };
        stmts.push(stmt(ctxt, span, e));
    }
    let body = mk(ctxt, span, &vir::ast_util::unit_typ(), ExprX::Block(Arc::new(stmts), None));
    let FunctionStubX {
        name,
        proxy,
        kind,
        visibility,
        body_visibility,
        opaqueness,
        owning_module,
        mode,
        typ_params,
        typ_bounds,
        params,
        outer_ret,
        item_kind,
        attrs,
        returns: _,
        decreases_len: _,
    } = stub.clone();
    let functionx = FunctionX {
        name,
        proxy,
        kind,
        visibility,
        body_visibility,
        opaqueness,
        owning_module,
        mode,
        typ_params,
        typ_bounds,
        params,
        outer_ret: outer_ret.clone(),
        inner_ret: outer_ret,
        decrease_by: None,
        item_kind,
        attrs,
        extra_dependencies: vec![],
        body: Some(body),
        return_opaque_type_eqs: Arc::new(vec![]),
        require: Arc::new(vec![require]),
        ensure: (Arc::new(vec![ensure]), Arc::new(vec![])),
        returns: None,
        decrease: Arc::new(vec![x()]),
        decrease_when: None,
        fndef_axioms: None,
        mask_spec: None,
        atomic_update: None,
        unwind_spec: None,
        allocates: None,
        allocates_cond: None,
        deallocations: None,
        deallocates: None,
        hidden: Arc::new(vec![]),
    };
    Ok(vir::def::Spanned::new(lemma.stub.span.clone(), functionx))
}

/// `tactic_motive(x, G)`: the closure `|x'| G[x'/x]` (a fresh `x'`)
pub(crate) fn motive_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    args: &[&'tcx Expr<'tcx>],
) -> Result<ExprX, VirErr> {
    let x = expr_to_vir_consume(bctx, args[0])?;
    let xv = match &x.x {
        ExprX::Var(v) => v.clone(),
        ExprX::ReadPlace(p, _) => match &p.x {
            PlaceX::Local(v) => v.clone(),
            _ => return err_span(args[0].span, "`induct`: expected the name of a variable"),
        },
        _ => return err_span(args[0].span, "`induct`: expected the name of a variable"),
    };
    let goal = expr_to_vir_consume(bctx, args[1])?;
    let x2 = vir::def::subst_rename_ident(&xv, bctx.ctxt.spans.get_next_span_id());
    let old_flag = std::cell::Cell::new(false);
    let goal = vir::ast_visitor::map_expr_visitor_env(
        &goal,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_, scopes, e: &VExpr| {
            Ok(match &e.x {
                ExprX::Var(v) if *v == xv => e.new_x(ExprX::Var(x2.clone())),
                ExprX::VarAt(v, _) if *v == xv => {
                    old_flag.set(true);
                    e.clone()
                }
                // (a `#[trigger]` outside the quantifiers of `G` is one of a quantifier around the
                // goal, e.g. the one that `intro` took it out of; it means nothing in the closure)
                ExprX::Unary(UnaryOp::Trigger(_), inner) if scopes.num_scopes() == 0 => {
                    inner.clone()
                }
                _ => e.clone(),
            })
        },
        &|_, _, s| Ok(vec![s.clone()]),
        &|_, t| Ok(t.clone()),
        &|_, _, p| {
            Ok(match &p.x {
                PlaceX::Local(v) if *v == xv => p.new_x(PlaceX::Local(x2.clone())),
                _ => p.clone(),
            })
        },
        &|_, _, pat| Ok(pat.clone()),
    )?;
    if old_flag.get() {
        return err_span(
            expr.span,
            "`induct(x)`: the goal uses `old(x)`, which is not a function of `x`",
        );
    }
    // (the read of `x` written here is kept, as `x == x`, so that erasure sees it: a read it does
    // not see would be kept in the compiled code, where an `x` bound by a `forall` does not exist)
    let ctxt = &bctx.ctxt;
    let same = mk(
        ctxt,
        expr.span,
        &bool_typ(),
        ExprX::Binary(
            vir::ast::BinaryOp::Eq(Mode::Spec),
            x.clone(),
            bctx.clone_expr_with_fresh_ids(&x),
        ),
    );
    let goal = mk(ctxt, expr.span, &bool_typ(), ExprX::Logical(LogicalOp::And, goal, same));
    let binder = Arc::new(VarBinderX { name: x2, a: x.typ.clone() });
    Ok(ExprX::Closure(Arc::new(vec![binder]), goal))
}

/// The `assert forall|x| .. implies p(x) by { CASE }` that the macro passes to `tactic_induct`:
/// its variable, its conclusion and its proof
fn step_parts(e: &VExpr) -> Option<(vir::ast::VarBinders<Typ>, VExpr, VExpr, VExpr)> {
    match &e.x {
        ExprX::Block(stmts, None) if stmts.len() == 1 => match &stmts[0].x {
            StmtX::Expr(e) => step_parts(e),
            _ => None,
        },
        ExprX::Block(stmts, Some(e)) if stmts.is_empty() => step_parts(e),
        ExprX::AssertBy { vars, require, ensure, proof, isolate: None } if vars.len() == 1 => {
            Some((vars.clone(), require.clone(), ensure.clone(), proof.clone()))
        }
        _ => None,
    }
}

/// The proof of one case: the notes of the assertions that the script made say which case it is
/// (the one of this step) or in which case they are (the others)
fn fill_case(e: &VExpr, text: &str, where_: &str) -> Result<VExpr, VirErr> {
    vir::ast_visitor::map_expr_visitor(e, &|e: &VExpr| match &e.x {
        ExprX::UnaryOpr(UnaryOpr::ProofNote(label), inner)
            if !label.is_custom_err && label.text.starts_with("from the tactic step ") =>
        {
            let new_text = if *label.text == "from the tactic step `induct` (%case%)" {
                format!("from the tactic step `induct` ({text})")
            } else {
                format!("{}, where {where_}", label.text)
            };
            let label = vir::ast::ProofNoteLabel { text: Arc::new(new_text), ..label.clone() };
            Ok(e.new_x(ExprX::UnaryOpr(UnaryOpr::ProofNote(label), inner.clone())))
        }
        _ => Ok(e.clone()),
    })
}

/// `tactic_induct(p, x, { assert forall|x| .. implies p(x) by { CASE } })`
pub(crate) fn induct_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    args: &[&'tcx Expr<'tcx>],
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let ctxt = &bctx.ctxt;
    let tcx = ctxt.tcx;
    let shown = tcx
        .sess
        .source_map()
        .span_to_snippet(args[1].span)
        .unwrap_or_else(|_| "the variable".to_string());
    // (the type is checked before the proof is lowered, so that its errors do not come first)
    let ty = bctx.types.expr_ty_adjusted(args[1]);
    let typ = bctx.mid_ty_to_vir(args[1].span, &ty)?;
    enum Kind {
        Nat,
        Datatype(DefId, Typs),
    }
    let kind = match (&*typ, ty.kind()) {
        (TypX::Int(IntRange::Nat), _) => Kind::Nat,
        (TypX::Int(IntRange::Int), _) => {
            return err_span(
                args[1].span,
                format!(
                    "`induct({shown})`: `{shown}` is an `int`; write `induct({shown}, from(lo))` for induction from a start `lo`"
                ),
            );
        }
        (TypX::Datatype(Dt::Path(_), typ_args, _), TyKind::Adt(adt, _))
            if !adt.is_box() && !ctxt.verus_items.id_to_name.contains_key(&adt.did()) =>
        {
            Kind::Datatype(adt.did(), typ_args.clone())
        }
        (_, TyKind::Ref(..)) => {
            return err_span(
                args[1].span,
                format!(
                    "`induct({shown})`: `{shown}` is a reference; induction is on a `nat` or on a value of a datatype"
                ),
            );
        }
        _ => {
            return err_span(
                args[1].span,
                format!(
                    "`induct({shown})` is on a `nat` (or on an `int`, with `from(..)`) or on a value of a datatype (an enum or a struct), and `{shown}` is a `{ty}`"
                ),
            );
        }
    };
    let (shape, lemma) = match &kind {
        Kind::Nat => {
            if ctxt.no_vstd {
                return err_span(
                    span,
                    "`induct` on a `nat` uses vstd, and is not supported with `--no-vstd`",
                );
            }
            (None, vir::def::tactic_lemma_induct_nat_fun())
        }
        Kind::Datatype(adt_did, _) => {
            let checked = dt_shape(ctxt, span, *adt_did)
                .and_then(|shape| check_visible(ctxt, *adt_did, bctx.fun_id).map(|()| shape));
            let shape = match checked {
                Ok(shape) => shape,
                Err(msg) => return err_span(args[1].span, format!("`induct({shown})`: {msg}")),
            };
            let Some(lemmas) = &bctx.tactic_induct_lemmas else {
                return err_span(
                    args[1].span,
                    format!(
                        "`induct({shown})` on a datatype is supported only in the body of a function (the induction principle of `{}` is generated for the function)",
                        shape.name
                    ),
                );
            };
            let Some((_, lemma)) = lemmas.iter().find(|(d, _)| d == adt_did) else {
                return err_span(
                    args[1].span,
                    format!(
                        "`induct({shown})`: write the type of `{shown}` where `{shown}` is bound (a parameter of the function, or a `let`, closure or `forall` variable with its type), so that the induction principle of `{}` can be made for this function",
                        shape.name
                    ),
                );
            };
            (Some(shape), lemma.clone())
        }
    };
    let p = expr_to_vir_consume(bctx, args[0])?;
    let x = expr_to_vir_consume(bctx, args[1])?;
    let step = expr_to_vir_consume(bctx, args[2])?;
    // (the `require` written there, `tactic_induct_hyp(p, x)`, is true; it is kept, conjoined with
    // the hypothesis of each case, so that its reads of `p` and `x` stay, for erasure)
    let Some((vars, written, ensure, proof)) = step_parts(&step) else {
        return err_span(span, "`tactic_induct`: expected an `assert forall` with one variable");
    };
    let xb = vars[0].clone();
    let n = xb.name.0.to_string();
    let fresh = |e: &VExpr| bctx.clone_expr_with_fresh_ids(e);
    // (every node made here goes through `fresh`, which registers its ids for erasure)
    let xv = || mk(ctxt, span, &xb.a, ExprX::Var(xb.name.clone()));
    let mut stmts = vec![];
    match (&kind, &shape) {
        (Kind::Nat, _) => {
            let nat = Arc::new(TypX::Int(IntRange::Nat));
            let int = Arc::new(TypX::Int(IntRange::Int));
            let num = |k: i64| {
                mk(ctxt, span, &nat, ExprX::Const(vir::ast_util::const_int_from_u128(k as u128)))
            };
            let base_req = mk(
                ctxt,
                span,
                &bool_typ(),
                ExprX::Binary(vir::ast::BinaryOp::Eq(Mode::Spec), xv(), num(0)),
            );
            let pos = mk(
                ctxt,
                span,
                &bool_typ(),
                ExprX::Binary(
                    vir::ast::BinaryOp::Inequality(vir::ast::InequalityOp::Gt),
                    xv(),
                    num(0),
                ),
            );
            let minus = mk(
                ctxt,
                span,
                &int,
                ExprX::Binary(
                    vir::ast::BinaryOp::Arith(vir::ast::ArithOp::Sub(
                        vir::ast::OverflowBehavior::Truncate(IntRange::Int),
                    )),
                    xv(),
                    num(1),
                ),
            );
            let prev = mk(
                ctxt,
                span,
                &nat,
                ExprX::Unary(UnaryOp::Clip { range: IntRange::Nat, truncate: true }, minus),
            );
            let step_req = and(ctxt, span, pos, apply(ctxt, span, p.clone(), prev));
            let base_text = format!("the base case, `{n} == 0`");
            let step_text = format!("the step, `{n} > 0`, with the goal for `{n} - 1`");
            let base = ExprX::AssertBy {
                vars: vars.clone(),
                require: and(ctxt, span, written.clone(), fresh(&base_req)),
                ensure: ensure.clone(),
                proof: fill_case(&proof, &base_text, &format!("`{n} == 0`"))?,
                isolate: None,
            };
            let step = ExprX::AssertBy {
                vars: vars.clone(),
                require: and(ctxt, span, fresh(&written), fresh(&step_req)),
                ensure: fresh(&ensure),
                proof: fill_case(&fresh(&proof), &step_text, &format!("`{n} > 0`"))?,
                isolate: None,
            };
            let unit = vir::ast_util::unit_typ();
            stmts.push(stmt(ctxt, span, mk(ctxt, span, &unit, base)));
            stmts.push(stmt(ctxt, span, mk(ctxt, span, &unit, step)));
            stmts.push(stmt(ctxt, span, call(ctxt, span, lemma, Arc::new(vec![]), vec![p, x])));
        }
        (Kind::Datatype(_, typ_args), Some(shape)) => {
            let require = and(
                ctxt,
                span,
                written,
                fresh(&hyp(ctxt, span, shape, typ_args, &|| p.clone(), &xv)),
            );
            // the cases, one per variant, each with its own copy of the proof
            let enum_name = &shape.name;
            let mut cases: Vec<(Option<VExpr>, VExpr)> = vec![];
            for (k, (variant, fields)) in shape.variants.iter().enumerate() {
                let is = if shape.is_enum {
                    format!("`{n}` is `{enum_name}::{variant}`")
                } else {
                    format!("`{n}` is a `{enum_name}`")
                };
                let text = match fields.len() {
                    0 => is.clone(),
                    1 => format!("{is}, with the goal for its field `{}`", fields[0].0),
                    _ => format!(
                        "{is}, with the goal for its fields {}",
                        fields.iter().map(|(f, _)| format!("`{f}`")).collect::<Vec<_>>().join(", ")
                    ),
                };
                let copy = if k == 0 { proof.clone() } else { fresh(&proof) };
                let body = fill_case(&copy, &text, &is)?;
                let test = (shape.is_enum && k + 1 < shape.variants.len())
                    .then(|| fresh(&is_variant(ctxt, span, shape, variant, xv())));
                cases.push((test, body));
            }
            let mut chain: Option<VExpr> = None;
            for (test, body) in cases.into_iter().rev() {
                chain = Some(match (test, chain) {
                    (None, None) => body,
                    (Some(test), Some(rest)) => {
                        mk(ctxt, span, &body.typ.clone(), ExprX::If(test, body, Some(rest)))
                    }
                    (Some(test), None) => {
                        mk(ctxt, span, &body.typ.clone(), ExprX::If(test, body, None))
                    }
                    (None, Some(_)) => unreachable!(),
                });
            }
            let proof = chain.unwrap_or(proof);
            let assert_by =
                ExprX::AssertBy { vars: vars.clone(), require, ensure, proof, isolate: None };
            let unit = vir::ast_util::unit_typ();
            stmts.push(stmt(ctxt, span, mk(ctxt, span, &unit, assert_by)));
            stmts.push(stmt(ctxt, span, call(ctxt, span, lemma, typ_args.clone(), vec![p, x])));
        }
        _ => unreachable!(),
    }
    Ok(ExprX::Block(Arc::new(stmts), None))
}

/// `tactic_induct_hyp(p, x)`: `p(x) || true`, which is true (the hypothesis of each case is made
/// by `induct_to_vir`, conjoined with it); the reads of `p` and `x` are kept, for erasure
pub(crate) fn hyp_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    args: &[&'tcx Expr<'tcx>],
) -> Result<ExprX, VirErr> {
    let p = expr_to_vir_consume(bctx, args[0])?;
    let x = expr_to_vir_consume(bctx, args[1])?;
    let t = mk(&bctx.ctxt, expr.span, &bool_typ(), ExprX::Const(Constant::Bool(true)));
    Ok(ExprX::Logical(LogicalOp::Or, apply(&bctx.ctxt, expr.span, p, x), t))
}
