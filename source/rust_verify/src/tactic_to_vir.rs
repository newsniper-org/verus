//! The steps of a `by(tactic)` script that work on the goal after `unfold`, which the macro that
//! expands scripts (builtin_macros/src/tactic.rs) cannot see: it writes them as calls of builtins
//! (`tactic_unfold`, `tactic_split`, `tactic_split_each`, with `tactic_goal()` for the goal), and
//! they are lowered here, with the goal in `BodyCtxt::tactic_goal`.
//!
//! What they produce is ordinary proof code, checked as usual: `Fuel` (the `reveal_with_fuel`
//! of `unfold`), `AssertBy`, `If` and `Block`. Every goal they work on is asserted, never assumed,
//! and the macro still asserts the original goal after the script, so a wrong expansion here can
//! only make a proof fail. They are allowed only in the block of a script, in the proof of an
//! `assert .. by` (`in_tactic`, `in_assert_by_proof`), where no assumption is allowed and every
//! variable is spec.
//! - `unfold(f)`: the goal with each call of `f` replaced by `f`'s body (one level), its binders
//!   renamed and its parameters replaced by the arguments. It is asserted, after `f` is revealed,
//!   with the rest of the script as its proof, and the enclosing step asserts the goal.
//! - `split()`: a conjunction is split into its parts (an `if`, into its branches); each part is
//!   asserted, with the rest of the script (lowered once, with a placeholder for the goal, and
//!   copied for each part) or its own block as its proof.

use crate::context::BodyCtxt;
use crate::rust_to_vir_expr::expr_to_vir_consume;
use crate::util::err_span;
use crate::verus_items::AssertItem;
use rustc_hir::{Expr, ExprKind};
use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    Constant, ExprX, Fun, FunX, Function, FunctionKind, ItemKind, LogicalOp, Mode, PatternX,
    PlaceX, ProofNoteLabel, StmtX, TypX, UnaryOpr, UnfinalizedReadKind, VarBinderX, VarIdent,
    VarIdentDisambiguate, VirErr,
};

type VExpr = vir::ast::Expr;

pub(crate) fn tactic_step_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    item: AssertItem,
    args: &[&'tcx Expr<'tcx>],
) -> Result<ExprX, VirErr> {
    let (name, n_args) = match item {
        AssertItem::TacticUnfold => ("tactic_unfold", 3),
        AssertItem::TacticSplit => ("tactic_split", 1),
        AssertItem::TacticSplitEach => ("tactic_split_each", 1),
        AssertItem::TacticGoal => ("tactic_goal", 0),
        AssertItem::TacticIntro => ("tactic_intro", 1),
        AssertItem::TacticShow => ("tactic_show", 1),
        AssertItem::TacticMotive => ("tactic_motive", 2),
        AssertItem::TacticInductHyp => ("tactic_induct_hyp", 2),
        AssertItem::TacticInduct => ("tactic_induct", 3),
        _ => unreachable!(),
    };
    if !bctx.in_tactic || !bctx.in_assert_by_proof {
        return err_span(
            expr.span,
            format!("`{name}` is a step of a `by(tactic)` script, and is not used directly"),
        );
    }
    if args.len() != n_args {
        return err_span(expr.span, format!("`{name}`: expected {n_args} arguments"));
    }
    match item {
        AssertItem::TacticGoal => match &bctx.tactic_goal {
            // (in a block, so that the goal keeps its own span: what `show()` prints)
            Some(goal) => {
                Ok(ExprX::Block(Arc::new(vec![]), Some(bctx.clone_expr_with_fresh_ids(goal))))
            }
            None => err_span(
                expr.span,
                "`tactic_goal()` is the goal of a `by(tactic)` script after `unfold`, and is used only there",
            ),
        },
        AssertItem::TacticUnfold => unfold_to_vir(bctx, expr, args),
        AssertItem::TacticSplit => split_to_vir(bctx, expr, args[0]),
        AssertItem::TacticSplitEach => split_each_to_vir(bctx, expr, args[0]),
        AssertItem::TacticIntro => intro_to_vir(bctx, expr, args[0]),
        AssertItem::TacticShow => show_to_vir(bctx, expr, args[0]),
        AssertItem::TacticMotive => crate::tactic_induct::motive_to_vir(bctx, expr, args),
        AssertItem::TacticInductHyp => crate::tactic_induct::hyp_to_vir(bctx, expr, args),
        AssertItem::TacticInduct => crate::tactic_induct::induct_to_vir(bctx, expr, args),
        _ => unreachable!(),
    }
}

fn bool_typ() -> vir::ast::Typ {
    Arc::new(TypX::Bool)
}

/// `e`, with the note of the tactic step that asserts it
fn with_note(e: VExpr, text: String) -> VExpr {
    let label = ProofNoteLabel { text: Arc::new(text), is_custom_err: false, isolate: None };
    e.new_x(ExprX::UnaryOpr(UnaryOpr::ProofNote(label), e.clone()))
}

/// `assert(ensure) by { proof }`
fn assert_by(bctx: &BodyCtxt, span: rustc_span::Span, ensure: VExpr, proof: VExpr) -> VExpr {
    let require = bctx.spanned_typed_new(span, &bool_typ(), ExprX::Const(Constant::Bool(true)));
    bctx.spanned_typed_new(
        span,
        &vir::ast_util::unit_typ(),
        ExprX::AssertBy { vars: Arc::new(vec![]), require, ensure, proof, isolate: None },
    )
}

fn stmt(bctx: &BodyCtxt, span: rustc_span::Span, e: VExpr) -> vir::ast::Stmt {
    bctx.spanned_new(span, StmtX::Expr(e))
}

fn fun_name(f: &Fun) -> String {
    match f.path.segments.last() {
        Some(s) => s.to_string(),
        None => vir::ast_util::fun_as_friendly_rust_name(f),
    }
}

/// `tactic_unfold(goal, { reveal_with_fuel(f, k); }, { rest })`
fn unfold_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    args: &[&'tcx Expr<'tcx>],
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let reveal = expr_to_vir_consume(bctx, args[1])?;
    let mut fuels: Vec<(Fun, u32)> = vec![];
    let mut other = false;
    vir::ast_visitor::expr_visitor_check::<VirErr, _>(&reveal, &mut |_, e| {
        match &e.x {
            ExprX::Fuel(f, k, false) => fuels.push((f.clone(), *k)),
            ExprX::Fuel(_, _, true) | ExprX::Header(_) => other = true,
            _ => {}
        }
        Ok(())
    })?;
    let (f, k) = match &fuels[..] {
        [fk] if !other => fk.clone(),
        _ => {
            return err_span(
                span,
                "`unfold`: expected one spec function, with a fuel of 1 or more",
            );
        }
    };
    let name = fun_name(&f);
    let function = unfold_target(bctx, span, &f, &name)?;
    let goal = untrigger(expr_to_vir_consume(bctx, args[0])?);
    let count = Cell::new(0usize);
    let unfolded = inline_calls(bctx, &goal, &function, &count)?;
    // (for `show()`: the arguments in place of `f`'s parameters, for each call)
    let mut desc = (*bctx.tactic_goal_desc).clone();
    let _ = vir::ast_visitor::expr_visitor_check::<VirErr, _>(&goal, &mut |_, e| {
        if let ExprX::Call {
            target: vir::ast::CallTarget::Fun(vir::ast::CallTargetKind::Static, g, ..),
            args,
            ..
        } = &e.x
        {
            if *g == function.x.name {
                let substs: Vec<String> = function
                    .x
                    .params
                    .iter()
                    .zip(args.iter())
                    .map(|(p, a)| format!("`{}` is `{}`", p.x.name.0, source_text(bctx, a)))
                    .collect();
                desc.push(format!("(`{name}` unfolded: in its body, {})", substs.join(", ")));
            }
        }
        Ok(())
    });
    if count.get() == 0 {
        return err_span(span, format!("`unfold({name})`: the goal has no call of `{name}`"));
    }
    // (fresh ids for the copy, whose parts came from `f` and from the goal)
    let unfolded = bctx.clone_expr_with_fresh_ids(&unfolded);
    let rest_bctx = BodyCtxt {
        tactic_goal: Some(unfolded.clone()),
        tactic_goal_desc: Arc::new(desc),
        ..bctx.clone()
    };
    let proof = expr_to_vir_consume(&rest_bctx, args[2])?;
    let fuel = if k == 1 { String::new() } else { format!(", fuel {k}") };
    let ensure = with_note(
        bctx.clone_expr_with_fresh_ids(&unfolded),
        format!("from the tactic step `unfold` (`{name}`, one level{fuel})"),
    );
    let check = assert_by(bctx, span, ensure, proof);
    Ok(ExprX::Block(Arc::new(vec![stmt(bctx, span, reveal), stmt(bctx, span, check)]), None))
}

/// The function that `unfold(f)` unfolds, with its body: a spec function (not a trait method)
/// whose body is visible here, other than the one being defined (or one being defined around
/// it: a cycle)
fn unfold_target<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: rustc_span::Span,
    f: &Fun,
    name: &str,
) -> Result<Function, VirErr> {
    let tcx = bctx.ctxt.tcx;
    let me = Arc::new(FunX { path: bctx.ctxt.def_id_to_vir_path(bctx.fun_id) });
    if *f == me {
        return err_span(span, format!("`unfold({name})`: `{name}` is the function being defined"));
    }
    let Some(query) = crate::query::get_global_query(tcx) else {
        return err_span(span, "`unfold`: internal error: no query");
    };
    let definition_err = |_| {
        crate::util::err_span_bare(span, format!("`unfold({name})`: its definition has errors"))
    };
    let stubs = query.get_all_function_stubs().map_err(definition_err)?;
    let Some(stub) = stubs.get(f) else {
        return err_span(span, format!("`unfold({name})`: `{name}` is not a function"));
    };
    if stub.x.mode != Mode::Spec
        || !matches!(stub.x.kind, FunctionKind::Static)
        || !matches!(stub.x.item_kind, ItemKind::Function)
    {
        return err_span(
            span,
            format!(
                "`unfold({name})`: only a spec function that is not a trait method can be unfolded into the goal"
            ),
        );
    }
    if let Some(my_module) = stubs.get(&me).and_then(|s| s.x.owning_module.clone()) {
        if !vir::ast_util::is_body_visible_to(&stub.x.body_visibility, &my_module) {
            return err_span(
                span,
                format!("`unfold({name})`: the body of `{name}` is not visible here"),
            );
        }
    }
    let pre_crate = query.get_pre_crate().map_err(definition_err)?;
    let function = if pre_crate.fun_name_to_info.contains_key(f) {
        if query.unchecked_function_in_progress(f) {
            return err_span(
                span,
                format!(
                    "`unfold({name})`: `{name}` is being defined, and a proof in it unfolds the function being defined here (a cycle)"
                ),
            );
        }
        query.get_unchecked_function(f).map_err(definition_err)?
    } else {
        let krates = query.get_other_vir_crates().map_err(definition_err)?;
        match krates.iter().flat_map(|k| k.functions.iter()).find(|g| &g.x.name == f) {
            Some(g) => g.clone(),
            None => {
                return err_span(
                    span,
                    format!("`unfold({name})`: the body of `{name}` is not available here"),
                );
            }
        }
    };
    if function.x.body.is_none() {
        return err_span(
            span,
            format!("`unfold({name})`: the body of `{name}` is not visible here"),
        );
    }
    if function.x.decrease_when.is_some() {
        return err_span(
            span,
            format!(
                "`unfold({name})`: `{name}` has a `decreases .. when` clause (its body is its value only where that holds); unfolding it into the goal is not supported yet"
            ),
        );
    }
    Ok(function)
}

/// `goal` with each call of `function` replaced by its body, one level (the body's own calls of
/// it stay calls); `count` counts them
fn inline_calls(
    bctx: &BodyCtxt,
    goal: &VExpr,
    function: &Function,
    count: &Cell<usize>,
) -> Result<VExpr, VirErr> {
    let body = function.x.body.as_ref().unwrap();
    let name = fun_name(&function.x.name);
    // only an expression can be put into a goal
    vir::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_, e| match &e.x {
        ExprX::Loop { .. }
        | ExprX::Assign { .. }
        | ExprX::AssertAssume { .. }
        | ExprX::AssertBy { .. }
        | ExprX::AssertQuery { .. }
        | ExprX::AssertCompute(..)
        | ExprX::AirStmt(_)
        | ExprX::OpenInvariant(..)
        | ExprX::Return(_)
        | ExprX::BreakOrContinue { .. }
        | ExprX::Header(_)
        | ExprX::VarAt(..)
        | ExprX::NonSpecClosure { .. }
        | ExprX::ProofInSpec(_)
        | ExprX::Fuel(..)
        | ExprX::RevealString(_)
        | ExprX::RevealByteString(_)
        | ExprX::AssertAssumeUserDefinedTypeInvariant { .. }
        | ExprX::TryOpenAtomicUpdate(..)
        | ExprX::Atomically(..)
        | ExprX::Update(_)
        | ExprX::InvMask(_)
        | ExprX::Ghost { .. }
        | ExprX::BorrowMut(_)
        | ExprX::TwoPhaseBorrowMut(_)
        | ExprX::BorrowMutTracked(_)
        | ExprX::ChargeDeallocations(_)
        | ExprX::Await(_) => Err(vir::messages::error(
            &e.span,
            format!("`unfold({name})`: the body of `{name}` cannot be put into the goal"),
        )),
        _ => Ok(()),
    })?;
    vir::ast_visitor::map_expr_visitor(goal, &|e: &VExpr| match &e.x {
        ExprX::Call {
            target: vir::ast::CallTarget::Fun(vir::ast::CallTargetKind::Static, g, typs, _, _),
            args,
            ..
        } if *g == function.x.name => {
            count.set(count.get() + 1);
            instance(bctx, function, typs, args)
        }
        _ => Ok(e.clone()),
    })
}

/// The body of `function` for the type arguments `typs` and the arguments `args`: its binders
/// renamed apart (so that no argument is captured), then its parameters replaced by the
/// arguments
fn instance(
    bctx: &BodyCtxt,
    function: &Function,
    typs: &vir::ast::Typs,
    args: &vir::ast::Exprs,
) -> Result<VExpr, VirErr> {
    let body = function.x.body.as_ref().unwrap();
    let typ_substs: HashMap<vir::ast::Ident, vir::ast::Typ> =
        function.x.typ_params.iter().cloned().zip(typs.iter().cloned()).collect();
    // (fresh names: a counter for the whole crate)
    let fresh = |x: &VarIdent| vir::def::subst_rename_ident(x, bctx.ctxt.spans.get_next_span_id());
    let rename = |env: &mut HashMap<VarIdent, VarIdent>, x: &VarIdent| -> VarIdent {
        env.entry(x.clone()).or_insert_with(|| fresh(x)).clone()
    };
    let rename_binders = |env: &mut HashMap<VarIdent, VarIdent>,
                          bs: &vir::ast::VarBinders<vir::ast::Typ>|
     -> vir::ast::VarBinders<vir::ast::Typ> {
        Arc::new(
            bs.iter()
                .map(|b| Arc::new(VarBinderX { name: rename(env, &b.name), a: b.a.clone() }))
                .collect(),
        )
    };
    let mut env: HashMap<VarIdent, VarIdent> = HashMap::new();
    for p in function.x.params.iter() {
        rename(&mut env, &p.x.name);
    }
    let renamed = vir::ast_visitor::map_expr_visitor_env(
        body,
        &mut air::scope_map::ScopeMap::new(),
        &mut env,
        &|env, _, e: &VExpr| {
            Ok(match &e.x {
                ExprX::Var(x) => e.new_x(ExprX::Var(rename(env, x))),
                ExprX::Quant(q, bs, b) => {
                    e.new_x(ExprX::Quant(*q, rename_binders(env, bs), b.clone()))
                }
                ExprX::Closure(bs, b) => {
                    e.new_x(ExprX::Closure(rename_binders(env, bs), b.clone()))
                }
                ExprX::Choose { params, cond, body } => e.new_x(ExprX::Choose {
                    params: rename_binders(env, params),
                    cond: cond.clone(),
                    body: body.clone(),
                }),
                ExprX::ReadPlace(p, rk) => e.new_x(ExprX::ReadPlace(
                    p.clone(),
                    UnfinalizedReadKind {
                        preliminary_kind: rk.preliminary_kind.clone(),
                        id: bctx.ctxt.unique_read_kind_id(),
                    },
                )),
                _ => e.clone(),
            })
        },
        &|_, _, s| Ok(vec![s.clone()]),
        &|_, t| {
            Ok(if typ_substs.is_empty() {
                t.clone()
            } else {
                vir::sst_util::subst_typ(&typ_substs, t)
            })
        },
        &|env, _, p| {
            Ok(match &p.x {
                PlaceX::Local(x) => p.new_x(PlaceX::Local(rename(env, x))),
                _ => p.clone(),
            })
        },
        &|env, _, pat| {
            Ok(match &pat.x {
                PatternX::Var(b) => pat.new_x(PatternX::Var(vir::ast::PatternBinding {
                    name: rename(env, &b.name),
                    ..b.clone()
                })),
                PatternX::Binding { binding, sub_pat } => pat.new_x(PatternX::Binding {
                    binding: vir::ast::PatternBinding {
                        name: rename(env, &binding.name),
                        ..binding.clone()
                    },
                    sub_pat: sub_pat.clone(),
                }),
                _ => pat.clone(),
            })
        },
    )?;
    // the parameters (renamed) replaced by the arguments
    let params: HashMap<VarIdent, VExpr> = function
        .x
        .params
        .iter()
        .zip(args.iter())
        .map(|(p, a)| (env[&p.x.name].clone(), a.clone()))
        .collect();
    check_trigger_args(&renamed, &params, &fun_name(&function.x.name))?;
    vir::ast_visitor::map_expr_visitor_env(
        &renamed,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_, _, e: &VExpr| {
            Ok(match &e.x {
                ExprX::Var(x) if params.contains_key(x) => params[x].clone(),
                ExprX::ReadPlace(p, _) => match &p.x {
                    PlaceX::Temporary(a) => a.clone(),
                    _ => e.clone(),
                },
                _ => e.clone(),
            })
        },
        &|_, _, s| Ok(vec![s.clone()]),
        &|_, t| Ok(t.clone()),
        &|_, _, p| {
            Ok(match &p.x {
                PlaceX::Local(x) if params.contains_key(x) => {
                    p.new_x(PlaceX::Temporary(params[x].clone()))
                }
                _ => p.clone(),
            })
        },
        &|_, _, pat| Ok(pat.clone()),
    )
}

/// A parameter used in a trigger of the body cannot take an argument that may not be in a
/// trigger (a closure, a quantifier, a comparison, a boolean operator, an `if`, a `let`): the
/// unfolded goal would be rejected, so say why here
fn check_trigger_args(
    body: &VExpr,
    params: &HashMap<VarIdent, VExpr>,
    name: &str,
) -> Result<(), VirErr> {
    let mut in_triggers: Vec<VarIdent> = vec![];
    let mut collect = |t: &VExpr| {
        let _ = vir::ast_visitor::expr_visitor_check::<VirErr, _>(t, &mut |_, e| {
            match &e.x {
                ExprX::Var(x) if params.contains_key(x) => in_triggers.push(x.clone()),
                ExprX::ReadPlace(p, _) => {
                    if let Some(local) = vir::ast_util::place_get_local(p) {
                        if let PlaceX::Local(x) = &local.x {
                            if params.contains_key(x) {
                                in_triggers.push(x.clone());
                            }
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        });
    };
    vir::ast_visitor::expr_visitor_check::<VirErr, _>(body, &mut |_, e| {
        match &e.x {
            ExprX::Unary(vir::ast::UnaryOp::Trigger(_), t) => collect(t),
            ExprX::WithTriggers { triggers, .. } => {
                for t in triggers.iter().flat_map(|ts| ts.iter()) {
                    collect(t);
                }
            }
            _ => {}
        }
        Ok(())
    })?;
    for x in in_triggers.iter() {
        let arg = &params[x];
        vir::ast_visitor::expr_visitor_check::<VirErr, _>(arg, &mut |_, e| match &e.x {
            ExprX::Closure(..)
            | ExprX::Quant(..)
            | ExprX::Choose { .. }
            | ExprX::If(..)
            | ExprX::Match(..)
            | ExprX::Logical(..)
            | ExprX::Unary(vir::ast::UnaryOp::Not, _)
            | ExprX::Binary(
                vir::ast::BinaryOp::Eq(_)
                | vir::ast::BinaryOp::Ne
                | vir::ast::BinaryOp::Inequality(_)
                | vir::ast::BinaryOp::BoolXor
                | vir::ast::BinaryOp::BoolAndNoSC
                | vir::ast::BinaryOp::BoolOrNoSC,
                ..,
            ) => Err(vir::messages::error(
                &arg.span,
                format!(
                    "`unfold({name})`: this argument is used in a trigger of `{name}`'s body, where it cannot be put (a closure, quantifier, comparison, boolean operator or `if`); bind it to a variable first"
                ),
            )),
            ExprX::Block(stmts, _) if !stmts.is_empty() => Err(vir::messages::error(
                &arg.span,
                format!(
                    "`unfold({name})`: this argument is used in a trigger of `{name}`'s body, where a `let` cannot be put; bind it to a variable first"
                ),
            )),
            _ => Ok(()),
        })?;
    }
    Ok(())
}

/// The parts of a goal for `split`: those of a conjunction, or the branches of an `if`
enum Shape {
    Parts(Vec<VExpr>),
    If(VExpr, VExpr, VExpr),
}

/// The goal without its notes and empty blocks
fn peel(e: &VExpr) -> &VExpr {
    match &e.x {
        ExprX::UnaryOpr(UnaryOpr::ProofNote(_), inner) => peel(inner),
        ExprX::Block(stmts, Some(inner)) if stmts.is_empty() => peel(inner),
        _ => e,
    }
}

/// The source text of an expression (`?` if it has none): through the span context, since the
/// spans of a body from another crate are packed (they have no raw span)
fn source_text(bctx: &BodyCtxt, e: &VExpr) -> String {
    let source_map = bctx.ctxt.tcx.sess.source_map();
    let span = if crate::spans::from_raw_span(&e.span.raw_span).is_some() || e.span.data.len() >= 2
    {
        bctx.ctxt.spans.from_air_span(&e.span, Some(source_map))
    } else {
        None
    };
    span.and_then(|s| source_map.span_to_snippet(s).ok())
        .map(|t| t.split_whitespace().collect::<Vec<_>>().join(" "))
        .unwrap_or_else(|| "?".to_string())
}

/// The text of a goal, by its structure where an `unfold` put a body into it (the text of the
/// whole would show the call), and else by its source text
fn goal_text(bctx: &BodyCtxt, e: &VExpr) -> String {
    match &peel(e).x {
        ExprX::Logical(LogicalOp::And, a, b) => {
            format!("{} && {}", goal_text(bctx, a), goal_text(bctx, b))
        }
        ExprX::Logical(LogicalOp::Or, a, b) => {
            format!("({}) || ({})", goal_text(bctx, a), goal_text(bctx, b))
        }
        ExprX::Logical(LogicalOp::Implies, a, b) => {
            format!("({}) ==> ({})", goal_text(bctx, a), goal_text(bctx, b))
        }
        ExprX::If(c, t, Some(f)) => format!(
            "if {} {{ {} }} else {{ {} }}",
            goal_text(bctx, c),
            goal_text(bctx, t),
            goal_text(bctx, f)
        ),
        _ => {
            let text = source_text(bctx, peel(e));
            if text == "?" { render(bctx, peel(e)) } else { text }
        }
    }
}

/// The text of an expression by its structure, for one without source text (in the body of a
/// function of another crate whose source is not at hand): the common forms, `?` for others
fn render(bctx: &BodyCtxt, e: &VExpr) -> String {
    let sub = |e: &VExpr| {
        let text = source_text(bctx, e);
        if text == "?" { render(bctx, e) } else { text }
    };
    fn place_text(bctx: &BodyCtxt, p: &vir::ast::Place) -> String {
        match &p.x {
            PlaceX::Local(x) => x.0.to_string(),
            PlaceX::Field(f, p) => format!("{}.{}", place_text(bctx, p), f.field),
            PlaceX::Temporary(e) => {
                let text = source_text(bctx, e);
                if text == "?" { render(bctx, e) } else { text }
            }
            _ => "?".to_string(),
        }
    }
    use vir::ast::{ArithOp, BinaryOp, InequalityOp, UnaryOp};
    match &e.x {
        ExprX::Const(Constant::Bool(b)) => b.to_string(),
        ExprX::Const(Constant::Int(i)) => i.to_string(),
        ExprX::Var(x) => x.0.to_string(),
        ExprX::ReadPlace(p, _) => place_text(bctx, p),
        ExprX::UnaryOpr(_, inner) => sub(inner),
        ExprX::Unary(UnaryOp::Not, inner) => format!("!({})", sub(inner)),
        ExprX::Unary(_, inner) => sub(inner),
        ExprX::Block(stmts, Some(inner)) if stmts.is_empty() => sub(inner),
        ExprX::Call { target: vir::ast::CallTarget::Fun(_, f, ..), args, .. } => {
            let args: Vec<String> = args.iter().map(|a| sub(a)).collect();
            format!("{}({})", fun_name(f), args.join(", "))
        }
        ExprX::Logical(op, a, b) => {
            let op = match op {
                LogicalOp::And => "&&",
                LogicalOp::Or => "||",
                LogicalOp::Implies => "==>",
            };
            format!("({}) {} ({})", sub(a), op, sub(b))
        }
        ExprX::Binary(op, a, b) => {
            let op = match op {
                BinaryOp::Eq(_) => "==",
                BinaryOp::Ne => "!=",
                BinaryOp::Inequality(InequalityOp::Le) => "<=",
                BinaryOp::Inequality(InequalityOp::Lt) => "<",
                BinaryOp::Inequality(InequalityOp::Ge) => ">=",
                BinaryOp::Inequality(InequalityOp::Gt) => ">",
                BinaryOp::Arith(ArithOp::Add(_)) => "+",
                BinaryOp::Arith(ArithOp::Sub(_)) => "-",
                BinaryOp::Arith(ArithOp::Mul(_)) => "*",
                _ => "?",
            };
            format!("{} {} {}", sub(a), op, sub(b))
        }
        ExprX::Quant(q, bs, body) => {
            let q = if q.quant == air::ast::Quant::Forall { "forall" } else { "exists" };
            let vars: Vec<String> = bs.iter().map(|b| b.name.0.to_string()).collect();
            format!("{}|{}| {}", q, vars.join(", "), sub(body))
        }
        _ => "?".to_string(),
    }
}

/// `e` without its top-level `#[trigger]` marks (they mean nothing outside their quantifier,
/// and a goal that `intro` took out of a `forall` may have one)
fn untrigger(e: VExpr) -> VExpr {
    fn has_trigger(e: &VExpr) -> bool {
        match &e.x {
            ExprX::Unary(vir::ast::UnaryOp::Trigger(_), _) => true,
            ExprX::UnaryOpr(UnaryOpr::ProofNote(_), inner) => has_trigger(inner),
            ExprX::Block(stmts, Some(inner)) if stmts.is_empty() => has_trigger(inner),
            _ => false,
        }
    }
    if !has_trigger(&e) {
        return e;
    }
    match &e.x {
        ExprX::Unary(vir::ast::UnaryOp::Trigger(_), inner)
        | ExprX::UnaryOpr(UnaryOpr::ProofNote(_), inner)
        | ExprX::Block(_, Some(inner)) => untrigger(inner.clone()),
        _ => e,
    }
}

fn shape(goal: &VExpr) -> Option<Shape> {
    fn conjuncts(e: &VExpr, parts: &mut Vec<VExpr>) {
        match &peel(e).x {
            ExprX::Logical(LogicalOp::And, a, b) => {
                conjuncts(a, parts);
                conjuncts(b, parts);
            }
            _ => parts.push(e.clone()),
        }
    }
    let goal = peel(goal);
    match &goal.x {
        ExprX::Logical(LogicalOp::And, ..) => {
            let mut parts = vec![];
            conjuncts(goal, &mut parts);
            Some(Shape::Parts(parts))
        }
        ExprX::If(c, t, Some(e)) => Some(Shape::If(c.clone(), t.clone(), e.clone())),
        _ => None,
    }
}

fn current_goal<'a>(
    bctx: &'a BodyCtxt,
    span: rustc_span::Span,
    name: &str,
) -> Result<&'a VExpr, VirErr> {
    match &bctx.tactic_goal {
        Some(goal) => Ok(goal),
        None => err_span(
            span,
            format!(
                "`{name}` is a step of a `by(tactic)` script after `unfold`, and is not used directly"
            ),
        ),
    }
}

fn not_split_err<T>(span: rustc_span::Span) -> Result<T, VirErr> {
    err_span(
        span,
        "`split`: after `unfold`, the goal is not a conjunction or an `if` with an `else` (an `<==>` is not split there yet)",
    )
}

/// `tactic_split({ rest })`: each part asserted, with a copy of the rest as its proof
fn split_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    rest: &'tcx Expr<'tcx>,
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let goal = current_goal(bctx, span, "tactic_split")?;
    let Some(shape) = shape(goal) else { return not_split_err(span) };
    // the rest, lowered once (its HIR may be lowered only once) for a placeholder goal, then
    // copied for each part with the part in place of the placeholder
    let placeholder = VarIdent(
        Arc::new("tactic%goal".to_string()),
        VarIdentDisambiguate::VirTemp(bctx.ctxt.spans.get_next_span_id()),
    );
    let placeholder_expr =
        bctx.spanned_typed_new(span, &bool_typ(), ExprX::Var(placeholder.clone()));
    let mut desc = (*bctx.tactic_goal_desc).clone();
    let part_texts: Vec<String> = match &shape {
        Shape::Parts(parts) => {
            parts.iter().map(|p| format!("`{}`", source_text(bctx, p))).collect()
        }
        Shape::If(c, t, e) => vec![
            format!("`{}` (where `{}`)", source_text(bctx, t), source_text(bctx, c)),
            format!("`{}` (where it does not hold)", source_text(bctx, e)),
        ],
    };
    desc.push(format!(
        "(the rest of the script is shared by the parts of the `split` after `unfold`: {})",
        part_texts.join("; ")
    ));
    let rest_bctx = BodyCtxt {
        tactic_goal: Some(placeholder_expr),
        tactic_goal_desc: Arc::new(desc),
        ..bctx.clone()
    };
    let rest = expr_to_vir_consume(&rest_bctx, rest)?;
    let fill = |k: usize, part: &VExpr| -> Result<VExpr, VirErr> {
        let body = if k == 0 { rest.clone() } else { bctx.clone_expr_with_fresh_ids(&rest) };
        let filled = vir::ast_visitor::map_expr_visitor(&body, &|e: &VExpr| match &e.x {
            ExprX::Var(x) if *x == placeholder => Ok(bctx.clone_expr_with_fresh_ids(part)),
            _ => Ok(e.clone()),
        })?;
        vir::ast_visitor::expr_visitor_check::<VirErr, _>(&filled, &mut |_, e| match &e.x {
            ExprX::Var(x) if *x == placeholder => {
                err_span(span, "`split`: internal error: the goal of a part was not filled in")
            }
            _ => Ok(()),
        })?;
        Ok(filled)
    };
    let fresh = |e: &VExpr| bctx.clone_expr_with_fresh_ids(e);
    match shape {
        Shape::Parts(parts) => {
            let n = parts.len();
            let mut stmts = vec![];
            for (k, part) in parts.iter().enumerate() {
                let proof = fill(k, part)?;
                let note = format!(
                    "from the tactic step `split` (part {} of {}, after `unfold`)",
                    k + 1,
                    n
                );
                stmts.push(stmt(
                    bctx,
                    span,
                    assert_by(bctx, span, with_note(fresh(part), note), proof),
                ));
            }
            Ok(ExprX::Block(Arc::new(stmts), None))
        }
        Shape::If(c, t, e) => {
            let then_proof = fill(0, &t)?;
            let else_proof = fill(1, &e)?;
            let then_note = "from the tactic step `split` (the `if` branch, after `unfold`)";
            let else_note = "from the tactic step `split` (the `else` branch, after `unfold`)";
            Ok(ExprX::If(
                fresh(&c),
                assert_by(bctx, span, with_note(fresh(&t), then_note.to_string()), then_proof),
                Some(assert_by(
                    bctx,
                    span,
                    with_note(fresh(&e), else_note.to_string()),
                    else_proof,
                )),
            ))
        }
    }
}

/// `tactic_split_each(({ .. }, { .. }, ..))`: each part asserted, with its own block as its proof
fn split_each_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    blocks: &'tcx Expr<'tcx>,
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let goal = current_goal(bctx, span, "tactic_split_each")?;
    let Some(shape) = shape(goal) else { return not_split_err(span) };
    let ExprKind::Tup(blocks) = &blocks.kind else {
        return err_span(span, "`tactic_split_each`: expected a tuple of blocks");
    };
    let (parts, notes): (Vec<VExpr>, Vec<String>) = match &shape {
        Shape::Parts(parts) => {
            let n = parts.len();
            let notes = (1..=n)
                .map(|k| format!("from the tactic step `split` (part {k} of {n}, after `unfold`)"))
                .collect();
            (parts.clone(), notes)
        }
        Shape::If(_, t, e) => (
            vec![t.clone(), e.clone()],
            vec![
                "from the tactic step `split` (the `if` branch, after `unfold`)".to_string(),
                "from the tactic step `split` (the `else` branch, after `unfold`)".to_string(),
            ],
        ),
    };
    if blocks.len() != parts.len() {
        return err_span(
            span,
            format!(
                "`split`: the goal after `unfold` has {} parts, but {} block{} given",
                parts.len(),
                blocks.len(),
                if blocks.len() == 1 { " is" } else { "s are" }
            ),
        );
    }
    let fresh = |e: &VExpr| bctx.clone_expr_with_fresh_ids(e);
    let mut checks = vec![];
    for ((part, note), block) in parts.iter().zip(notes.into_iter()).zip(blocks.iter()) {
        let part_bctx = BodyCtxt { tactic_goal: Some(fresh(part)), ..bctx.clone() };
        let proof = expr_to_vir_consume(&part_bctx, block)?;
        checks.push(assert_by(bctx, span, with_note(fresh(part), note), proof));
    }
    match shape {
        Shape::Parts(_) => Ok(ExprX::Block(
            Arc::new(checks.into_iter().map(|c| stmt(bctx, span, c)).collect()),
            None,
        )),
        Shape::If(c, ..) => {
            let mut checks = checks.into_iter();
            let then_check = checks.next().unwrap();
            let else_check = checks.next().unwrap();
            Ok(ExprX::If(fresh(&c), then_check, Some(else_check)))
        }
    }
}

/// `tactic_intro({ rest })`: the body of a `forall` (with its variables, unnamed in the script),
/// or the conclusion of an `==>` under its condition, asserted with the rest as its proof
fn intro_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    rest: &'tcx Expr<'tcx>,
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let goal = current_goal(bctx, span, "tactic_intro")?.clone();
    let fresh = |e: &VExpr| bctx.clone_expr_with_fresh_ids(e);
    let note = "from the tactic step `intro` (after `unfold`)".to_string();
    // (for `show()`: what `intro` introduced)
    let lower_rest = |goal: &VExpr, introduced: String| {
        let mut desc = (*bctx.tactic_goal_desc).clone();
        desc.push(introduced);
        let rest_bctx = BodyCtxt {
            tactic_goal: Some(fresh(goal)),
            tactic_goal_desc: Arc::new(desc),
            ..bctx.clone()
        };
        expr_to_vir_consume(&rest_bctx, rest)
    };
    match &peel(&goal).x {
        ExprX::Quant(q, bs, body) if q.quant == air::ast::Quant::Forall => {
            // (the triggers of the `forall` stay with it, on the condition)
            let (triggers, body) = match &peel(body).x {
                ExprX::WithTriggers { triggers, body } => (Some(triggers.clone()), body.clone()),
                _ => (None, body.clone()),
            };
            // (`#![auto]`, `#![all_triggers]`: on the condition too, as for `assert forall`)
            let (annotation, body) = match &peel(&body).x {
                ExprX::Unary(
                    vir::ast::UnaryOp::Trigger(
                        a @ (vir::ast::TriggerAnnotation::AutoTrigger
                        | vir::ast::TriggerAnnotation::AllTriggers),
                    ),
                    inner,
                ) => (Some(a.clone()), inner.clone()),
                _ => (None, body.clone()),
            };
            let (require, ensure) = match &peel(&body).x {
                ExprX::Logical(LogicalOp::Implies, a, b) => (a.clone(), b.clone()),
                _ => (
                    bctx.spanned_typed_new(span, &bool_typ(), ExprX::Const(Constant::Bool(true))),
                    body.clone(),
                ),
            };
            let require = match annotation {
                Some(a) => {
                    require.new_x(ExprX::Unary(vir::ast::UnaryOp::Trigger(a), require.clone()))
                }
                None => require,
            };
            let require = match triggers {
                Some(triggers) => {
                    require.new_x(ExprX::WithTriggers { triggers, body: require.clone() })
                }
                None => require,
            };
            let names: Vec<String> = bs.iter().map(|b| format!("`{}`", b.name.0)).collect();
            let condition = match &peel(&body).x {
                ExprX::Logical(LogicalOp::Implies, a, _) => {
                    format!(", with `{}`", source_text(bctx, a))
                }
                _ => String::new(),
            };
            let introduced = format!("(introduced by `intro`: {}{condition})", names.join(", "));
            let proof = lower_rest(&ensure, introduced)?;
            Ok(ExprX::AssertBy {
                vars: bs.clone(),
                require: fresh(&require),
                ensure: with_note(fresh(&ensure), note),
                proof,
                isolate: None,
            })
        }
        ExprX::Logical(LogicalOp::Implies, a, b) => {
            let introduced = format!("(introduced by `intro`: `{}`)", source_text(bctx, a));
            let proof = lower_rest(b, introduced)?;
            let check = assert_by(bctx, span, with_note(fresh(b), note), proof);
            Ok(ExprX::If(fresh(a), check, None))
        }
        _ => err_span(span, "`intro`: after `unfold`, the goal is not a `forall` or an `==>`"),
    }
}

/// `tactic_show("facts")`: a note with the goal (its text, and what `unfold` put into it) and the
/// facts that the script added (from the macro); nothing is checked
fn show_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    facts: &'tcx Expr<'tcx>,
) -> Result<ExprX, VirErr> {
    let span = expr.span;
    let facts = match &facts.kind {
        ExprKind::Lit(l) => match l.node {
            rustc_ast::LitKind::Str(sym, _) => sym.to_string(),
            _ => return err_span(span, "`tactic_show`: expected a string"),
        },
        _ => return err_span(span, "`tactic_show`: expected a string"),
    };
    let goal = current_goal(bctx, span, "tactic_show")?;
    let placeholder = matches!(&goal.x, ExprX::Var(x) if *x.0 == "tactic%goal");
    let mut msg = if placeholder {
        "tactic: the goal here is each part of the `split` after `unfold`".to_string()
    } else {
        format!("tactic: the goal here is\n    {}", goal_text(bctx, goal))
    };
    for line in bctx.tactic_goal_desc.iter() {
        msg.push_str("\n");
        msg.push_str(line);
    }
    if facts.is_empty() {
        msg.push_str("\nthe script has added no facts before this step");
    } else {
        msg.push_str("\nfacts that the script added before this step:");
        for fact in facts.lines() {
            msg.push_str("\n    ");
            msg.push_str(fact);
        }
    }
    msg.push_str(
        "\n(nothing here has been checked yet, and the facts of the context, such as `requires` and the statements before the assertion, are not listed)",
    );
    let vspan = bctx.ctxt.spans.to_air_span(span);
    bctx.ctxt
        .diagnostics
        .borrow_mut()
        .push(vir::ast::VirErrAs::Note(vir::messages::note(&vspan, msg)));
    Ok(ExprX::Block(Arc::new(vec![]), None))
}
