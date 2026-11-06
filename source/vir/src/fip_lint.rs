//! `-V fip-lint`: suggestions for recursion that could use constant stack space
//! (`#[verifier::fip(strict)]`). This module finds tail recursion modulo a constructor (TRMC):
//! a recursive call whose result becomes a field of a constructor (possibly inside `Box::new` or
//! `Some`) that the function returns. Such a call is not a tail call, so the recursion grows the
//! stack, but it can be written as a loop that writes each constructed value into a hole (a
//! `&mut` place) and moves the hole into the new value (destination-passing style; Leijen and
//! Lorenzen, "Tail Recursion Modulo Context"). The calls in tail position that are not tail calls
//! are found on the MIR by rust_verify (`fip_mir`), which knows the drops that follow them.

use crate::ast::{CallTarget, CallTargetKind, Expr, ExprX, Fun, Function, Krate, Mode, StmtX};
use crate::messages::{Message, Span, warning};
use std::collections::{HashMap, HashSet};

/// The static exec callees of `body` (statically resolved trait calls included)
fn callees(body: &Expr) -> HashSet<Fun> {
    let mut out = HashSet::new();
    let _ = crate::ast_visitor::expr_visitor_check::<(), _>(body, &mut |_scope, e| {
        if let ExprX::Call { target: CallTarget::Fun(kind, fun, _, _, _), .. } = &e.x {
            match kind {
                CallTargetKind::DynamicResolved { resolved, .. } => {
                    out.insert(resolved.clone());
                }
                _ => {
                    out.insert(fun.clone());
                }
            }
        }
        Ok(())
    });
    out
}

fn reaches(graph: &HashMap<Fun, HashSet<Fun>>, from: &Fun, to: &Fun) -> bool {
    let mut seen: HashSet<Fun> = HashSet::new();
    let mut work = vec![from.clone()];
    while let Some(f) = work.pop() {
        if &f == to {
            return true;
        }
        if !seen.insert(f.clone()) {
            continue;
        }
        if let Some(cs) = graph.get(&f) {
            work.extend(cs.iter().cloned());
        }
    }
    false
}

fn call_fun(e: &Expr) -> Option<&Fun> {
    match &e.x {
        ExprX::Call { target: CallTarget::Fun(kind, fun, _, _, _), .. } => match kind {
            CallTargetKind::DynamicResolved { resolved, .. } => Some(resolved),
            _ => Some(fun),
        },
        _ => None,
    }
}

fn is_box_new(f: &Fun) -> bool {
    let name = crate::ast_util::fun_as_friendly_rust_name(f);
    name == "alloc::boxed::Box::new"
        || name.starts_with("alloc::boxed::impl") && name.ends_with("::new")
}

/// Recursive calls inside the fields of the constructor `ctor` (through `Box::new` and nested
/// constructors), with the span of the constructor
fn calls_in_fields<'a>(e: &'a Expr, is_rec: &dyn Fn(&Fun) -> bool, out: &mut Vec<&'a Expr>) {
    match &e.x {
        ExprX::Ctor(_, _, fields, _) => {
            for f in fields.iter() {
                calls_in_fields(&f.a, is_rec, out);
            }
        }
        ExprX::Call { args, .. } => {
            if let Some(f) = call_fun(e) {
                if is_rec(f) {
                    out.push(e);
                } else if is_box_new(f) {
                    for a in args.iter() {
                        calls_in_fields(a, is_rec, out);
                    }
                }
            }
        }
        _ => {}
    }
}

/// The tail positions of an expression
fn tail_exprs<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &e.x {
        ExprX::Block(stmts, last) => {
            if let Some(last) = last {
                tail_exprs(last, out);
            } else if let Some(s) = stmts.last() {
                if let StmtX::Expr(e) = &s.x {
                    tail_exprs(e, out);
                }
            }
            // (`return e` anywhere in the block is a tail position too)
            for s in stmts.iter() {
                if let StmtX::Expr(e) = &s.x {
                    if let ExprX::Return(Some(r)) = &e.x {
                        tail_exprs(r, out);
                    }
                }
            }
        }
        ExprX::If(_, t, f) => {
            tail_exprs(t, out);
            if let Some(f) = f {
                tail_exprs(f, out);
            }
        }
        ExprX::Match(_, arms, _) => {
            for arm in arms.iter() {
                tail_exprs(&arm.x.body, out);
            }
        }
        ExprX::Return(Some(r)) => tail_exprs(r, out),
        _ => out.push(e),
    }
}

/// TRMC suggestions for the exec functions of the crate being verified
pub fn lint_krate(krate: &Krate) -> Vec<Message> {
    let mut graph: HashMap<Fun, HashSet<Fun>> = HashMap::new();
    let exec_with_body: Vec<&Function> =
        krate.functions.iter().filter(|f| f.x.mode == Mode::Exec && f.x.body.is_some()).collect();
    for f in exec_with_body.iter() {
        graph.insert(f.x.name.clone(), callees(f.x.body.as_ref().unwrap()));
    }
    let mut msgs = Vec::new();
    for f in exec_with_body.iter() {
        let name = &f.x.name;
        let is_rec = |g: &Fun| reaches(&graph, g, name);
        let mut tails = Vec::new();
        tail_exprs(f.x.body.as_ref().unwrap(), &mut tails);
        let mut seen_spans: HashSet<String> = HashSet::new();
        for t in tails {
            if !matches!(&t.x, ExprX::Ctor(..)) && !call_fun(t).is_some_and(|g| is_box_new(g)) {
                continue;
            }
            let mut calls = Vec::new();
            calls_in_fields(t, &is_rec, &mut calls);
            for c in calls {
                let key = format!("{:?}", c.span.as_string);
                if !seen_spans.insert(key) {
                    continue;
                }
                let callee = call_fun(c).map(crate::ast_util::fun_as_friendly_rust_name);
                msgs.push(trmc_message(&c.span, &t.span, callee.unwrap_or_default()));
            }
        }
    }
    msgs
}

fn trmc_message(call: &Span, ctor: &Span, callee: String) -> Message {
    warning(
        call,
        format!(
            "-V fip-lint: this recursive call of `{}` is not a tail call: its result becomes a field of the value built here, so the recursion grows the stack (tail recursion modulo a constructor). A loop can build the same value in constant stack space: keep a `&mut` hole (the field that is still to be filled), build each value with that field empty, store it into the hole, and move the hole into its field (destination-passing style, as in Leijen and Lorenzen's \"Tail Recursion Modulo Context\")",
            callee
        ),
    )
    .secondary_label(ctor, "the value that the result becomes a part of")
}
