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

// ---------------------------------------------------------------------------------------------
// TRMC rewriting plans (`-V fip-lint=fix`, and the suggestion attached to the TRMC warning)
//
// The rewrite itself is done on the source text by rust_verify, which has the source map. This
// part finds what to rewrite: a strongly connected component of the call graph (direct or mutual
// recursion) in which every recursive call is either a tail call or a call whose result is
// directly a field of a constructor in tail position (through `Box::new` and nested
// constructors). The function bodies become one loop that keeps a `&mut` hole: each constructor
// is written into the hole with a placeholder where the recursive result goes, and the hole moves
// to that field (Leijen and Lorenzen, "Tail Recursion Modulo Context").

use crate::ast::{CtorPrintStyle, Datatype, Dt, FunctionKind, Ident, Path, TypX};
use crate::ast_visitor::{VisitorControlFlow, VisitorScopeMap};
use std::sync::Arc;

/// One step from a constructor in tail position down to the recursive call
#[derive(Clone, Debug)]
pub enum TrmcLevel {
    /// `Box::new(_)`
    Box,
    /// A constructor, with the hole in field `hole`. The other fields are given in the order in
    /// which they appear (and are evaluated) in the source.
    Ctor {
        dt: Path,
        variant: Ident,
        style: CtorPrintStyle,
        before: Vec<(Ident, Span)>,
        hole: Ident,
        after: Vec<(Ident, Span)>,
    },
}

/// A recursive call in tail position, possibly inside a constructor
#[derive(Clone, Debug)]
pub struct TrmcSite {
    /// The source to replace (the call, the constructor, or `return`/`become` with either)
    pub span: Span,
    /// The constructor (or, for a tail call, the call) itself
    pub expr: Span,
    pub callee: Fun,
    pub args: Vec<Span>,
    /// Empty for a tail call
    pub levels: Vec<TrmcLevel>,
}

#[derive(Clone, Debug)]
pub struct TrmcFn {
    pub function: Function,
    pub sites: Vec<TrmcSite>,
    /// `return e` that is not a site: (span of the whole `return e`, span of `e`). (The source
    /// text is checked by rust_verify: a `?` is also a return.)
    pub returns: Vec<(Span, Span)>,
    /// A variant without fields of the return type, used as a placeholder for the hole
    pub placeholder: (Path, Ident),
}

/// The functions of one strongly connected component, in source order
#[derive(Clone, Debug)]
pub struct TrmcPlan {
    pub fns: Vec<TrmcFn>,
}

/// Why a component with a TRMC call cannot be rewritten
#[derive(Clone, Debug)]
pub struct TrmcBlocked {
    pub span: Span,
    pub reason: String,
}

fn exec_graph(krate: &Krate) -> (HashMap<Fun, HashSet<Fun>>, HashMap<Fun, Function>) {
    let mut graph: HashMap<Fun, HashSet<Fun>> = HashMap::new();
    let mut funs: HashMap<Fun, Function> = HashMap::new();
    for f in krate.functions.iter() {
        if f.x.mode == Mode::Exec && f.x.body.is_some() {
            graph.insert(f.x.name.clone(), callees(f.x.body.as_ref().unwrap()));
            funs.insert(f.x.name.clone(), f.clone());
        }
    }
    (graph, funs)
}

/// Strongly connected components (Tarjan), each sorted by span
fn sccs(graph: &HashMap<Fun, HashSet<Fun>>, order: &Vec<Fun>) -> Vec<Vec<Fun>> {
    struct St<'a> {
        graph: &'a HashMap<Fun, HashSet<Fun>>,
        index: HashMap<Fun, usize>,
        low: HashMap<Fun, usize>,
        on_stack: HashSet<Fun>,
        stack: Vec<Fun>,
        next: usize,
        out: Vec<Vec<Fun>>,
    }
    fn visit(st: &mut St, v: &Fun) {
        st.index.insert(v.clone(), st.next);
        st.low.insert(v.clone(), st.next);
        st.next += 1;
        st.stack.push(v.clone());
        st.on_stack.insert(v.clone());
        let succs: Vec<Fun> = match st.graph.get(v) {
            Some(s) => s.iter().filter(|w| st.graph.contains_key(*w)).cloned().collect(),
            None => vec![],
        };
        for w in succs.iter() {
            if !st.index.contains_key(w) {
                visit(st, w);
                let lw = st.low[w];
                let lv = st.low[v];
                st.low.insert(v.clone(), lv.min(lw));
            } else if st.on_stack.contains(w) {
                let iw = st.index[w];
                let lv = st.low[v];
                st.low.insert(v.clone(), lv.min(iw));
            }
        }
        if st.low[v] == st.index[v] {
            let mut comp = Vec::new();
            loop {
                let w = st.stack.pop().unwrap();
                st.on_stack.remove(&w);
                let done = &w == v;
                comp.push(w);
                if done {
                    break;
                }
            }
            st.out.push(comp);
        }
    }
    let mut st = St {
        graph,
        index: HashMap::new(),
        low: HashMap::new(),
        on_stack: HashSet::new(),
        stack: Vec::new(),
        next: 0,
        out: Vec::new(),
    };
    for v in order.iter() {
        if !st.index.contains_key(v) {
            visit(&mut st, v);
        }
    }
    st.out
}

/// The tail positions of a body: its value and the operands of all `return`s (outside closures).
/// Each comes with the span to replace when it is rewritten (the `return` itself, if any).
fn body_tails(body: &Expr) -> Vec<(Span, Expr)> {
    let mut out: Vec<(Span, Expr)> = Vec::new();
    let mut tails = Vec::new();
    tail_exprs(body, &mut tails);
    for t in tails {
        out.push((t.span.clone(), t.clone()));
    }
    let mut map: VisitorScopeMap = air::scope_map::ScopeMap::new();
    let _ = crate::ast_visitor::expr_visitor_dfs::<(), _>(body, &mut map, &mut |_, e| {
        match &e.x {
            ExprX::Closure(..) | ExprX::NonSpecClosure { .. } => VisitorControlFlow::Return,
            ExprX::Return(Some(r)) => {
                let mut ts = Vec::new();
                tail_exprs(r, &mut ts);
                for t in ts {
                    // `return site` is replaced as a whole
                    let span = if Arc::ptr_eq(t, r) { e.span.clone() } else { t.span.clone() };
                    out.push((span, t.clone()));
                }
                VisitorControlFlow::Recurse
            }
            _ => VisitorControlFlow::Recurse,
        }
    });
    out
}

/// All calls in `body` (closures included) whose callee is in `scc`
fn calls_into(body: &Expr, scc: &HashSet<Fun>) -> Vec<Expr> {
    let mut out = Vec::new();
    let _ = crate::ast_visitor::expr_visitor_check::<(), _>(body, &mut |_, e| {
        if let Some(f) = call_fun(e) {
            if scc.contains(f) {
                out.push(e.clone());
            }
        }
        Ok(())
    });
    out
}

/// If `e` is a constructor in tail position with exactly one call into `scc` on its path, the
/// levels from `e` down to that call
fn ctor_site(e: &Expr, scc: &HashSet<Fun>) -> Option<(Vec<TrmcLevel>, Expr)> {
    match &e.x {
        ExprX::Ctor(Dt::Path(dt), variant, binders, None) => {
            let mut found: Option<(usize, Vec<TrmcLevel>, Expr)> = None;
            for (i, b) in binders.iter().enumerate() {
                if let Some(f) = call_fun(&b.a) {
                    if scc.contains(f) {
                        if found.is_some() {
                            return None;
                        }
                        found = Some((i, vec![], b.a.clone()));
                        continue;
                    }
                }
                if let Some((levels, call)) = ctor_site(&b.a, scc) {
                    if found.is_some() {
                        return None;
                    }
                    found = Some((i, levels, call));
                }
            }
            let (i, inner, call) = found?;
            let style = CtorPrintStyle::Parens; // filled in by trmc_plans from the datatype
            let mut levels = vec![TrmcLevel::Ctor {
                dt: dt.clone(),
                variant: variant.clone(),
                style,
                before: binders[..i].iter().map(|b| (b.name.clone(), b.a.span.clone())).collect(),
                hole: binders[i].name.clone(),
                after: binders[i + 1..]
                    .iter()
                    .map(|b| (b.name.clone(), b.a.span.clone()))
                    .collect(),
            }];
            levels.extend(inner);
            Some((levels, call))
        }
        ExprX::Call { args, .. } if args.len() == 1 && call_fun(e).is_some_and(is_box_new) => {
            let a = &args[0];
            if let Some(f) = call_fun(a) {
                if scc.contains(f) {
                    return Some((vec![TrmcLevel::Box], a.clone()));
                }
            }
            let (inner, call) = ctor_site(a, scc)?;
            let mut levels = vec![TrmcLevel::Box];
            levels.extend(inner);
            Some((levels, call))
        }
        _ => None,
    }
}

fn call_args(e: &Expr) -> Vec<Span> {
    match &e.x {
        ExprX::Call { args, .. } => args.iter().map(|a| a.span.clone()).collect(),
        _ => vec![],
    }
}

fn typ_has_mut_ref(t: &crate::ast::Typ) -> bool {
    let mut found = false;
    let _ = crate::ast_visitor::typ_visitor_check::<(), _>(t, &mut |t| {
        if matches!(&**t, TypX::MutRef(_)) {
            found = true;
        }
        Ok(())
    });
    found
}

fn placeholder_variant(
    datatypes: &HashMap<Path, Datatype>,
    typ: &crate::ast::Typ,
) -> Option<(Path, Ident)> {
    match &**typ {
        TypX::Datatype(Dt::Path(p), _, _) => {
            let d = datatypes.get(p)?;
            let v = d.x.variants.iter().find(|v| v.fields.is_empty())?;
            Some((p.clone(), v.name.clone()))
        }
        TypX::Decorate(_, _, t) => placeholder_variant(datatypes, t),
        _ => None,
    }
}

/// Rewriting plans for the components that contain a TRMC call, or why each cannot be rewritten.
/// `is_local` says which functions belong to the crate being verified (only those are rewritten).
pub fn trmc_plans(
    krate: &Krate,
    is_local: &dyn Fn(&Fun) -> bool,
) -> Vec<Result<TrmcPlan, TrmcBlocked>> {
    let (graph, funs) = exec_graph(krate);
    let datatypes: HashMap<Path, Datatype> = krate
        .datatypes
        .iter()
        .filter_map(|d| match &d.x.name {
            Dt::Path(p) => Some((p.clone(), d.clone())),
            Dt::Tuple(_) => None,
        })
        .collect();
    let order: Vec<Fun> = krate
        .functions
        .iter()
        .filter(|f| graph.contains_key(&f.x.name) && is_local(&f.x.name))
        .map(|f| f.x.name.clone())
        .collect();
    let mut results = Vec::new();
    for comp in sccs(&graph, &order) {
        if !comp.iter().all(|f| is_local(f)) {
            continue;
        }
        let scc: HashSet<Fun> = comp.iter().cloned().collect();
        let is_recursive = comp.len() > 1 || graph[&comp[0]].contains(&comp[0]);
        if !is_recursive {
            continue;
        }
        let mut members: Vec<Function> = comp.iter().map(|f| funs[f].clone()).collect();
        members.sort_by_key(|f| (f.span.as_string.clone(), f.x.name.clone()));
        // order by position in the source when the spans are comparable (same file)
        members.sort_by(|a, b| a.span.data.cmp(&b.span.data));

        let mut fns = Vec::new();
        let mut blocked: Option<TrmcBlocked> = None;
        let mut any_ctor_site = false;
        let mut block = |span: &Span, reason: String| {
            if blocked.is_none() {
                blocked = Some(TrmcBlocked { span: span.clone(), reason });
            }
        };
        for f in members.iter() {
            let body = f.x.body.as_ref().unwrap();
            let mut sites: Vec<TrmcSite> = Vec::new();
            let mut site_calls: Vec<Span> = Vec::new();
            let mut tail_spans: HashSet<String> = HashSet::new();
            for (span, t) in body_tails(body) {
                if !tail_spans.insert(format!("{:?}", span.data)) {
                    continue;
                }
                if let Some(g) = call_fun(&t) {
                    if scc.contains(g) {
                        site_calls.push(t.span.clone());
                        sites.push(TrmcSite {
                            span,
                            expr: t.span.clone(),
                            callee: g.clone(),
                            args: call_args(&t),
                            levels: vec![],
                        });
                        continue;
                    }
                }
                if let Some((mut levels, call)) = ctor_site(&t, &scc) {
                    for l in levels.iter_mut() {
                        if let TrmcLevel::Ctor { dt, variant, style, .. } = l {
                            let d = datatypes.get(dt);
                            match d.and_then(|d| d.x.variants.iter().find(|v| &v.name == variant)) {
                                Some(v) => *style = v.ctor_style,
                                None => block(
                                    &t.span,
                                    "the constructor's datatype is not known to Verus".into(),
                                ),
                            }
                        }
                    }
                    any_ctor_site = true;
                    site_calls.push(call.span.clone());
                    sites.push(TrmcSite {
                        span,
                        expr: t.span.clone(),
                        callee: call_fun(&call).unwrap().clone(),
                        args: call_args(&call),
                        levels,
                    });
                }
            }
            for c in calls_into(body, &scc) {
                if !site_calls
                    .iter()
                    .any(|s| s.data == c.span.data && s.as_string == c.span.as_string)
                {
                    block(
                        &c.span,
                        format!(
                            "this recursive call of `{}` is neither a tail call nor the only recursive call inside a constructor in tail position",
                            call_fun(&c)
                                .map(crate::ast_util::fun_as_friendly_rust_name)
                                .unwrap_or_default()
                        ),
                    );
                }
            }
            if !matches!(f.x.kind, FunctionKind::Static) {
                block(&f.span, "only free functions are rewritten (not trait methods)".into());
            }
            for p in f.x.params.iter() {
                if p.x.mode != Mode::Exec || p.x.unwrapped_info.is_some() {
                    block(&p.span, "only exec parameters are supported".into());
                }
                if typ_has_mut_ref(&p.x.typ) {
                    block(&p.span, "`&mut` parameters are not supported".into());
                }
            }
            if f.x.decrease.is_empty() {
                block(
                    &f.span,
                    "the function needs a `decreases` clause (it becomes the loop's)".into(),
                );
            }
            if f.x.returns.is_some() {
                block(&f.span, "`returns` clauses are not supported (use `ensures`)".into());
            }
            if !f.x.ensure.1.is_empty() {
                block(&f.span, "trait-default `ensures` are not supported".into());
            }
            let placeholder = match placeholder_variant(&datatypes, &f.x.outer_ret.x.typ) {
                Some(p) => p,
                None => {
                    block(
                        &f.span,
                        "the return type must be an enum with a variant without fields (used as a placeholder while the value is built)".into(),
                    );
                    continue;
                }
            };
            let mut returns = Vec::new();
            let site_spans: Vec<Span> = sites.iter().map(|s| s.span.clone()).collect();
            let mut map: VisitorScopeMap = air::scope_map::ScopeMap::new();
            let _ =
                crate::ast_visitor::expr_visitor_dfs::<(), _>(
                    body,
                    &mut map,
                    &mut |_, e| match &e.x {
                        ExprX::Closure(..) | ExprX::NonSpecClosure { .. } => {
                            VisitorControlFlow::Return
                        }
                        ExprX::Return(r) => {
                            if !site_spans.iter().any(|s| s.data == e.span.data) {
                                match r {
                                    Some(r) => returns.push((e.span.clone(), r.span.clone())),
                                    None => returns.push((e.span.clone(), e.span.clone())),
                                }
                            }
                            VisitorControlFlow::Recurse
                        }
                        _ => VisitorControlFlow::Recurse,
                    },
                );
            fns.push(TrmcFn { function: f.clone(), sites, returns, placeholder });
        }
        if !any_ctor_site {
            continue;
        }
        if members.len() > 1 {
            let n_dec = members[0].x.decrease.len();
            if members.iter().any(|f| f.x.decrease.len() != n_dec || f.x.decrease.len() != 1) {
                block(
                    &members[0].span,
                    "mutually recursive functions need one `decreases` expression each (they become one loop's measure)".into(),
                );
            }
            if members.iter().any(|f| f.x.allocates.is_some() != members[0].x.allocates.is_some()) {
                block(
                    &members[0].span,
                    "either all or none of the mutually recursive functions must have `allocates`"
                        .into(),
                );
            }
        }
        results.push(match blocked {
            Some(b) => Err(b),
            None => Ok(TrmcPlan { fns }),
        });
    }
    results
}
