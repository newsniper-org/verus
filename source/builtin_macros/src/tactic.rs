//! `assert(P) by(tactic) { step(); .. }`: a tactic script, expanded into ordinary proof code
//! before the rest of `verus!` sees it, so the expansion is then checked like any other proof.
//!
//! The expansion is not trusted. It produces `assert(P) by { .. }`, whose block ends with `P`
//! being asserted, and every assertion a step makes is checked where it is made. A step changes
//! how `P` is proved, never what is proved. Statements that are not steps pass through as they
//! are, so a script may mix steps with ordinary proof code (`assert(..)`, lemma calls, `let`).
//!
//! The steps work on the current goal, starting with `P`:
//!
//! - `have(Q)`: `assert(Q);`, and `Q` is a fact for the rest of the script.
//! - `split()`: for a goal `A && B` (or `&&& A &&& B`), `A <==> B`, or `if c { A } else { B }`,
//!   prove each part on its own (`assert(A) by { .. }`, ..., or an `if` with the part asserted in
//!   each branch). The steps after `split()` apply to each part. `split({ .. }, { .. })` gives
//!   each part its own steps instead, one block per part.
//! - `intro()`: for a goal `forall|x| A ==> B`, `assert forall|x| A implies B by { .. }`; for
//!   `forall|x| B`, `assert forall|x| B by { .. }`; for `A ==> B`, `if A { assert(B) by { .. } }`.
//!   The steps after `intro()` prove the new goal `B`.
//! - `cases(b)`: `if b { .. } else { .. }`, with the goal asserted in both branches and the steps
//!   after `cases(b)` in each. `cases(b, { .. }, { .. })` gives each branch its own steps.
//!   `cases(match e { Pat => { .. }, .. })`: a `match`, with the goal asserted in every arm and
//!   the arm's block as the steps for it.
//! - `unfold(f)`: `reveal(f);` `unfold(f, k)`: `reveal_with_fuel(f, k);`
//! - `apply(L(a))`: the call `L(a);`, whose `ensures` are facts for the rest of the script.
//! - `inst(forall|x: T| Q, t)`: `assert(forall|x: T| Q); assert({ let x: T = t; Q });`, which gives
//!   the solver the instance at `t` (one term for each bound variable).
//! - `smt()`, `smt(nonlinear_arith, R..)`, `smt(bit_vector, R..)`, `compute()`: prove the goal now,
//!   with `assert(G);`, `assert(G) by(nonlinear_arith) requires R..;`, `assert(G) by(bit_vector)
//!   requires R..;` or `assert(G) by(compute);`. No steps may follow.
//! - `show()`: a note with the current goal and the facts that the script added before it. The
//!   facts of the context (`requires`, earlier statements) also hold but are not listed.
//!
//! Step names are recognized only as bare names called at the top of a script (a function of
//! the same name can still be called with a path, such as `self::split()`).

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{ToTokens, quote_spanned};
use std::convert::TryFrom;
use verus_syn::spanned::Spanned;
use verus_syn::{Assert, BinOp, Block, Error, Expr, ExprCall, ExprMatch, Pat, Stmt, UnOp};

const STEP_NAMES: &[&str] = &[
    "have", "split", "intro", "cases", "unfold", "apply", "inst", "smt", "compute", "show",
    "isolate",
];

type Result<T> = std::result::Result<T, Error>;

enum Item {
    Stmt(Stmt),
    Step(Step),
}

struct Step {
    span: Span,
    kind: StepKind,
}

enum StepKind {
    Have(Expr),
    Split(Vec<Vec<Item>>),
    Intro,
    Cases(Expr, Option<(Vec<Item>, Vec<Item>)>),
    CasesMatch(ExprMatch, Vec<Vec<Item>>),
    Unfold(Expr, Option<Expr>),
    Apply(Expr),
    Inst(Expr, Vec<Expr>),
    Smt(Option<verus_syn::Ident>, Vec<Expr>),
    Compute,
    Show,
    /// the options of `#[verus::internal(isolate(..))]`, such as `rlimit(30)`
    Isolate(TokenStream),
}

impl StepKind {
    fn closes_goal(&self) -> bool {
        matches!(self, StepKind::Smt(..) | StepKind::Compute)
    }
}

/// The facts that the script added so far, for `show()`.
#[derive(Clone, Default)]
struct Facts(Vec<String>);

impl Facts {
    fn with(&self, fact: String) -> Facts {
        let mut facts = self.clone();
        facts.0.push(fact);
        facts
    }
}

/// Expand `assert(P) by(tactic) { .. }` into `assert(P) by { .. }`. `mark` wraps the generated
/// block so that the rest of Verus knows it came from a tactic script.
pub(crate) fn expand_tactic_assert(
    assert: Assert,
    mark: impl FnOnce(Block) -> Block,
) -> Result<Expr> {
    expand(assert, mark)
}

fn expand(assert: Assert, mark: impl FnOnce(Block) -> Block) -> Result<Expr> {
    let prover_span =
        assert.prover.as_ref().map(|(p, _)| p.span.join()).unwrap_or(Span::call_site());
    if let Some(requires) = &assert.requires {
        return Err(Error::new(
            requires.token.span,
            "`by(tactic)` does not take a `requires` clause (for `by(nonlinear_arith)` or `by(bit_vector)` with `requires`, use the step `smt(nonlinear_arith, ..)` or `smt(bit_vector, ..)`)",
        ));
    }
    let Some(body) = assert.body else {
        return Err(Error::new(
            prover_span,
            "`by(tactic)` needs a block with the steps: `assert(P) by(tactic) { .. }`",
        ));
    };
    let brace_token = body.brace_token;
    let script = parse_script(*body)?;
    let stmts = expand_items(&assert.expr, &script, &Facts::default())?;
    Ok(Expr::Assert(Assert {
        attrs: assert.attrs,
        assert_token: assert.assert_token,
        paren_token: assert.paren_token,
        expr: assert.expr,
        by_token: assert.by_token,
        prover: None,
        requires: None,
        body: Some(Box::new(mark(Block { brace_token, stmts }))),
    }))
}

fn parse_script(block: Block) -> Result<Vec<Item>> {
    block.stmts.into_iter().map(parse_item).collect()
}

fn parse_item(stmt: Stmt) -> Result<Item> {
    if let Stmt::Expr(Expr::Call(call), _) = &stmt {
        if let Some(name) = step_name(&call.func) {
            return Ok(Item::Step(parse_step(name, call.clone())?));
        }
    }
    Ok(Item::Stmt(stmt))
}

fn step_name(func: &Expr) -> Option<verus_syn::Ident> {
    let Expr::Path(path) = func else { return None };
    if path.qself.is_some() || path.path.leading_colon.is_some() || path.path.segments.len() != 1 {
        return None;
    }
    let segment = &path.path.segments[0];
    if !segment.arguments.is_none() {
        return None;
    }
    STEP_NAMES.contains(&segment.ident.to_string().as_str()).then(|| segment.ident.clone())
}

/// A block given to a step as an argument (`split({ .. }, { .. })`): its statements are a script.
fn block_script(expr: &Expr, what: &str) -> Result<Vec<Item>> {
    match expr {
        Expr::Block(block) if block.label.is_none() => parse_script(block.block.clone()),
        _ => Err(Error::new(expr.span(), format!("expected a block with the steps for {}", what))),
    }
}

fn parse_step(name: verus_syn::Ident, call: ExprCall) -> Result<Step> {
    let span = name.span();
    let args: Vec<Expr> = call.args.into_iter().collect();
    let n = args.len();
    let wrong_args = |usage: &str| Err(Error::new(span, format!("expected {}", usage)));
    let kind = match name.to_string().as_str() {
        "have" => match <[Expr; 1]>::try_from(args) {
            Ok([q]) => StepKind::Have(q),
            Err(_) => return wrong_args("`have(Q)`"),
        },
        "split" => StepKind::Split(
            args.iter()
                .enumerate()
                .map(|(i, a)| block_script(a, &format!("part {} of the split", i + 1)))
                .collect::<Result<_>>()?,
        ),
        "intro" if n == 0 => StepKind::Intro,
        "intro" => return wrong_args("`intro()`"),
        "cases" => match n {
            1 => match args.into_iter().next().unwrap() {
                Expr::Match(m) => {
                    let scripts = m
                        .arms
                        .iter()
                        .map(|arm| match &*arm.body {
                            Expr::Block(b) if b.label.is_none() => parse_script(b.block.clone()),
                            body => Ok(vec![parse_item(Stmt::Expr(body.clone(), None))?]),
                        })
                        .collect::<Result<_>>()?;
                    StepKind::CasesMatch(m, scripts)
                }
                b => StepKind::Cases(b, None),
            },
            3 => {
                let mut args = args.into_iter();
                let b = args.next().unwrap();
                let then_script = block_script(&args.next().unwrap(), "the case where it holds")?;
                let else_script =
                    block_script(&args.next().unwrap(), "the case where it does not hold")?;
                StepKind::Cases(b, Some((then_script, else_script)))
            }
            _ => {
                return wrong_args(
                    "`cases(b)`, `cases(b, { .. }, { .. })` or `cases(match e { .. })`",
                );
            }
        },
        "unfold" => match n {
            1 | 2 => {
                let mut args = args.into_iter();
                let f = args.next().unwrap();
                if !matches!(f, Expr::Path(_)) {
                    return Err(Error::new(f.span(), "`unfold`: expected the name of a function"));
                }
                StepKind::Unfold(f, args.next())
            }
            _ => return wrong_args("`unfold(f)` or `unfold(f, fuel)`"),
        },
        "apply" => match <[Expr; 1]>::try_from(args) {
            Ok([e]) => StepKind::Apply(e),
            Err(_) => return wrong_args("`apply(lemma(args))`"),
        },
        "inst" => {
            if n < 2 {
                return wrong_args(
                    "`inst(forall|x: T| Q, t)`, with a term for each bound variable",
                );
            }
            let mut args = args.into_iter();
            let fact = args.next().unwrap();
            let terms: Vec<Expr> = args.collect();
            let Some((inputs, _, _)) = as_forall(&fact) else {
                return Err(Error::new(fact.span(), "`inst`: expected a `forall` fact"));
            };
            if inputs.len() != terms.len() {
                return Err(Error::new(
                    span,
                    format!(
                        "`inst`: the fact binds {} variable{}, but {} term{} given",
                        inputs.len(),
                        if inputs.len() == 1 { "" } else { "s" },
                        terms.len(),
                        if terms.len() == 1 { " is" } else { "s are" },
                    ),
                ));
            }
            StepKind::Inst(fact, terms)
        }
        "smt" => {
            let mut args = args.into_iter();
            match args.next() {
                None => StepKind::Smt(None, vec![]),
                Some(Expr::Path(p))
                    if p.path
                        .get_ident()
                        .map_or(false, |i| i == "nonlinear_arith" || i == "bit_vector") =>
                {
                    StepKind::Smt(p.path.get_ident().cloned(), args.collect())
                }
                Some(e) => {
                    return Err(Error::new(
                        e.span(),
                        "`smt`: expected `smt()`, `smt(nonlinear_arith, ..)` or `smt(bit_vector, ..)`",
                    ));
                }
            }
        }
        "compute" if n == 0 => StepKind::Compute,
        "compute" => return wrong_args("`compute()`"),
        "show" if n == 0 => StepKind::Show,
        "show" => return wrong_args("`show()`"),
        "isolate" => {
            let mut options: Vec<TokenStream> = Vec::new();
            let (mut rlimit, mut backend) = (false, false);
            for arg in args.iter() {
                let expected = || {
                    Error::new(
                        arg.span(),
                        "`isolate`: expected `isolate()`, with the options `rlimit = N` (a number or `infinity`) and `backend = z3` or `backend = cvc5`, each at most once",
                    )
                };
                let Expr::Assign(assign) = arg else { return Err(expected()) };
                let Expr::Path(key) = &*assign.left else { return Err(expected()) };
                let value = &assign.right;
                let value_ident = match &**value {
                    Expr::Path(p) => p.path.get_ident().map(|i| i.to_string()),
                    _ => None,
                };
                match key.path.get_ident().map(|i| i.to_string()).as_deref() {
                    Some("rlimit") if !rlimit => {
                        let is_number = matches!(&**value, Expr::Lit(l)
                            if matches!(l.lit, verus_syn::Lit::Int(_) | verus_syn::Lit::Float(_)));
                        if !is_number && value_ident.as_deref() != Some("infinity") {
                            return Err(expected());
                        }
                        rlimit = true;
                        options.push(quote_spanned!(span => rlimit(#value)));
                    }
                    Some("backend")
                        if !backend && matches!(value_ident.as_deref(), Some("z3" | "cvc5")) =>
                    {
                        backend = true;
                        options.push(quote_spanned!(span => backend(#value)));
                    }
                    _ => return Err(expected()),
                }
            }
            StepKind::Isolate(quote_spanned!(span => #(#options),*))
        }
        _ => unreachable!(),
    };
    Ok(Step { span, kind })
}

/// The goal without parentheses, or a block `{ e }` around it (as `&&&` lists need).
fn strip_parens(e: &Expr) -> &Expr {
    match e {
        Expr::Paren(p) => strip_parens(&p.expr),
        Expr::Group(g) => strip_parens(&g.expr),
        Expr::Block(b) if b.attrs.is_empty() && b.label.is_none() => match &b.block.stmts[..] {
            [Stmt::Expr(e, None)] => strip_parens(e),
            _ => e,
        },
        _ => e,
    }
}

/// `forall|x: T, ..| #![inner attrs] body`: the bound variables, the inner attributes (triggers)
/// and the body.
fn as_forall(e: &Expr) -> Option<(Vec<Pat>, Vec<verus_syn::Attribute>, &Expr)> {
    let Expr::Unary(u) = strip_parens(e) else { return None };
    let UnOp::Forall(_) = u.op else { return None };
    let Expr::Closure(c) = &*u.expr else { return None };
    if c.inputs.iter().any(|a| a.tracked_token.is_some()) {
        return None;
    }
    Some((c.inputs.iter().map(|a| a.pat.clone()).collect(), c.inner_attrs.clone(), &c.body))
}

fn as_implies(e: &Expr) -> Option<(&Expr, &Expr)> {
    match strip_parens(e) {
        Expr::Binary(b) if matches!(b.op, BinOp::Imply(_)) => Some((&b.left, &b.right)),
        _ => None,
    }
}

fn conjuncts<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match strip_parens(e) {
        Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
            conjuncts(&b.left, out);
            conjuncts(&b.right, out);
        }
        Expr::BigAnd(big) => {
            for e in big.exprs.iter() {
                conjuncts(&e.expr, out);
            }
        }
        // the part as written, not stripped: `{ ||| a ||| b }` needs its braces
        _ => out.push(e),
    }
}

/// The single expression of a block `{ e }`, or the block as an expression (also for a list
/// `{ &&& a &&& b }`, which needs its braces).
fn block_value(block: &Block) -> Expr {
    match &block.stmts[..] {
        [Stmt::Expr(e, None)] if !matches!(e, Expr::BigAnd(_) | Expr::BigOr(_)) => e.clone(),
        _ => Expr::Block(verus_syn::ExprBlock { attrs: vec![], label: None, block: block.clone() }),
    }
}

/// `let` in an `if` condition (`if let`, or a let chain).
fn contains_let(e: &Expr) -> bool {
    match strip_parens(e) {
        Expr::Let(_) => true,
        Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
            contains_let(&b.left) || contains_let(&b.right)
        }
        _ => false,
    }
}

/// The names that `pat` binds.
fn pat_names(pat: &Pat) -> Vec<verus_syn::Ident> {
    struct Names(Vec<verus_syn::Ident>);
    impl<'ast> verus_syn::visit::Visit<'ast> for Names {
        fn visit_pat_ident(&mut self, p: &'ast verus_syn::PatIdent) {
            self.0.push(p.ident.clone());
            verus_syn::visit::visit_pat_ident(self, p);
        }
    }
    let mut names = Names(Vec::new());
    verus_syn::visit::Visit::visit_pat(&mut names, pat);
    names.0
}

/// Does `e` use the name `x` (a path of one segment)? It may also count a use that is bound
/// inside `e`, which only makes the check that uses it stricter.
fn mentions(e: &Expr, x: &verus_syn::Ident) -> bool {
    struct Finder<'a>(&'a verus_syn::Ident, bool);
    impl<'ast, 'a> verus_syn::visit::Visit<'ast> for Finder<'a> {
        fn visit_expr_path(&mut self, p: &'ast verus_syn::ExprPath) {
            if p.qself.is_none() && p.path.get_ident() == Some(self.0) {
                self.1 = true;
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
    }
    let mut finder = Finder(x, false);
    verus_syn::visit::Visit::visit_expr(&mut finder, e);
    finder.1
}

enum SplitGoal {
    Parts(Vec<Expr>),
    If(Expr, Expr, Expr),
}

fn split_goal(goal: &Expr, span: Span) -> Result<SplitGoal> {
    match strip_parens(goal) {
        Expr::Binary(b) if matches!(b.op, BinOp::Equiv(_)) => {
            let (l, r) = (&b.left, &b.right);
            let imply = imply_tokens(span);
            Ok(SplitGoal::Parts(vec![
                parse_expr(quote_spanned!(span => (#l) #imply (#r)))?,
                parse_expr(quote_spanned!(span => (#r) #imply (#l)))?,
            ]))
        }
        Expr::If(i) => {
            if contains_let(&i.cond) {
                return Err(Error::new(
                    span,
                    "`split`: an `if let` goal is not supported; use `cases(match ..)` instead",
                ));
            }
            let Some((_, else_branch)) = &i.else_branch else {
                return Err(Error::new(span, "`split`: an `if` goal needs an `else`"));
            };
            let else_goal = match &**else_branch {
                Expr::Block(b) => block_value(&b.block),
                e => e.clone(),
            };
            Ok(SplitGoal::If((*i.cond).clone(), block_value(&i.then_branch), else_goal))
        }
        g => {
            let mut parts = Vec::new();
            conjuncts(g, &mut parts);
            if parts.len() < 2 {
                return Err(Error::new(
                    span,
                    format!(
                        "`split`: the goal `{}` is not a conjunction (`&&`, `&&&`), an `<==>` or an `if`",
                        show_expr(goal)
                    ),
                ));
            }
            Ok(SplitGoal::Parts(parts.into_iter().cloned().collect()))
        }
    }
}

/// `==>` as one operator: written in `quote!`, it would come out as `==` followed by `>`.
fn imply_tokens(span: Span) -> TokenStream {
    use proc_macro2::{Punct, Spacing};
    [('=', Spacing::Joint), ('=', Spacing::Joint), ('>', Spacing::Alone)]
        .into_iter()
        .map(|(c, spacing)| {
            let mut p = Punct::new(*c, *spacing);
            p.set_span(span);
            TokenTree::Punct(p)
        })
        .collect()
}

fn parse_expr(tokens: TokenStream) -> Result<Expr> {
    verus_syn::parse2(tokens)
}

fn parse_stmt(tokens: TokenStream) -> Result<Stmt> {
    let block: Block = verus_syn::parse2(quote::quote!({ #tokens }))?;
    let mut stmts = block.stmts;
    assert!(stmts.len() == 1);
    Ok(stmts.pop().unwrap())
}

/// `assert(goal);`, or `assert(goal) by { body }`. `note` says which step the assertion comes
/// from; it labels the error if the assertion fails (`#[verifier::proof_note]`).
fn assert_stmt(span: Span, note: &str, goal: &Expr, body: Vec<Stmt>) -> Result<Stmt> {
    let note = match note.split_once(": ") {
        Some((step, detail)) => format!("from the tactic step `{}` ({})", step, detail),
        None => format!("from the tactic step `{}`", note),
    };
    if body.is_empty() {
        parse_stmt(quote_spanned!(span => #[verifier::proof_note(#note)] assert(#goal);))
    } else {
        let mut stmt = parse_stmt(
            quote_spanned!(span => #[verifier::proof_note(#note)] assert(#goal) by {};),
        )?;
        let Stmt::Expr(Expr::Assert(a), _) = &mut stmt else { unreachable!() };
        a.body.as_mut().unwrap().stmts = body;
        Ok(stmt)
    }
}

/// Replace the statements of the first (and only) block in `stmt` built by `parse_stmt` with
/// `body`: used for `if c {} else {}`, whose branches are filled in afterwards.
fn if_stmt(
    span: Span,
    cond: &Expr,
    then_body: Vec<Stmt>,
    else_body: Option<Vec<Stmt>>,
) -> Result<Stmt> {
    let mut stmt = if else_body.is_some() {
        parse_stmt(quote_spanned!(span => if (#cond) {} else {}))?
    } else {
        parse_stmt(quote_spanned!(span => if (#cond) {}))?
    };
    let Stmt::Expr(Expr::If(i), _) = &mut stmt else { unreachable!() };
    i.then_branch.stmts = then_body;
    if let Some(else_body) = else_body {
        let Some((_, e)) = &mut i.else_branch else { unreachable!() };
        let Expr::Block(b) = &mut **e else { unreachable!() };
        b.block.stmts = else_body;
    }
    Ok(stmt)
}

fn item_span(item: &Item) -> Span {
    match item {
        Item::Stmt(s) => s.span(),
        Item::Step(s) => s.span,
    }
}

/// The statements that prove `goal` with the steps `items`: the block they go in ends with
/// `goal` being asserted (by the caller).
fn expand_items(goal: &Expr, items: &[Item], facts: &Facts) -> Result<Vec<Stmt>> {
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut facts = facts.clone();
    for (i, item) in items.iter().enumerate() {
        let rest = &items[i + 1..];
        let step = match item {
            Item::Stmt(stmt) => {
                if let Stmt::Expr(Expr::Assert(a), _) = stmt {
                    facts = facts.with(show_expr(&a.expr));
                }
                stmts.push(stmt.clone());
                continue;
            }
            Item::Step(step) => step,
        };
        let span = step.span;
        if step.kind.closes_goal() {
            if let Some(next) = rest.first() {
                return Err(Error::new(
                    item_span(next),
                    "no steps may follow `smt(..)` or `compute()`: they prove the goal",
                ));
            }
        }
        let no_rest = |what: &str| -> Result<()> {
            match rest.first() {
                Some(next) => Err(Error::new(
                    item_span(next),
                    format!("no steps may follow {}: put them in its blocks", what),
                )),
                None => Ok(()),
            }
        };
        match &step.kind {
            StepKind::Have(q) => {
                stmts.push(assert_stmt(span, "have", q, vec![])?);
                facts = facts.with(show_expr(q));
            }
            StepKind::Unfold(f, None) => {
                stmts.push(parse_stmt(quote_spanned!(span => reveal(#f);))?);
                facts = facts.with(format!("`{}` unfolded", show_expr(f)));
            }
            StepKind::Unfold(f, Some(fuel)) => {
                stmts.push(parse_stmt(quote_spanned!(span => reveal_with_fuel(#f, #fuel);))?);
                facts =
                    facts.with(format!("`{}` unfolded, fuel {}", show_expr(f), show_expr(fuel)));
            }
            StepKind::Apply(e) => {
                stmts.push(parse_stmt(quote_spanned!(span => #e;))?);
                facts = facts.with(format!("the `ensures` of `{}`", show_expr(e)));
            }
            StepKind::Inst(fact, terms) => {
                let (pats, _, body) = as_forall(fact).unwrap();
                // one `let` for all the variables, so that a term cannot refer to a variable
                // that an earlier `let` of the instance binds
                let instance = if pats.len() == 1 {
                    let (pat, t) = (&pats[0], &terms[0]);
                    parse_expr(quote_spanned!(span => { let #pat = (#t); (#body) }))?
                } else {
                    let names = pats.iter().map(|p| match p {
                        Pat::Type(p) => p.pat.to_token_stream(),
                        p => p.to_token_stream(),
                    });
                    let types = pats.iter().map(|p| match p {
                        Pat::Type(p) => p.ty.to_token_stream(),
                        _ => quote_spanned!(span => _),
                    });
                    parse_expr(quote_spanned!(span =>
                        { let (#(#names),*): (#(#types),*) = (#((#terms)),*); (#body) }
                    ))?
                };
                stmts.push(assert_stmt(span, "inst", fact, vec![])?);
                stmts.push(assert_stmt(span, "inst", &instance, vec![])?);
                facts = facts.with(show_expr(&instance));
            }
            StepKind::Show => {
                show_note(span, goal, &facts);
            }
            StepKind::Isolate(options) => {
                // `assert(goal) by { #[verus::internal(isolate(..))] { rest } }`: rust_verify
                // makes the proof (and the assertion of the goal at its end) a part of the query
                // of its own (`air::context::Context::set_partitions`)
                let block = Block {
                    brace_token: verus_syn::token::Brace(span),
                    stmts: expand_items(goal, rest, &facts)?,
                };
                let marked = Stmt::Expr(
                    Expr::Block(verus_syn::ExprBlock {
                        attrs: vec![crate::syntax::mk_verus_attr(
                            span,
                            quote_spanned!(span => isolate(#options)),
                        )],
                        label: None,
                        block,
                    }),
                    None,
                );
                stmts.push(assert_stmt(span, "isolate", goal, vec![marked])?);
                return Ok(stmts);
            }
            StepKind::Smt(None, _) => {
                stmts.push(assert_stmt(span, "smt", goal, vec![])?);
            }
            StepKind::Smt(Some(prover), requires) => {
                let requires = if requires.is_empty() {
                    quote_spanned!(span =>)
                } else {
                    quote_spanned!(span => requires #(#requires),*)
                };
                stmts.push(parse_stmt(
                    quote_spanned!(span => assert(#goal) by(#prover) #requires;),
                )?);
            }
            StepKind::Compute => {
                stmts.push(parse_stmt(quote_spanned!(span => assert(#goal) by(compute);))?);
            }
            StepKind::Intro => {
                if let Some((pats, attrs, body)) = as_forall(goal) {
                    let bound = pats.iter().map(show_pat).collect::<Vec<_>>().join(", ");
                    let facts = facts.with(format!("{} (bound by `intro`)", bound));
                    let (stmt_tokens, new_goal, facts) = match as_implies(body) {
                        Some((a, b)) => (
                            quote_spanned!(span => assert forall|#(#pats),*| #(#attrs)* (#a) implies (#b) by {};),
                            b,
                            facts.with(show_expr(a)),
                        ),
                        None => (
                            quote_spanned!(span => assert forall|#(#pats),*| #(#attrs)* (#body) by {};),
                            body,
                            facts,
                        ),
                    };
                    let mut stmt = parse_stmt(stmt_tokens)?;
                    let Stmt::Expr(Expr::AssertForall(a), _) = &mut stmt else { unreachable!() };
                    a.body.stmts = expand_items(new_goal, rest, &facts)?;
                    stmts.push(stmt);
                } else if let Some((a, b)) = as_implies(goal) {
                    let body = expand_items(b, rest, &facts.with(show_expr(a)))?;
                    stmts.push(if_stmt(span, a, vec![assert_stmt(span, "intro", b, body)?], None)?);
                } else {
                    return Err(Error::new(
                        span,
                        format!(
                            "`intro`: the goal `{}` is not a `forall` or an `==>`",
                            show_expr(goal)
                        ),
                    ));
                }
                return Ok(stmts);
            }
            StepKind::Split(scripts) => {
                let split = split_goal(goal, span)?;
                let parts = match &split {
                    SplitGoal::Parts(parts) => parts.len(),
                    SplitGoal::If(..) => 2,
                };
                if !scripts.is_empty() {
                    if scripts.len() != parts {
                        return Err(Error::new(
                            span,
                            format!(
                                "`split`: the goal has {} parts, but {} block{} given",
                                parts,
                                scripts.len(),
                                if scripts.len() == 1 { " is" } else { "s are" }
                            ),
                        ));
                    }
                    no_rest("`split` with blocks")?;
                }
                let script =
                    |k: usize| -> &[Item] { if scripts.is_empty() { rest } else { &scripts[k] } };
                match split {
                    SplitGoal::Parts(parts) => {
                        let n = parts.len();
                        for (k, part) in parts.iter().enumerate() {
                            let body = expand_items(part, script(k), &facts)?;
                            let note = format!("split: part {} of {}", k + 1, n);
                            stmts.push(assert_stmt(span, &note, part, body)?);
                        }
                    }
                    SplitGoal::If(cond, then_goal, else_goal) => {
                        let then_body =
                            expand_items(&then_goal, script(0), &facts.with(show_expr(&cond)))?;
                        let else_body = expand_items(
                            &else_goal,
                            script(1),
                            &facts.with(format!("!({})", show_expr(&cond))),
                        )?;
                        stmts.push(if_stmt(
                            span,
                            &cond,
                            vec![assert_stmt(
                                span,
                                "split: the `if` branch",
                                &then_goal,
                                then_body,
                            )?],
                            Some(vec![assert_stmt(
                                span,
                                "split: the `else` branch",
                                &else_goal,
                                else_body,
                            )?]),
                        )?);
                    }
                }
                return Ok(stmts);
            }
            StepKind::Cases(b, scripts) => {
                if scripts.is_some() {
                    no_rest("`cases` with blocks")?;
                }
                let (then_script, else_script) = match scripts {
                    Some((t, e)) => (&t[..], &e[..]),
                    None => (rest, rest),
                };
                let then_body = expand_items(goal, then_script, &facts.with(show_expr(b)))?;
                let else_body =
                    expand_items(goal, else_script, &facts.with(format!("!({})", show_expr(b))))?;
                stmts.push(if_stmt(
                    span,
                    b,
                    vec![assert_stmt(span, "cases: the condition holds", goal, then_body)?],
                    Some(vec![assert_stmt(
                        span,
                        "cases: the condition does not hold",
                        goal,
                        else_body,
                    )?]),
                )?);
                return Ok(stmts);
            }
            StepKind::CasesMatch(m, scripts) => {
                no_rest("`cases(match ..)`")?;
                let mut m = m.clone();
                for (k, (arm, script)) in m.arms.iter_mut().zip(scripts.iter()).enumerate() {
                    // the goal is asserted inside the arm, where a name the pattern binds
                    // would mean the new variable, not the one the goal is about
                    if let Some(x) = pat_names(&arm.pat).into_iter().find(|x| mentions(goal, x)) {
                        return Err(Error::new(
                            x.span(),
                            format!(
                                "`cases`: the pattern binds `{}`, which the goal also uses; give the pattern variable another name",
                                x
                            ),
                        ));
                    }
                    let arm_facts = facts.with(format!(
                        "`{}` matches `{}`",
                        show_expr(&m.expr),
                        show_pat(&arm.pat)
                    ));
                    let body = expand_items(goal, script, &arm_facts)?;
                    let block = Block {
                        brace_token: verus_syn::token::Brace(arm.body.span()),
                        stmts: vec![assert_stmt(
                            span,
                            &format!("cases: arm {}", k + 1),
                            goal,
                            body,
                        )?],
                    };
                    arm.body = Box::new(Expr::Block(verus_syn::ExprBlock {
                        attrs: vec![],
                        label: None,
                        block,
                    }));
                    arm.comma = Some(verus_syn::token::Comma(span));
                }
                stmts.push(Stmt::Expr(Expr::Match(m), None));
                return Ok(stmts);
            }
        }
    }
    Ok(stmts)
}

/// `show()`: a note at the step with the goal and the facts that the script added.
fn show_note(span: Span, goal: &Expr, facts: &Facts) {
    let mut msg = format!("tactic: the goal here is\n    {}", show_expr(goal));
    if facts.0.is_empty() {
        msg.push_str("\nthe script has added no facts before this step");
    } else {
        msg.push_str("\nfacts that the script added before this step:");
        for fact in facts.0.iter() {
            msg.push_str("\n    ");
            msg.push_str(fact);
        }
    }
    msg.push_str(
        "\n(as written in the source: nothing here has been checked yet, and the facts of the context, such as `requires` and the statements before the assertion, are not listed)",
    );
    #[cfg(verus_keep_ghost)]
    if !crate::cfg_erase().erase() {
        proc_macro::Diagnostic::spanned(span.unwrap(), proc_macro::Level::Note, msg).emit();
    }
    #[cfg(not(verus_keep_ghost))]
    let _ = (span, msg);
}

fn show_pat(pat: &Pat) -> String {
    let text = verus_prettyplease::unparse_pat(pat);
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn show_expr(e: &Expr) -> String {
    let text = verus_prettyplease::unparse_expr(e);
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}
