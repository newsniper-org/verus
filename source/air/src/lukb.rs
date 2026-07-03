//! AIR → lu-kb-successor surface renderer (Phase 1c).
//!
//! Renders an AIR obligation — the global declarations plus a checked
//! [`QueryX`] — to the **lu-kb-successor surface** (`adsmt-ir-lukb`), emitted
//! behind `-V emit-lukb` to a `.lukb` log ALONGSIDE the canonical `.smt2`. The
//! SMT-LIB path stays the verdict oracle; this log exists for the structural
//! (parse/elaborate) differential and for inspecting the less-lossy surface.
//!
//! ## Mapping
//!
//! | AIR | lu-kb-successor item |
//! |-----|----------------------|
//! | `DeclX::Sort`        | `sort S`                              |
//! | `DeclX::Const`/`Var` | `const x: T`                          |
//! | `DeclX::Fun`         | `fn f(x0: T0, …): U` (synthetic names) |
//! | `DeclX::Axiom`       | `axiom [name]: φ`                     |
//! | `StmtX::Assume`      | `assume: h`                           |
//! | `StmtX::Assert`      | `goal: g` — the **un-negated** goal (the lukb goal is structural; negation is the solver's job) |
//!
//! Identifiers carrying characters a bare name can't hold (`%`, `~`, `@`, `!`,
//! `.`) or a keyword spelling are **backtick-quoted** (`` `%%location_label%%0` ``)
//! so Verus/AIR's internal names round-trip *faithfully* rather than being
//! mangled (mangling loses the name — *more* lossy than SMT-LIB).
//!
//! ## Fallback (never a silent drop)
//!
//! Tier-2+ constructs (bit-vectors, floats, arrays, higher-order
//! lambda/choose/apply-fun, Z3 special relations) and the imperative statements
//! that survive an unusual lowering (havoc/assign/snapshot/break) have no
//! lu-kb-successor form. They are emitted as a `#`
//! comment carrying a short reason — the lukb lexer skips `#` lines, so the
//! file still parses, and nothing is silently dropped (the comment records what
//! the SMT-LIB path carries that the surface can't yet express).

use crate::ast::*;

// ── precedence ladder (mirrors the adsmt-ir-lukb parser/printer) ───────────
// iff 1 · implies 2 · or 3 · and 4 · cmp 5 · add 6 · mul 7 · unary 8 · atom 9
// `ctx` is the surrounding precedence; a node parenthesises when it binds looser.

/// Render a **global declaration** as one or more lu-kb-successor lines
/// (an item, or a `#` fallback comment), terminated by `\n`.
pub(crate) fn decl_to_lukb(decl: &DeclX) -> String {
    match decl {
        DeclX::Sort(name) => match checked_ident(name) {
            Ok(n) => format!("sort {n}\n"),
            Err(r) => fallback("sort", &r),
        },
        DeclX::Const(name, ty) | DeclX::Var(name, ty) => render_const(name, ty),
        DeclX::Fun(name, params, ret) => render_fun(name, params, ret),
        DeclX::Axiom(ax) => {
            let name = ax.named.as_ref().map(|s| s.as_str());
            render_item("axiom", name, &ax.expr)
        }
        DeclX::Datatypes(dts) => render_datatypes(dts),
    }
}

/// Render an AIR datatype group (`declare-datatypes`) to lu-kb-successor `data`
/// items. Verus monomorphises before AIR, so every AIR datatype is arity-0
/// (non-parametric) — exactly the fragment the lukb `data` surface (slice 7)
/// accepts. Each datatype in the group is rendered independently; one whose
/// field carries a type the surface can't express (a Tier-2 `BitVec`/`Array`/
/// `Fun` field) drops to a `#` comment on its own line, so a mixed group still
/// contributes every representable member (never a silent drop).
fn render_datatypes(dts: &Datatypes) -> String {
    let mut out = String::new();
    for dt in dts.iter() {
        match render_one_datatype(dt) {
            Ok(line) => out.push_str(&line),
            Err(r) => out.push_str(&fallback("datatypes", &r)),
        }
    }
    out
}

/// `data N = C0(f: T, …) | C1 | …` — one datatype. A nullary constructor is a
/// bare name (`nil`); a constructor with fields carries its named selectors
/// (`cons(head: Int, tail: Lst)`) — AIR always names its fields, and the lukb
/// surface round-trips selector names (they are sugar the solver lowering
/// re-synthesises positionally).
fn render_one_datatype(dt: &Datatype) -> Result<String, String> {
    let name = checked_ident(&dt.name)?;
    let mut ctors = Vec::with_capacity(dt.a.len());
    for variant in dt.a.iter() {
        let cname = checked_ident(&variant.name)?;
        if variant.a.is_empty() {
            ctors.push(cname);
            continue;
        }
        let mut fields = Vec::with_capacity(variant.a.len());
        for field in variant.a.iter() {
            let fname = checked_ident(&field.name)?;
            let fty = typ(&field.a)?;
            fields.push(format!("{fname}: {fty}"));
        }
        ctors.push(format!("{cname}({})", fields.join(", ")));
    }
    // A datatype with no constructors has no lukb `data` form (an empty sum);
    // it can't arise from a Verus type, but guard rather than emit `data N = `.
    if ctors.is_empty() {
        return Err(format!("datatype {} has no constructors", &*dt.name));
    }
    Ok(format!("data {name} = {}\n", ctors.join(" | ")))
}

/// Render a checked query — its local declarations followed by the assertion
/// statement tree mapped to `assume`/`goal` items.
pub(crate) fn query_to_lukb(query: &QueryX) -> String {
    let mut out = String::new();
    for decl in query.local.iter() {
        out.push_str(&decl_to_lukb(decl));
    }
    stmt_to_lukb(&query.assertion, &mut out);
    out
}

// ── declarations ───────────────────────────────────────────────────────────

fn render_const(name: &str, ty: &TypX) -> String {
    let n = match checked_ident(name) {
        Ok(n) => n,
        Err(r) => return fallback("const", &r),
    };
    match typ(ty) {
        Ok(t) => format!("const {n}: {t}\n"),
        Err(r) => fallback("const", &format!("{name}: {r}")),
    }
}

fn render_fun(name: &str, params: &[Typ], ret: &TypX) -> String {
    let n = match checked_ident(name) {
        Ok(n) => n,
        Err(r) => return fallback("fn", &r),
    };
    let rt = match typ(ret) {
        Ok(t) => t,
        Err(r) => return fallback("fn", &format!("{name} ret: {r}")),
    };
    // A 0-ary AIR `Fun` is a constant; lukb represents it as `const` (and a
    // 0-ary `Apply` of it renders as a bare ident — see `expr`), so the two
    // stay consistent.
    if params.is_empty() {
        return format!("const {n}: {rt}\n");
    }
    let mut ps = Vec::with_capacity(params.len());
    for (i, pt) in params.iter().enumerate() {
        match typ(pt) {
            Ok(t) => ps.push(format!("x{i}: {t}")),
            Err(r) => return fallback("fn", &format!("{name} param {i}: {r}")),
        }
    }
    format!("fn {n}({}): {rt}\n", ps.join(", "))
}

/// Render an obligation item (`axiom`/`assume`/`goal`), falling back to a `#`
/// comment when the body uses a construct the surface can't express.
fn render_item(kw: &str, name: Option<&str>, body: &Expr) -> String {
    match expr(body, 0) {
        Ok(rendered) => {
            let mut s = String::from(kw);
            // An unrenderable *name* (backtick inside it) just drops to the
            // unnamed (auto-numbered) form — the body is what matters.
            if let Some(n) = name {
                if let Ok(qn) = checked_ident(n) {
                    s.push(' ');
                    s.push_str(&qn);
                }
            }
            s.push_str(": ");
            s.push_str(&rendered);
            s.push('\n');
            s
        }
        Err(reason) => fallback(kw, &reason),
    }
}

// ── statements ─────────────────────────────────────────────────────────────

fn stmt_to_lukb(s: &StmtX, out: &mut String) {
    match s {
        StmtX::Assume(e) => out.push_str(&render_item("assume", None, e)),
        StmtX::Assert(_, _, _, e) => out.push_str(&render_item("goal", None, e)),
        StmtX::Block(stmts) => {
            for st in stmts.iter() {
                stmt_to_lukb(st, out);
            }
        }
        StmtX::DeadEnd(st) => {
            out.push_str("# dead-end block (assumptions local to the block):\n");
            stmt_to_lukb(st, out);
        }
        StmtX::Breakable(_, st) => stmt_to_lukb(st, out),
        StmtX::Switch(stmts) => {
            // Nondeterministic choice of one branch — no lukb disjunction-of-
            // paths form, so the branches are emitted comment-delimited.
            out.push_str("# switch (nondeterministic choice of one branch):\n");
            for (i, st) in stmts.iter().enumerate() {
                out.push_str(&format!("# branch {i}:\n"));
                stmt_to_lukb(st, out);
            }
        }
        // These imperative ops are eliminated by `var_to_const` + `block_to_assert`
        // before the final query; if one survives, record it rather than drop it.
        StmtX::Havoc(x) => out.push_str(&fallback("stmt", &format!("havoc {x}"))),
        StmtX::Assign(x, _) => out.push_str(&fallback("stmt", &format!("assign {x}"))),
        StmtX::Snapshot(x) => out.push_str(&fallback("stmt", &format!("snapshot {x}"))),
        StmtX::Break(x) => out.push_str(&fallback("stmt", &format!("break {x}"))),
    }
}

// ── expressions ────────────────────────────────────────────────────────────

fn expr(e: &Expr, ctx: u8) -> Result<String, String> {
    match &**e {
        ExprX::Const(c) => constant(c),
        ExprX::Var(x) => checked_ident(x),
        ExprX::Old(snap, x) => Err(format!("snapshot read {x}@{snap}")),
        ExprX::Apply(f, args) => apply(f, args),
        ExprX::ApplyFun(..) => Err("higher-order ApplyFun".to_string()),
        ExprX::Unary(op, a) => unary(*op, a, ctx),
        ExprX::Binary(op, a, b) => binary(op, a, b, ctx),
        ExprX::Multi(op, args) => multi(*op, args, ctx),
        ExprX::IfElse(c, a, b) => if_then_else(c, a, b, ctx),
        ExprX::Array(_) => Err("array literal".to_string()),
        ExprX::Bind(bind, body) => bind_expr(bind, body, ctx),
        ExprX::LabeledAxiom(_, _, inner) => expr(inner, ctx),
        ExprX::LabeledAssertion(_, _, _, inner) => expr(inner, ctx),
    }
}

fn constant(c: &Constant) -> Result<String, String> {
    match c {
        Constant::Bool(true) => Ok("true".to_string()),
        Constant::Bool(false) => Ok("false".to_string()),
        // AIR `Nat` is decimal digits (lukb Int); `Real` is `digits.digits`
        // (lukb Real) — both lex back verbatim.
        Constant::Nat(s) => Ok((**s).clone()),
        Constant::Real(s) => Ok((**s).clone()),
        Constant::BitVec(..) => Err("bit-vector literal".to_string()),
    }
}

fn apply(f: &str, args: &[Expr]) -> Result<String, String> {
    let head = checked_ident(f)?;
    // A 0-ary application is a bare symbol (consistent with a 0-ary `Fun`
    // rendered as a `const`).
    if args.is_empty() {
        return Ok(head);
    }
    let mut parts = Vec::with_capacity(args.len());
    for a in args.iter() {
        parts.push(expr(a, 0)?);
    }
    Ok(format!("{head}({})", parts.join(", ")))
}

fn unary(op: UnaryOp, a: &Expr, ctx: u8) -> Result<String, String> {
    match op {
        UnaryOp::Not => Ok(paren(ctx > 8, format!("not {}", expr(a, 8)?))),
        UnaryOp::ToReal => Ok(format!("to_real({})", expr(a, 0)?)),
        // `RealToInt`/bit/float unary ops have no Tier-0/1 lukb form (no
        // `to_int` builtin yet).
        _ => Err(format!("unary op {op:?}")),
    }
}

fn binary(op: &BinaryOp, a: &Expr, b: &Expr, ctx: u8) -> Result<String, String> {
    // Euclidean div/mod map to the lukb `div`/`mod` builtins (prefix calls).
    match op {
        BinaryOp::EuclideanDiv => return Ok(format!("div({}, {})", expr(a, 0)?, expr(b, 0)?)),
        BinaryOp::EuclideanMod => return Ok(format!("mod({}, {})", expr(a, 0)?, expr(b, 0)?)),
        _ => {}
    }
    let (sym, prec) = match op {
        BinaryOp::Implies => ("==>", 2u8),
        BinaryOp::Eq => ("=", 5),
        BinaryOp::Le => ("<=", 5),
        BinaryOp::Ge => (">=", 5),
        BinaryOp::Lt => ("<", 5),
        BinaryOp::Gt => (">", 5),
        BinaryOp::RealDiv => ("/", 7),
        // bit/float ops, Z3 special `Relation`, `FieldUpdate` — no lukb form.
        _ => return Err(format!("binary op {op:?}")),
    };
    // Child precedence by associativity: `==>` is right-assoc; comparisons are
    // non-associative (both operands one tighter, so a nested compare can't be
    // misread as a chain); `/` is left-assoc.
    let (lp, rp) = match op {
        BinaryOp::Implies => (prec + 1, prec),
        BinaryOp::Eq | BinaryOp::Le | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Gt => {
            (prec + 1, prec + 1)
        }
        _ => (prec, prec + 1),
    };
    Ok(paren(ctx > prec, format!("{} {sym} {}", expr(a, lp)?, expr(b, rp)?)))
}

fn multi(op: MultiOp, args: &[Expr], ctx: u8) -> Result<String, String> {
    let (sep, prec) = match op {
        MultiOp::And => (" and ", 4u8),
        MultiOp::Or => (" or ", 3),
        MultiOp::Add => (" + ", 6),
        MultiOp::Sub => (" - ", 6),
        MultiOp::Mul => (" * ", 7),
        MultiOp::Distinct => return distinct(args, ctx),
        MultiOp::Xor => return Err("xor".to_string()),
        MultiOp::Float => return Err("fp constructor".to_string()),
    };
    if args.is_empty() {
        // Identity element of the (empty) fold.
        return Ok(match op {
            MultiOp::And => "true".to_string(),
            MultiOp::Or => "false".to_string(),
            MultiOp::Add => "0".to_string(),
            MultiOp::Mul => "1".to_string(),
            _ => return Err("empty subtraction".to_string()),
        });
    }
    // A single-argument `Sub` is unary minus.
    if matches!(op, MultiOp::Sub) && args.len() == 1 {
        return Ok(paren(ctx > 8, format!("-{}", expr(&args[0], 8)?)));
    }
    let mut parts = Vec::with_capacity(args.len());
    for a in args.iter() {
        parts.push(expr(a, prec + 1)?);
    }
    Ok(paren(ctx > prec, parts.join(sep)))
}

fn distinct(args: &[Expr], ctx: u8) -> Result<String, String> {
    match args.len() {
        0 | 1 => Ok("true".to_string()),
        2 => Ok(paren(ctx > 5, format!("{} != {}", expr(&args[0], 6)?, expr(&args[1], 6)?))),
        _ => {
            // pairwise `and` of `!=`
            let mut clauses = Vec::new();
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    clauses.push(format!("{} != {}", expr(&args[i], 6)?, expr(&args[j], 6)?));
                }
            }
            Ok(paren(ctx > 4, clauses.join(" and ")))
        }
    }
}

fn bind_expr(bind: &BindX, body: &Expr, ctx: u8) -> Result<String, String> {
    match bind {
        BindX::Let(binders) => {
            // Nest single-binding lukb lets, innermost = the body.
            let mut inner = expr(body, 0)?;
            for b in binders.iter().rev() {
                let name = checked_ident(&b.name)?;
                inner = format!("let {name} = {} in {inner}", expr(&b.a, 0)?);
            }
            Ok(paren(ctx > 0, inner))
        }
        BindX::Quant(q, binders, triggers, _qid) => {
            let kw = match q {
                Quant::Forall => "forall",
                Quant::Exists => "exists",
            };
            let mut s = String::from(kw);
            s.push(' ');
            for (i, b) in binders.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(&checked_ident(&b.name)?);
                s.push_str(": ");
                s.push_str(&typ(&b.a)?);
            }
            s.push_str(". ");
            s.push_str(&expr(body, 0)?);
            // Triggers are out-of-band (dropped at elaboration), so render them
            // best-effort: an unrenderable pattern just omits its clause rather
            // than sinking the whole quantifier.
            for trig in triggers.iter() {
                if let Some(clause) = render_trigger(trig) {
                    s.push_str(&clause);
                }
            }
            Ok(paren(ctx > 0, s))
        }
        BindX::Lambda(..) => Err("higher-order lambda".to_string()),
        BindX::Choose(..) => Err("choose binder".to_string()),
    }
}

/// `if c then a else b` — the surface conditional (adsmt-ir-lukb slice ①,
/// `4ae487d`: `S::If` → the `ite` prelude const, lowered by the Verus-verified
/// term-`ite` atom-duplication). Emitted for AIR `ExprX::IfElse`, which is *also*
/// how Verus's VIR lowers every Rust `match` (desugared to nested `IfElse` +
/// `is-Variant`/selector applies before AIR — `ast_simplify`), so this one arm
/// carries every Verus conditional. A loosest-precedence prefix form (like
/// `let`/quantifiers), parenthesised when it sits in a tighter context; the
/// condition is Prop and the two branch values reconcile to one sort on the
/// adsmt side, so all three sub-terms render at the top (`0`) precedence.
fn if_then_else(c: &Expr, a: &Expr, b: &Expr, ctx: u8) -> Result<String, String> {
    let cond = expr(c, 0)?;
    let then_branch = expr(a, 0)?;
    let else_branch = expr(b, 0)?;
    Ok(paren(ctx > 0, format!("if {cond} then {then_branch} else {else_branch}")))
}

/// A trigger clause `trigger p` / `trigger { p1, … }`, or `None` if any pattern
/// is unrenderable (triggers only guide instantiation, so dropping is sound).
fn render_trigger(trig: &[Expr]) -> Option<String> {
    let mut pats = Vec::with_capacity(trig.len());
    for p in trig.iter() {
        pats.push(expr(p, 8).ok()?); // application level
    }
    match pats.len() {
        0 => None,
        1 => Some(format!(" trigger {}", pats[0])),
        _ => Some(format!(" trigger {{ {} }}", pats.join(", "))),
    }
}

// ── types ──────────────────────────────────────────────────────────────────

fn typ(t: &TypX) -> Result<String, String> {
    match t {
        TypX::Bool => Ok("Bool".to_string()),
        TypX::Int => Ok("Int".to_string()),
        TypX::Real => Ok("Real".to_string()),
        TypX::Named(n) => checked_ident(n),
        TypX::Fun => Err("Fun type".to_string()),
        TypX::BitVec(w) => Err(format!("BitVec({w})")),
        TypX::Float { exp_bits, sig_bits } => Err(format!("Float({exp_bits}, {sig_bits})")),
    }
}

// ── identifiers + fallback ───────────────────────────────────────────────────

/// A reserved lu-kb-successor keyword (must be backtick-quoted to be used as a
/// symbol). Kept in sync with `adsmt-ir-lukb`'s lexer.
fn is_lukb_keyword(s: &str) -> bool {
    matches!(
        s,
        "sort"
            | "const"
            | "fn"
            | "axiom"
            | "assume"
            | "goal"
            | "forall"
            | "exists"
            | "let"
            | "in"
            | "trigger"
            | "not"
            | "and"
            | "or"
            | "true"
            | "false"
    )
}

/// Whether `s` must be backtick-quoted to lex back as this exact identifier.
fn needs_quote(s: &str) -> bool {
    let mut chars = s.chars();
    let bare = match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        _ => false,
    };
    !bare || is_lukb_keyword(s)
}

/// Render an identifier, backtick-quoting it when a bare spelling would not lex
/// back. A name that *itself* contains a backtick has no representation in this
/// surface (it never occurs in AIR/SMT names) → reported, not mis-rendered.
fn checked_ident(s: &str) -> Result<String, String> {
    if s.contains('`') {
        return Err(format!("identifier contains a backtick: {s}"));
    }
    Ok(if needs_quote(s) { format!("`{s}`") } else { s.to_string() })
}

fn paren(cond: bool, s: String) -> String {
    if cond { format!("({s})") } else { s }
}

/// A `#` comment line recording a construct the surface can't express (the
/// lukb lexer skips it, so the file still parses — never a silent drop).
fn fallback(kind: &str, reason: &str) -> String {
    format!("# fallback ({kind}): {reason}\n")
}

// ── tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn var(name: &str) -> Expr {
        Arc::new(ExprX::Var(Arc::new(name.to_string())))
    }
    fn nat(n: &str) -> Expr {
        Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.to_string()))))
    }
    fn binder(name: &str, t: TypX) -> Binder<Typ> {
        Arc::new(BinderX { name: Arc::new(name.to_string()), a: Arc::new(t) })
    }

    #[test]
    fn renders_a_quantified_implication() {
        // forall x: Int. x > 0 ==> x >= 0
        let gt = Arc::new(ExprX::Binary(BinaryOp::Gt, var("x"), nat("0")));
        let ge = Arc::new(ExprX::Binary(BinaryOp::Ge, var("x"), nat("0")));
        let imp = Arc::new(ExprX::Binary(BinaryOp::Implies, gt, ge));
        let bind = Arc::new(BindX::Quant(
            Quant::Forall,
            Arc::new(vec![binder("x", TypX::Int)]),
            Arc::new(vec![]),
            None,
        ));
        let forall = Arc::new(ExprX::Bind(bind, imp));
        assert_eq!(expr(&forall, 0).unwrap(), "forall x: Int. x > 0 ==> x >= 0");
    }

    #[test]
    fn renders_if_then_else() {
        // if x > 0 then x else 0 - x   (the shape Verus VIR desugars match into)
        let c = Arc::new(ExprX::Binary(BinaryOp::Gt, var("x"), nat("0")));
        let neg = Arc::new(ExprX::Multi(MultiOp::Sub, Arc::new(vec![nat("0"), var("x")])));
        let ite = Arc::new(ExprX::IfElse(c, var("x"), neg));
        // top level: no parens
        assert_eq!(expr(&ite, 0).unwrap(), "if x > 0 then x else 0 - x");
        // nested in a tighter context (as an operand): parenthesised, like let/quant
        let eq = Arc::new(ExprX::Binary(BinaryOp::Eq, ite, var("x")));
        assert_eq!(expr(&eq, 0).unwrap(), "(if x > 0 then x else 0 - x) = x");
    }

    #[test]
    fn renders_and_chain_and_distinct() {
        // (and (> x 0) (< x 10))
        let a = Arc::new(ExprX::Binary(BinaryOp::Gt, var("x"), nat("0")));
        let b = Arc::new(ExprX::Binary(BinaryOp::Lt, var("x"), nat("10")));
        let conj = Arc::new(ExprX::Multi(MultiOp::And, Arc::new(vec![a, b])));
        assert_eq!(expr(&conj, 0).unwrap(), "x > 0 and x < 10");
        // (distinct a b) -> a != b
        let d = Arc::new(ExprX::Multi(MultiOp::Distinct, Arc::new(vec![var("a"), var("b")])));
        assert_eq!(expr(&d, 0).unwrap(), "a != b");
    }

    #[test]
    fn quotes_special_and_keyword_idents() {
        assert_eq!(checked_ident("%%loc%%0").unwrap(), "`%%loc%%0`");
        assert_eq!(checked_ident("forall").unwrap(), "`forall`");
        assert_eq!(checked_ident("plain_1").unwrap(), "plain_1");
    }

    #[test]
    fn renders_decls_and_falls_back_on_tier2() {
        assert_eq!(decl_to_lukb(&DeclX::Sort(Arc::new("S".to_string()))), "sort S\n");
        let c = DeclX::Const(Arc::new("x".to_string()), Arc::new(TypX::Int));
        assert_eq!(decl_to_lukb(&c), "const x: Int\n");
        // a Fun with synthetic param names
        let f = DeclX::Fun(
            Arc::new("f".to_string()),
            Arc::new(vec![Arc::new(TypX::Int), Arc::new(TypX::Bool)]),
            Arc::new(TypX::Int),
        );
        assert_eq!(decl_to_lukb(&f), "fn f(x0: Int, x1: Bool): Int\n");
        // a bit-vector const falls back to a comment (still parseable lukb)
        let bv = DeclX::Const(Arc::new("b".to_string()), Arc::new(TypX::BitVec(8)));
        assert!(decl_to_lukb(&bv).starts_with("# fallback (const):"));
    }

    fn mk<A>(name: &str, a: A) -> Arc<BinderX<A>> {
        Arc::new(BinderX { name: Arc::new(name.to_string()), a })
    }

    #[test]
    fn renders_a_recursive_datatype() {
        // data Lst = nil | cons(head: Int, tail: Lst)
        let int: Typ = Arc::new(TypX::Int);
        let lst: Typ = Arc::new(TypX::Named(Arc::new("Lst".to_string())));
        let nil: Variant = mk("nil", Arc::new(vec![]));
        let cons: Variant = mk("cons", Arc::new(vec![mk("head", int), mk("tail", lst)]));
        let lst_dt: Datatype = mk("Lst", Arc::new(vec![nil, cons]));
        let dts: Datatypes = Arc::new(vec![lst_dt]);
        assert_eq!(
            decl_to_lukb(&DeclX::Datatypes(dts)),
            "data Lst = nil | cons(head: Int, tail: Lst)\n"
        );
    }

    #[test]
    fn datatype_group_falls_back_only_the_tier2_member() {
        // A two-datatype group: a clean `Ok` one + one with a BitVec field.
        // The clean member must still render; only the Tier-2 one comments out.
        let ok: Datatype = mk("Ok", Arc::new(vec![mk("k", Arc::new(vec![] as Vec<Field>))]));
        let bad: Datatype = mk(
            "Bad",
            Arc::new(vec![mk("b", Arc::new(vec![mk("w", Arc::new(TypX::BitVec(8)))]))]),
        );
        let dts: Datatypes = Arc::new(vec![ok, bad]);
        let out = decl_to_lukb(&DeclX::Datatypes(dts));
        assert!(out.contains("data Ok = k\n"), "clean member renders: {out}");
        assert!(out.contains("# fallback (datatypes):"), "tier-2 member comments: {out}");
    }
}
