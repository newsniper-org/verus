//! `-V fip-lint`: the TRMC rewrite. vir::fip_lint finds the strongly connected components of the
//! call graph whose recursion is all tail calls or recursion modulo a constructor, and says where
//! the calls and constructors are. This module turns such a plan into source edits: the bodies
//! become a loop that writes each constructor into a `&mut` hole (destination-passing style), with
//! the loop invariant that makes the loop verify the same `ensures` and `allocates` as the
//! original. The edits are attached to the TRMC warning as a suggestion (an editor offers it as a
//! quick fix), and `-V fip-lint=fix` writes them to the source files and keeps them only if the
//! crate still verifies (see `apply_fixes`, called by main after verification succeeds).
//!
//! Nothing here is trusted: a rewrite that is wrong does not verify, and is not kept.

use crate::context::Context;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use rustc_errors::Applicability;
use rustc_hir::{FnRetTy, ItemKind, Node, PatKind};
use rustc_span::{FileName, Span};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use vir::ast::{CtorPrintStyle, Fun, FunctionX};
use vir::fip_lint::{TrmcFn, TrmcLevel, TrmcPlan, TrmcSite};

/// A replacement of `old` (bytes `lo..hi` of `path`) by `new`
#[derive(Clone, Debug)]
pub(crate) struct Edit {
    pub path: std::path::PathBuf,
    pub lo: usize,
    pub hi: usize,
    pub old: String,
    pub new: String,
}

/// The edits that rewrite one component
#[derive(Clone, Debug)]
pub(crate) struct Fix {
    pub names: Vec<String>,
    pub edits: Vec<Edit>,
}

static FIXES: Mutex<Vec<Fix>> = Mutex::new(Vec::new());

pub(crate) fn take_fixes() -> Vec<Fix> {
    std::mem::take(&mut *FIXES.lock().unwrap())
}

type Res<A> = Result<A, (Span, String)>;

struct Ctx<'a, 'tcx> {
    ctxt: &'a Context<'tcx>,
    infos: &'a HashMap<Fun, Arc<FunctionOrConstInfo<'tcx>>>,
}

/// What the rewrite needs to know about one function of the component
struct FnText {
    name: String,
    camel: String,
    /// (name, `mut`, type)
    params: Vec<(String, bool, String)>,
    ret_name: String,
    ret_typ: String,
    generics: String,
    where_clause: String,
    requires: Vec<String>,
    ensures: Vec<String>,
    decreases: Vec<String>,
    allocates: Option<String>,
    placeholder: String,
    fip: Option<bool>,
    body: Span,
    body_id: rustc_hir::BodyId,
    item: Span,
    /// indentation of the item
    indent: usize,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    fn span(&self, s: &vir::messages::Span) -> Option<Span> {
        self.ctxt.spans.from_air_span(s, Some(self.ctxt.tcx.sess.source_map()))
    }

    fn snippet(&self, s: Span) -> Res<String> {
        self.ctxt
            .tcx
            .sess
            .source_map()
            .span_to_snippet(s)
            .map_err(|_| (s, "the source of this code is not available".to_string()))
    }

    fn vir_snippet(&self, at: Span, s: &vir::messages::Span) -> Res<String> {
        let sp =
            self.span(s).ok_or((at, "the source of this code is not available".to_string()))?;
        self.snippet(sp)
    }

    /// Indentation (in columns) of the line containing `s`
    fn line_indent(&self, s: Span) -> usize {
        let sm = self.ctxt.tcx.sess.source_map();
        let loc = sm.lookup_char_pos(s.lo());
        match loc.file.get_line(loc.line - 1) {
            Some(line) => line.chars().take_while(|c| *c == ' ').count(),
            None => 0,
        }
    }

    fn fn_text(&self, f: &TrmcFn) -> Res<FnText> {
        let fx: &FunctionX = &f.function.x;
        let fspan = self.span(&f.function.span).unwrap_or(rustc_span::DUMMY_SP);
        let info = match self.infos.get(&fx.name).map(|i| &**i) {
            Some(FunctionOrConstInfo::Function(info)) => info,
            _ => return Err((fspan, "this function is not available for rewriting".into())),
        };
        let tcx = self.ctxt.tcx;
        let local = info.def_id.as_local().ok_or((fspan, "not a local function".to_string()))?;
        let parent = tcx.parent(info.def_id);
        if !matches!(tcx.def_kind(parent), rustc_hir::def::DefKind::Mod) {
            return Err((
                fspan,
                "only functions declared directly in a module are rewritten".into(),
            ));
        }
        let item = match tcx.hir_node_by_def_id(local) {
            Node::Item(item) => item,
            _ => return Err((fspan, "not a function item".into())),
        };
        let (sig, generics, body_id) = match &item.kind {
            ItemKind::Fn { sig, generics, body, .. } => (sig, generics, *body),
            _ => return Err((fspan, "not a function item".into())),
        };
        let body = tcx.hir_body(body_id);
        let mut params = Vec::new();
        for (i, p) in body.params.iter().enumerate() {
            let (name, is_mut) = match &p.pat.kind {
                PatKind::Binding(mode, _, ident, None) => {
                    (ident.to_string(), mode.1 == rustc_ast::Mutability::Mut)
                }
                _ => {
                    return Err((
                        p.pat.span,
                        "only parameters that are plain names are supported".into(),
                    ));
                }
            };
            let ty = self.snippet(sig.decl.inputs[i].span)?;
            params.push((name, is_mut, ty));
        }
        let ret_typ = match &sig.decl.output {
            FnRetTy::Return(ty) => self.snippet(ty.span)?,
            FnRetTy::DefaultReturn(_) => {
                return Err((fspan, "the function returns nothing".into()));
            }
        };
        let ret_name = fx.outer_ret.x.name.0.to_string();
        let generics_text =
            if generics.span.is_empty() { String::new() } else { self.snippet(generics.span)? };
        let where_clause = if generics.where_clause_span.is_empty() {
            String::new()
        } else {
            self.snippet(generics.where_clause_span)?
        };
        let mut requires = Vec::new();
        for e in fx.require.iter() {
            requires.push(self.vir_snippet(fspan, &e.span)?);
        }
        let mut ensures = Vec::new();
        for e in fx.ensure.0.iter() {
            ensures.push(self.vir_snippet(fspan, &e.span)?);
        }
        let mut decreases = Vec::new();
        for e in fx.decrease.iter() {
            decreases.push(self.vir_snippet(fspan, &e.span)?);
        }
        let allocates = match &fx.allocates {
            _ if !self.ctxt.cmd_line_args.alloc_check => None,
            None => None,
            // (`#[verifier::fip]` without `allocates` means `allocates 0`, with the signature's span)
            Some(e) => match self.span(&e.span) {
                Some(sp) if sp != sig.span => Some(self.snippet(sp)?),
                _ => Some("0".to_string()),
            },
        };
        let placeholder = {
            let (_, v) = &f.placeholder;
            let simple = ret_typ.chars().all(|c| c.is_alphanumeric() || c == '_' || c == ':');
            if simple { format!("{}::{}", ret_typ, v) } else { format!("<{}>::{}", ret_typ, v) }
        };
        let name = item.kind.ident().map(|i| i.to_string()).unwrap_or_default();
        let camel: String = name
            .split('_')
            .filter(|s| !s.is_empty())
            .map(|s| {
                let mut c = s.chars();
                match c.next() {
                    Some(h) => h.to_uppercase().collect::<String>() + c.as_str(),
                    None => String::new(),
                }
            })
            .collect();
        let body_span = body.value.span;
        let bs = self.snippet(body_span)?;
        if !(bs.starts_with('{') && bs.ends_with('}')) {
            return Err((fspan, "the function body is not a block".into()));
        }
        Ok(FnText {
            name,
            camel,
            params,
            ret_name,
            ret_typ,
            generics: generics_text,
            where_clause,
            requires,
            ensures,
            decreases,
            allocates,
            placeholder,
            fip: info.vattrs.fip,
            body: body_span,
            body_id,
            item: item.span,
            indent: self.line_indent(item.span),
        })
    }
}

/// Add `delta` spaces to each line of `s` after the first
fn reindent(s: &str, delta: usize) -> String {
    let pad = " ".repeat(delta);
    let mut out = String::new();
    for (i, line) in s.split('\n').enumerate() {
        if i > 0 {
            out.push('\n');
            if !line.trim().is_empty() {
                out.push_str(&pad);
            }
        }
        out.push_str(line);
    }
    out
}

/// How a site continues the loop: in a single function, by assigning its parameters; in a
/// component of several functions, by building the next state.
enum Mode<'b> {
    Single(&'b FnText),
    Multi { state: &'b str },
}

/// The HIR expressions of `body` with exactly the span `span`
fn hir_exprs_at<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: rustc_hir::BodyId,
    span: Span,
) -> Vec<&'tcx rustc_hir::Expr<'tcx>> {
    use rustc_hir::intravisit::{Visitor, walk_expr};
    struct V<'tcx> {
        span: Span,
        out: Vec<&'tcx rustc_hir::Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for V<'tcx> {
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if e.span == self.span {
                self.out.push(e);
            }
            walk_expr(self, e)
        }
    }
    let mut v = V { span, out: vec![] };
    v.visit_expr(tcx.hir_body(body).value);
    v.out
}

fn strip_hir<'tcx>(mut e: &'tcx rustc_hir::Expr<'tcx>) -> &'tcx rustc_hir::Expr<'tcx> {
    while let rustc_hir::ExprKind::DropTemps(inner) = &e.kind {
        e = inner;
    }
    e
}

/// One constructor level of a site, as written in the source
struct LevelText {
    /// The constructor's path (or `Box::new`)
    path: String,
    is_box: bool,
    style: CtorPrintStyle,
    hole: String,
    /// (field name, temporary)
    before: Vec<(String, String)>,
    after: Vec<(String, String)>,
}

fn render_site(
    cx: &Ctx,
    site: &TrmcSite,
    ft: &FnText,
    texts: &HashMap<Fun, FnText>,
    mode: &Mode,
) -> Res<(Span, String)> {
    use rustc_hir::ExprKind;
    let fspan = ft.item;
    let unavailable = |sp: Span| (sp, "the source of this code is not available".to_string());
    let span = cx.span(&site.span).ok_or(unavailable(fspan))?;
    let expr_span = cx.span(&site.expr).ok_or(unavailable(span))?;
    let callee = texts.get(&site.callee).ok_or((span, "unknown callee".to_string()))?;
    let tcx = cx.ctxt.tcx;
    let candidates = hir_exprs_at(tcx, ft.body_id, expr_span);
    let mut e = *candidates
        .iter()
        .find(|e| matches!(strip_hir(e).kind, ExprKind::Call(..) | ExprKind::Struct(..)))
        .ok_or((expr_span, "this constructor or call is not found in the source".to_string()))?;
    e = strip_hir(e);
    let ind = " ".repeat(cx.line_indent(span) + 4);
    let mut stmts: Vec<String> = Vec::new();
    let mut ntmp = 0;
    let mut levels: Vec<LevelText> = Vec::new();
    // fields before the hole, top-down (the order in which the original evaluates them)
    for l in site.levels.iter() {
        match (l, &e.kind) {
            (TrmcLevel::Box, ExprKind::Call(func, args)) if args.len() == 1 => {
                levels.push(LevelText {
                    path: cx.snippet(func.span)?,
                    is_box: true,
                    style: CtorPrintStyle::Parens,
                    hole: "0".into(),
                    before: vec![],
                    after: vec![],
                });
                e = strip_hir(&args[0]);
            }
            (TrmcLevel::Ctor { hole, style, .. }, ExprKind::Call(func, args)) => {
                let idx: usize =
                    hole.parse().map_err(|_| (e.span, "unexpected constructor".to_string()))?;
                let mut before = Vec::new();
                for (i, a) in args[..idx].iter().enumerate() {
                    let t = format!("__trmc_t{}", ntmp);
                    ntmp += 1;
                    stmts.push(format!("let {} = {};", t, cx.snippet(a.span)?));
                    before.push((i.to_string(), t));
                }
                levels.push(LevelText {
                    path: cx.snippet(func.span)?,
                    is_box: false,
                    style: *style,
                    hole: hole.to_string(),
                    before,
                    after: vec![],
                });
                e = strip_hir(args.get(idx).ok_or((e.span, "unexpected constructor".to_string()))?);
            }
            (
                TrmcLevel::Ctor { hole, style, .. },
                ExprKind::Struct(qpath, fields, rustc_hir::StructTailExpr::None),
            ) => {
                let idx = fields
                    .iter()
                    .position(|f| f.ident.as_str() == hole.as_str())
                    .ok_or((e.span, "unexpected struct literal".to_string()))?;
                let mut before = Vec::new();
                for f in fields[..idx].iter() {
                    let t = format!("__trmc_t{}", ntmp);
                    ntmp += 1;
                    stmts.push(format!("let {} = {};", t, cx.snippet(f.expr.span)?));
                    before.push((f.ident.to_string(), t));
                }
                levels.push(LevelText {
                    path: cx.snippet(qpath.span())?,
                    is_box: false,
                    style: *style,
                    hole: hole.to_string(),
                    before,
                    after: vec![],
                });
                e = strip_hir(&fields[idx].expr);
            }
            _ => return Err((e.span, "unexpected form of constructor".into())),
        }
    }
    // the arguments of the recursive call
    let call_args = match &e.kind {
        ExprKind::Call(_, args) => args,
        _ => return Err((e.span, "the recursive call is not a plain function call".into())),
    };
    let mut args = Vec::new();
    for (i, a) in call_args.iter().enumerate() {
        let name = format!("__trmc_a{}", i);
        let ty = &callee.params.get(i).ok_or((span, "argument count mismatch".to_string()))?.2;
        stmts.push(format!("let {}: {} = {};", name, ty, cx.snippet(a.span)?));
        args.push(name);
    }
    // fields after the hole, bottom-up
    {
        let mut e2 = strip_hir(
            *candidates
                .iter()
                .find(|e| matches!(strip_hir(e).kind, ExprKind::Call(..) | ExprKind::Struct(..)))
                .unwrap(),
        );
        let mut afters: Vec<Vec<(String, String, Span)>> = Vec::new();
        for l in site.levels.iter() {
            let mut v = Vec::new();
            match (l, &e2.kind) {
                (TrmcLevel::Box, ExprKind::Call(_, args)) => e2 = strip_hir(&args[0]),
                (TrmcLevel::Ctor { hole, .. }, ExprKind::Call(_, args)) => {
                    let idx: usize = hole.parse().unwrap();
                    for (i, a) in args.iter().enumerate().skip(idx + 1) {
                        v.push((i.to_string(), String::new(), a.span));
                    }
                    e2 = strip_hir(&args[idx]);
                }
                (TrmcLevel::Ctor { hole, .. }, ExprKind::Struct(_, fields, _)) => {
                    let idx =
                        fields.iter().position(|f| f.ident.as_str() == hole.as_str()).unwrap();
                    for f in fields[idx + 1..].iter() {
                        v.push((f.ident.to_string(), String::new(), f.expr.span));
                    }
                    e2 = strip_hir(&fields[idx].expr);
                }
                _ => {}
            }
            afters.push(v);
        }
        for (li, v) in afters.iter().enumerate().rev() {
            for (field, _, sp) in v.iter() {
                let t = format!("__trmc_t{}", ntmp);
                ntmp += 1;
                stmts.push(format!("let {} = {};", t, cx.snippet(*sp)?));
                levels[li].after.push((field.clone(), t));
            }
        }
    }
    // rebuild the constructor with the placeholder in the hole
    fn rebuild(levels: &[LevelText], placeholder: &str) -> String {
        match levels.first() {
            None => placeholder.to_string(),
            Some(l) if l.is_box => format!("{}({})", l.path, rebuild(&levels[1..], placeholder)),
            Some(l) => {
                let inner = rebuild(&levels[1..], placeholder);
                let mut fields: Vec<(String, String)> = l.before.clone();
                fields.push((l.hole.clone(), inner));
                fields.extend(l.after.iter().cloned());
                match l.style {
                    CtorPrintStyle::Braces => format!(
                        "{} {{ {} }}",
                        l.path,
                        fields
                            .iter()
                            .map(|(f, v)| format!("{}: {}", f, v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    _ => format!(
                        "{}({})",
                        l.path,
                        fields.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>().join(", ")
                    ),
                }
            }
        }
    }
    // move the hole to the field: a nested pattern for consecutive constructors, then a
    // dereference for each box
    fn advance(levels: &[LevelText], scrutinee: &str) -> String {
        fn pat(levels: &[LevelText]) -> (String, usize) {
            match levels.first() {
                Some(l) if !l.is_box => {
                    let (inner, n) = pat(&levels[1..]);
                    let p = match l.style {
                        CtorPrintStyle::Braces => {
                            format!("{} {{ {}: {}, .. }}", l.path, l.hole, inner)
                        }
                        _ => {
                            let idx: usize = l.hole.parse().unwrap_or(0);
                            format!("{}({}{}, ..)", l.path, "_, ".repeat(idx), inner)
                        }
                    };
                    (p, n + 1)
                }
                _ => ("__trmc_h".to_string(), 0),
            }
        }
        let (p, n) = pat(levels);
        let rest = &levels[n..];
        let boxes = rest.iter().take_while(|l| l.is_box).count();
        let deref = format!("&mut *{}__trmc_h", "*".repeat(boxes));
        let after = &rest[boxes..];
        let arm = if after.is_empty() { deref } else { advance(after, &deref) };
        format!("match {} {{ {} => {}, _ => vstd::pervasive::unreached() }}", scrutinee, p, arm)
    }
    let is_ctor = !levels.is_empty();
    if is_ctor {
        stmts.push(format!(
            "core::mem::forget(core::mem::replace(__trmc_hole, {}));",
            rebuild(&levels, &callee.placeholder)
        ));
    }
    match mode {
        Mode::Single(f) => {
            if is_ctor {
                stmts.push(format!("__trmc_hole = {};", advance(&levels, "__trmc_hole")));
            }
            for (i, (p, _, _)) in f.params.iter().enumerate() {
                stmts.push(format!("{} = {};", p, args[i]));
            }
        }
        Mode::Multi { state } => {
            let hole = if is_ctor {
                stmts.push(format!("let __trmc_next = {};", advance(&levels, "__trmc_hole")));
                "__trmc_next"
            } else {
                "__trmc_hole"
            };
            let mut fields = args.clone();
            fields.push(hole.to_string());
            stmts.push(format!("__trmc_st = {}::{}({});", state, callee.camel, fields.join(", ")));
        }
    }
    stmts.push("continue '__trmc;".to_string());
    let close = " ".repeat(ind.len() - 4);
    let text = format!(
        "{{\n{}\n{}}}",
        stmts.iter().map(|s| format!("{}{}", ind, s)).collect::<Vec<_>>().join("\n"),
        close
    );
    Ok((span, text))
}

/// The body of `f` with its sites and returns replaced
fn render_body(
    cx: &Ctx,
    f: &TrmcFn,
    ft: &FnText,
    texts: &HashMap<Fun, FnText>,
    mode: &Mode,
) -> Res<String> {
    let fspan = ft.item;
    // (span, Some(text)) for sites; (span, None) with value span for returns
    enum E {
        Site(String),
        Return(Span),
    }
    let mut edits: Vec<(Span, E)> = Vec::new();
    for s in f.sites.iter() {
        let (span, text) = render_site(cx, s, ft, texts, mode)?;
        edits.push((span, E::Site(text)));
    }
    for (r, v) in f.returns.iter() {
        let rs =
            cx.span(r).ok_or((fspan, "the source of a `return` is not available".to_string()))?;
        let text = cx.snippet(rs)?;
        if !text.trim_start().starts_with("return") {
            return Err((rs, "this returns early (e.g. `?`); only `return e` is supported".into()));
        }
        let vs = cx.span(v).ok_or((rs, "the source of a `return` is not available".to_string()))?;
        if vs == rs {
            return Err((rs, "`return` without a value".into()));
        }
        edits.push((rs, E::Return(vs)));
    }
    // sites must not contain other edits (their parts are copied as written)
    for (a, ea) in edits.iter() {
        if let E::Site(_) = ea {
            for (b, _) in edits.iter() {
                if a != b && a.contains(*b) {
                    return Err((
                        *b,
                        "this `return` is inside a recursive call's arguments or constructor"
                            .into(),
                    ));
                }
            }
        }
    }
    fn render(cx: &Ctx, span: Span, edits: &[(Span, E)]) -> Res<String> {
        let mut inner: Vec<&(Span, E)> = edits
            .iter()
            .filter(|(s, _)| span.contains(*s) && *s != span)
            .filter(|(s, _)| {
                !edits
                    .iter()
                    .any(|(t, _)| t != s && *t != span && span.contains(*t) && t.contains(*s))
            })
            .collect();
        inner.sort_by_key(|(s, _)| s.lo());
        let mut out = String::new();
        let mut pos = span.lo();
        for (s, e) in inner {
            out.push_str(&cx.snippet(span.with_lo(pos).with_hi(s.lo()))?);
            match e {
                E::Site(t) => out.push_str(t),
                E::Return(v) => {
                    let value = render(cx, *v, edits)?;
                    out.push_str(&format!(
                        "{{ core::mem::forget(core::mem::replace(__trmc_hole, {})); break '__trmc; }}",
                        value
                    ));
                }
            }
            pos = s.hi();
        }
        out.push_str(&cx.snippet(span.with_lo(pos))?);
        Ok(out)
    }
    render(cx, ft.body, &edits)
}

fn param_list(f: &FnText) -> String {
    f.params.iter().map(|(n, _, t)| format!("{}: {}", n, t)).collect::<Vec<_>>().join(", ")
}

fn arg_list(f: &FnText, prefix: &str) -> String {
    f.params.iter().map(|(n, _, _)| format!("{}{}", prefix, n)).collect::<Vec<_>>().join(", ")
}

fn conj(v: &Vec<String>) -> String {
    if v.is_empty() {
        "true".to_string()
    } else {
        v.iter().map(|e| format!("({})", e)).collect::<Vec<_>>().join(" && ")
    }
}

fn with_where(f: &FnText) -> String {
    if f.where_clause.is_empty() { String::new() } else { format!("\n{}", f.where_clause) }
}

/// The spec functions that name `f`'s precondition, postcondition and allocation bound
fn spec_items(f: &FnText) -> String {
    let mut out = String::new();
    if !f.requires.is_empty() {
        out.push_str(&format!(
            "spec fn {}_trmc_req{}({}) -> bool{} {{\n    {}\n}}\n\n",
            f.name,
            f.generics,
            param_list(f),
            with_where(f),
            conj(&f.requires)
        ));
    }
    if !f.ensures.is_empty() {
        let mut ps = param_list(f);
        if !ps.is_empty() {
            ps.push_str(", ");
        }
        out.push_str(&format!(
            "spec fn {}_trmc_ens{}({}{}: {}) -> bool{} {{\n    {}\n}}\n\n",
            f.name,
            f.generics,
            ps,
            f.ret_name,
            f.ret_typ,
            with_where(f),
            conj(&f.ensures)
        ));
    }
    if let Some(a) = &f.allocates {
        out.push_str(&format!(
            "spec fn {}_trmc_alloc{}({}) -> int{} {{\n    ({}) as int\n}}\n\n",
            f.name,
            f.generics,
            param_list(f),
            with_where(f),
            a
        ));
    }
    out
}

fn fip_attr(fip: Option<bool>) -> &'static str {
    match fip {
        Some(true) => "#[verifier::fip(strict)]\n",
        Some(false) => "#[verifier::fip]\n",
        None => "",
    }
}

fn file_edit(cx: &Ctx, span: Span, new: String) -> Res<Edit> {
    let sm = cx.ctxt.tcx.sess.source_map();
    let lo = sm.lookup_byte_offset(span.lo());
    let hi = sm.lookup_byte_offset(span.hi());
    let path = match &lo.sf.name {
        FileName::Real(r) => {
            r.local_path().map(|p| p.to_path_buf()).ok_or((span, "not a local file".to_string()))?
        }
        _ => return Err((span, "the function is not in a source file".into())),
    };
    Ok(Edit { path, lo: lo.pos.0 as usize, hi: hi.pos.0 as usize, old: cx.snippet(span)?, new })
}

/// The edits for one plan, as (span, replacement) pairs
fn render_plan(cx: &Ctx, plan: &TrmcPlan) -> Res<Vec<(Span, String)>> {
    let mut texts: HashMap<Fun, FnText> = HashMap::new();
    for f in plan.fns.iter() {
        texts.insert(f.function.x.name.clone(), cx.fn_text(f)?);
    }
    let mut out: Vec<(Span, String)> = Vec::new();
    if plan.fns.len() == 1 {
        let f = &plan.fns[0];
        let ft = &texts[&f.function.x.name];
        let body = render_body(cx, f, ft, &texts, &Mode::Single(ft))?;
        let i0 = " ".repeat(ft.indent + 4);
        let i1 = " ".repeat(ft.indent + 8);
        let i2 = " ".repeat(ft.indent + 12);
        let ps = arg_list(ft, "");
        let ps0 = arg_list(ft, "__trmc_");
        let comma = |s: &str| if s.is_empty() { String::new() } else { format!("{}, ", s) };
        let mut inv: Vec<String> = Vec::new();
        let mut ens: Vec<String> = Vec::new();
        if !ft.requires.is_empty() {
            inv.push(format!("{}_trmc_req({})", ft.name, ps));
        }
        if !ft.ensures.is_empty() {
            inv.push(format!(
                "{n}_trmc_ens({}*final(__trmc_hole))\n{i2}    ==> {n}_trmc_ens({}after_borrow(__trmc_root))",
                comma(&ps),
                comma(&ps0),
                n = ft.name,
                i2 = i2
            ));
            ens.push(format!("{}_trmc_ens({}after_borrow(__trmc_root))", ft.name, comma(&ps0)));
        }
        if ft.allocates.is_some() {
            inv.push(format!(
                "allocated() + {n}_trmc_alloc({}) <= {n}_trmc_alloc({})",
                ps,
                ps0,
                n = ft.name
            ));
            ens.push(format!("allocated() <= {}_trmc_alloc({})", ft.name, ps0));
        }
        let mut s = String::new();
        s.push_str("{\n");
        for (p, _, _) in ft.params.iter() {
            s.push_str(&format!("{}let ghost __trmc_{} = {};\n", i0, p, p));
        }
        for (p, _, _) in ft.params.iter() {
            s.push_str(&format!("{}let mut {} = {};\n", i0, p, p));
        }
        s.push_str(&format!("{}let mut __trmc_root = {};\n", i0, ft.placeholder));
        s.push_str(&format!("{}let mut __trmc_hole = &mut __trmc_root;\n", i0));
        s.push_str(&format!("{}'__trmc: loop\n", i0));
        if !inv.is_empty() {
            s.push_str(&format!("{}invariant_except_break\n", i1));
            for x in inv.iter() {
                s.push_str(&format!("{}{},\n", i2, x));
            }
        }
        if !ens.is_empty() {
            s.push_str(&format!("{}ensures\n", i1));
            for x in ens.iter() {
                s.push_str(&format!("{}{},\n", i2, x));
            }
        }
        s.push_str(&format!("{}decreases {}\n", i1, ft.decreases.join(", ")));
        s.push_str(&format!("{}{{\n", i0));
        // (the body's statements move from `indent + 4` to `indent + 12`)
        let delta = 8;
        s.push_str(&format!("{}let __trmc_value = {};\n", i1, reindent(&body, delta)));
        s.push_str(&format!(
            "{}core::mem::forget(core::mem::replace(__trmc_hole, __trmc_value));\n",
            i1
        ));
        s.push_str(&format!("{}break '__trmc;\n", i1));
        s.push_str(&format!("{}}}\n", i0));
        s.push_str(&format!("{}__trmc_root\n", i0));
        s.push_str(&format!("{}}}", " ".repeat(ft.indent)));
        out.push((ft.body, s));
        let items = spec_items(ft);
        if !items.is_empty() {
            let pad = " ".repeat(ft.indent);
            let items = items
                .trim_end()
                .split('\n')
                .map(|l| if l.is_empty() { String::new() } else { format!("{}{}", pad, l) })
                .collect::<Vec<_>>()
                .join("\n");
            out.push((ft.item.shrink_to_hi(), format!("\n\n{}", items)));
        }
        return Ok(out);
    }

    // several functions: one state enum, one loop in a helper, and each function calls it
    let fts: Vec<&FnText> = plan.fns.iter().map(|f| &texts[&f.function.x.name]).collect();
    if fts.iter().any(|f| f.generics != fts[0].generics || f.where_clause != fts[0].where_clause) {
        return Err((
            fts[0].item,
            "mutually recursive functions must have the same generic parameters to be rewritten"
                .into(),
        ));
    }
    let state = format!("{}Trmc", fts.iter().map(|f| f.camel.clone()).collect::<String>());
    let helper =
        format!("{}_trmc", fts.iter().map(|f| f.name.clone()).collect::<Vec<_>>().join("_"));
    let gen_names: Vec<String> = {
        let mut v = Vec::new();
        for (i, f) in fts.iter().enumerate() {
            for j in 0..f.params.len() {
                v.push(format!("P{}_{}", i, j));
            }
            v.push(format!("H{}", i));
        }
        v
    };
    let state_typ = {
        let mut args = Vec::new();
        for f in fts.iter() {
            for (_, _, t) in f.params.iter() {
                args.push(t.clone());
            }
            args.push(format!("&mut {}", f.ret_typ));
        }
        format!("{}<{}>", state, args.join(", "))
    };
    let generics = fts[0].generics.clone();
    let wc = with_where(fts[0]);
    let any_ens = fts.iter().any(|f| !f.ensures.is_empty());
    let any_req = fts.iter().any(|f| !f.requires.is_empty());
    let any_alloc = fts[0].allocates.is_some();
    let arm_pat = |f: &FnText, hole: &str| {
        let mut ps: Vec<String> = f.params.iter().map(|(n, _, _)| n.clone()).collect();
        ps.push(hole.to_string());
        format!("{}::{}({})", state, f.camel, ps.join(", "))
    };
    let comma = |s: String| if s.is_empty() { s } else { format!("{}, ", s) };
    let mut items = String::new();
    // the state
    {
        let mut variants = Vec::new();
        let mut k = 0;
        for (i, f) in fts.iter().enumerate() {
            let mut fs = Vec::new();
            for _ in f.params.iter() {
                fs.push(gen_names[k].clone());
                k += 1;
            }
            fs.push(gen_names[k].clone());
            k += 1;
            let _ = i;
            variants.push(format!("    {}({}),", f.camel, fs.join(", ")));
        }
        items.push_str(&format!(
            "#[allow(non_camel_case_types)]\nenum {}<{}> {{\n{}\n}}\n\n",
            state,
            gen_names.join(", "),
            variants.join("\n")
        ));
    }
    for f in fts.iter() {
        items.push_str(&spec_items(f));
    }
    let state_fn = |name: &str, ret: &str, per: &dyn Fn(&FnText) -> String, prophetic: bool| {
        let arms: Vec<String> = fts
            .iter()
            .map(|f| {
                format!(
                    "        {} => {},",
                    arm_pat(f, if prophetic { "__trmc_h" } else { "_" }),
                    per(f)
                )
            })
            .collect();
        format!(
            "{}spec fn {}{}(__trmc_st: {}) -> {}{} {{\n    match __trmc_st {{\n{}\n    }}\n}}\n\n",
            if prophetic { "#[verifier::prophetic]\n" } else { "" },
            name,
            generics,
            state_typ,
            ret,
            wc,
            arms.join("\n")
        )
    };
    if any_req {
        items.push_str(&state_fn(
            &format!("{}_req", helper),
            "bool",
            &|f| {
                if f.requires.is_empty() {
                    "true".into()
                } else {
                    format!("{}_trmc_req({})", f.name, arg_list(f, ""))
                }
            },
            false,
        ));
    }
    if any_ens {
        items.push_str(&state_fn(
            &format!("{}_ens", helper),
            "bool",
            &|f| {
                if f.ensures.is_empty() {
                    "true".into()
                } else {
                    format!("{}_trmc_ens({}*final(__trmc_h))", f.name, comma(arg_list(f, "")))
                }
            },
            true,
        ));
    }
    if any_alloc {
        items.push_str(&state_fn(
            &format!("{}_alloc", helper),
            "int",
            &|f| format!("{}_trmc_alloc({})", f.name, arg_list(f, "")),
            false,
        ));
    }
    // the helper
    {
        let fip = fts.iter().filter_map(|f| f.fip).max();
        let mut s = String::new();
        s.push_str(fip_attr(fip));
        s.push_str(&format!("fn {}{}(__trmc_st0: {}){}\n", helper, generics, state_typ, wc));
        if any_req {
            s.push_str(&format!("    requires\n        {}_req(__trmc_st0),\n", helper));
        }
        if any_ens {
            s.push_str(&format!("    ensures\n        {}_ens(__trmc_st0),\n", helper));
        }
        if any_alloc {
            s.push_str(&format!("    allocates {}_alloc(__trmc_st0)\n", helper));
        }
        s.push_str("{\n    let mut __trmc_st = __trmc_st0;\n    '__trmc: loop\n");
        let mut inv = Vec::new();
        let mut ens = Vec::new();
        if any_req {
            inv.push(format!("{}_req(__trmc_st)", helper));
        }
        if any_ens {
            inv.push(format!("{h}_ens(__trmc_st) ==> {h}_ens(__trmc_st0)", h = helper));
            ens.push(format!("{}_ens(__trmc_st0)", helper));
        }
        if any_alloc {
            inv.push(format!(
                "allocated() + {h}_alloc(__trmc_st) <= {h}_alloc(__trmc_st0)",
                h = helper
            ));
            ens.push(format!("allocated() <= {}_alloc(__trmc_st0)", helper));
        }
        if !inv.is_empty() {
            s.push_str("        invariant_except_break\n");
            for x in inv.iter() {
                s.push_str(&format!("            {},\n", x));
            }
        }
        if !ens.is_empty() {
            s.push_str("        ensures\n");
            for x in ens.iter() {
                s.push_str(&format!("            {},\n", x));
            }
        }
        s.push_str("        decreases match __trmc_st {\n");
        for f in fts.iter() {
            s.push_str(&format!("            {} => {},\n", arm_pat(f, "_"), f.decreases[0]));
        }
        s.push_str("        }\n    {\n        match __trmc_st {\n");
        for (f, ft) in plan.fns.iter().zip(fts.iter()) {
            let body = render_body(cx, f, ft, &texts, &Mode::Multi { state: &state })?;
            let mut ps: Vec<String> = ft
                .params
                .iter()
                .map(|(n, m, _)| if *m { format!("mut {}", n) } else { n.clone() })
                .collect();
            ps.push("__trmc_hole".to_string());
            s.push_str(&format!("            {}::{}({}) => {{\n", state, ft.camel, ps.join(", ")));
            let delta = 16usize.saturating_sub(ft.indent);
            s.push_str(&format!(
                "                let __trmc_value = {};\n",
                reindent(&body, delta)
            ));
            s.push_str("                core::mem::forget(core::mem::replace(__trmc_hole, __trmc_value));\n");
            s.push_str("                break '__trmc;\n            }\n");
        }
        s.push_str("        }\n    }\n}\n");
        items.push_str(&s);
    }
    // each function starts the loop in its state
    for ft in fts.iter() {
        let i0 = " ".repeat(ft.indent + 4);
        let mut args = arg_list(ft, "");
        args = comma(args);
        let s = format!(
            "{{\n{i0}let mut __trmc_root = {};\n{i0}{}({}::{}({}&mut __trmc_root));\n{i0}__trmc_root\n{}}}",
            ft.placeholder,
            helper,
            state,
            ft.camel,
            args,
            " ".repeat(ft.indent),
            i0 = i0
        );
        out.push((ft.body, s));
    }
    let last = fts.iter().max_by_key(|f| f.item.hi()).unwrap();
    let pad = " ".repeat(last.indent);
    let items = items
        .trim_end()
        .split('\n')
        .map(|l| if l.is_empty() { String::new() } else { format!("{}{}", pad, l) })
        .collect::<Vec<_>>()
        .join("\n");
    out.push((last.item.shrink_to_hi(), format!("\n\n{}", items)));
    Ok(out)
}

/// Report the TRMC components: a warning with the rewrite as a suggestion, or why there is none.
/// With `fix`, also record the edits for `apply_fixes`.
pub(crate) fn report<'tcx>(
    ctxt: &Context<'tcx>,
    infos: &HashMap<Fun, Arc<FunctionOrConstInfo<'tcx>>>,
    krate: &vir::ast::Krate,
    fix: bool,
) {
    let local = ctxt.crate_name.clone();
    let is_local = |f: &Fun| f.path.krate == local;
    let cx = Ctx { ctxt, infos };
    let dcx = ctxt.tcx.dcx();
    for r in vir::fip_lint::trmc_plans(krate, &is_local) {
        match r {
            Err(b) => {
                if let Some(sp) = cx.span(&b.span) {
                    dcx.struct_span_warn(
                        sp,
                        format!("-V fip-lint: this recursion modulo a constructor cannot be rewritten into a loop automatically: {}", b.reason),
                    )
                    .emit();
                }
            }
            Ok(plan) => {
                let names: Vec<String> = plan
                    .fns
                    .iter()
                    .map(|f| vir::ast_util::fun_as_friendly_rust_name(&f.function.x.name))
                    .collect();
                let first = cx.span(&plan.fns[0].function.span).unwrap_or(rustc_span::DUMMY_SP);
                match render_plan(&cx, &plan) {
                    Err((sp, reason)) => {
                        dcx.struct_span_warn(
                            if sp.is_dummy() { first } else { sp },
                            format!("-V fip-lint: this recursion modulo a constructor cannot be rewritten into a loop automatically: {}", reason),
                        )
                        .emit();
                    }
                    Ok(parts) => {
                        let mut edits = Vec::new();
                        let mut ok = true;
                        for (sp, t) in parts.iter() {
                            match file_edit(&cx, *sp, t.clone()) {
                                Ok(e) => edits.push(e),
                                Err(_) => ok = false,
                            }
                        }
                        let msg = format!(
                            "-V fip-lint: `{}` can be rewritten into a loop that runs in constant stack space (tail recursion modulo a constructor); run with `-V fip-lint=fix` to rewrite it, or apply the suggestion",
                            names.join("`, `")
                        );
                        dcx.struct_span_warn(first, msg)
                            .with_multipart_suggestion(
                                "rewrite the recursion into a loop that keeps a `&mut` hole",
                                parts,
                                Applicability::MaybeIncorrect,
                            )
                            .emit();
                        if fix && ok {
                            FIXES.lock().unwrap().push(Fix { names, edits });
                        }
                    }
                }
            }
        }
    }
}

fn apply_edits(original: &str, edits: &[&Edit]) -> Option<String> {
    let mut es: Vec<&&Edit> = edits.iter().collect();
    es.sort_by_key(|e| std::cmp::Reverse(e.lo));
    let mut s = original.to_string();
    for e in es {
        if s.get(e.lo..e.hi) != Some(e.old.as_str()) {
            return None;
        }
        s.replace_range(e.lo..e.hi, &e.new);
    }
    Some(s)
}

/// Write the fixes to the source files, one component at a time, keeping each only if the crate
/// still verifies (checked by running this verifier again, with the same arguments but without
/// `=fix`)
pub fn apply_fixes(args_without_fix: &[String]) {
    let fixes = take_fixes();
    if fixes.is_empty() {
        return;
    }
    let mut originals: HashMap<std::path::PathBuf, String> = HashMap::new();
    for f in fixes.iter() {
        for e in f.edits.iter() {
            if !originals.contains_key(&e.path) {
                match std::fs::read_to_string(&e.path) {
                    Ok(s) => {
                        originals.insert(e.path.clone(), s);
                    }
                    Err(err) => {
                        eprintln!(
                            "warning: -V fip-lint=fix: cannot read {}: {}",
                            e.path.display(),
                            err
                        );
                        return;
                    }
                }
            }
        }
    }
    let exe = match std::env::current_exe() {
        Ok(e) => e,
        Err(err) => {
            eprintln!("warning: -V fip-lint=fix: cannot find the verifier executable: {}", err);
            return;
        }
    };
    let write = |kept: &[&Fix]| -> bool {
        for (path, orig) in originals.iter() {
            let edits: Vec<&Edit> =
                kept.iter().flat_map(|f| f.edits.iter()).filter(|e| &e.path == path).collect();
            match apply_edits(orig, &edits) {
                Some(s) => {
                    if std::fs::write(path, s).is_err() {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    };
    let mut kept: Vec<&Fix> = Vec::new();
    for f in fixes.iter() {
        let mut trial = kept.clone();
        trial.push(f);
        let verified = write(&trial)
            && std::process::Command::new(&exe)
                .args(args_without_fix)
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
        if verified {
            eprintln!(
                "note: -V fip-lint=fix: rewrote `{}` into a loop (it verifies)",
                f.names.join("`, `")
            );
            kept.push(f);
        } else {
            eprintln!(
                "warning: -V fip-lint=fix: did not keep the rewrite of `{}`: the rewritten code does not verify",
                f.names.join("`, `")
            );
        }
    }
    if !write(&kept) {
        // restore everything
        for (path, orig) in originals.iter() {
            let _ = std::fs::write(path, orig);
        }
        eprintln!(
            "warning: -V fip-lint=fix: could not write the rewritten files; restored the originals"
        );
    }
}
