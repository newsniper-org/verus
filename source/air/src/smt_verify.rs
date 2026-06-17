use crate::ast::{
    Axiom, BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, StmtX, TypX,
    UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_nat, mk_not};
use crate::context::{
    AbductiveCandidate, AssertionInfo, AxiomInfo, Context, ContextState, SmtSolver, ValidityResult,
};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
use crate::messages::{ArcDynMessage, Diagnostics};
pub use crate::model::{Model, ModelDef};
use std::collections::HashMap;
use std::sync::Arc;

fn label_asserts<'ctx>(
    context: &mut Context,
    infos: &mut Vec<AssertionInfo>,
    axiom_infos: &mut Vec<AxiomInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(op @ BinaryOp::Implies, lhs, rhs)
        | ExprX::Binary(op @ BinaryOp::Eq, lhs, rhs) => {
            // asserts are on rhs of =>
            // (slight hack to also allow rhs of == for quantified function definitions)
            Arc::new(ExprX::Binary(
                op.clone(),
                lhs.clone(),
                label_asserts(context, infos, axiom_infos, rhs),
            ))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, axiom_infos, expr));
            }
            Arc::new(ExprX::Multi(*op, Arc::new(exprs_vec)))
        }
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, _, _, _) => Arc::new(ExprX::Bind(
                bind.clone(),
                label_asserts(context, infos, axiom_infos, body),
            )),
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(assert_id, error, filter, expr) => {
            let label = Arc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info = AssertionInfo {
                assert_id: assert_id.clone(),
                error: error.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
                disabled: false,
            };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        ExprX::LabeledAxiom(labels, filter, expr) => {
            let count = context.axiom_infos_count;
            context.axiom_infos_count += 1;
            let label = Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let axiom_info = AxiomInfo {
                labels: labels.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
            };
            axiom_infos.push(axiom_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        _ => expr.clone(),
    }
}

/// In SMT-LIB, functions applied to zero arguments are considered constants.
/// REVIEW: maybe AIR should follow this design for consistency.
/// Parses the single-line abductive payload that `lu-smt` emits on
/// the line right after a literal `abductive` verdict.  Schema is
/// pinned by Y4 `smt-cross-validation-tracker.md` §9 and matches
/// the engine's `adsmt-abduce::rank::RankedCandidate` +
/// `Candidate { hypotheses, explanations, sources }` 1:1.  All
/// fields are required (`null` is only allowed inside the
/// `explanations` array's per-hypothesis slot).
fn parse_abductive_candidates_line(line: &str) -> Result<Vec<AbductiveCandidate>, String> {
    let root: serde_json::Value =
        serde_json::from_str(line).map_err(|e| format!("not valid JSON: {}", e))?;
    let array = root
        .get("abductive_candidates")
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| "top-level object missing `abductive_candidates` array".to_string())?;
    array
        .iter()
        .map(|entry| -> Result<AbductiveCandidate, String> {
            let rank = entry
                .get("rank")
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| "candidate missing `rank` (non-negative integer)".to_string())?
                as u32;
            let score = entry
                .get("score")
                .and_then(serde_json::Value::as_f64)
                .ok_or_else(|| "candidate missing `score` (number)".to_string())?;
            let hypotheses = entry
                .get("hypotheses")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "candidate missing `hypotheses` array".to_string())?
                .iter()
                .map(|h| {
                    h.as_str()
                        .map(str::to_string)
                        .ok_or_else(|| "hypothesis entry is not a string".to_string())
                })
                .collect::<Result<Vec<_>, _>>()?;
            let explanations = entry
                .get("explanations")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "candidate missing `explanations` array".to_string())?
                .iter()
                .map(|e| -> Result<Option<String>, String> {
                    if e.is_null() {
                        Ok(None)
                    } else {
                        e.as_str()
                            .map(|s| Some(s.to_string()))
                            .ok_or_else(|| {
                                "explanation entry is neither a string nor null".to_string()
                            })
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let sources = entry
                .get("sources")
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| "candidate missing `sources` array".to_string())?
                .iter()
                .map(|s| {
                    s.as_str()
                        .map(str::to_string)
                        .ok_or_else(|| "source entry is not a string".to_string())
                })
                .collect::<Result<Vec<_>, _>>()?;
            if hypotheses.len() != explanations.len() || hypotheses.len() != sources.len() {
                return Err(format!(
                    "candidate lock-step lists out of sync: hypotheses={} explanations={} sources={}",
                    hypotheses.len(),
                    explanations.len(),
                    sources.len(),
                ));
            }
            Ok(AbductiveCandidate {
                rank,
                score,
                hypotheses,
                explanations,
                sources,
            })
        })
        .collect()
}

fn elim_zero_args_expr(expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(expr, &mut |expr| match &**expr {
        ExprX::Apply(x, es) if es.len() == 0 => Arc::new(ExprX::Var(x.clone())),
        _ => expr.clone(),
    })
}

pub(crate) fn smt_add_decl<'ctx>(context: &mut Context, decl: &Decl) {
    match &**decl {
        DeclX::Sort(_) | DeclX::Datatypes(_) | DeclX::Const(_, _) | DeclX::Fun(_, _, _) => {
            context.smt_log.log_decl(decl);
        }
        DeclX::Var(_, _) => {}
        DeclX::Axiom(Axiom { named, expr }) => {
            let expr = elim_zero_args_expr(expr);
            let mut infos: Vec<AssertionInfo> = Vec::new();
            let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
            let labeled_expr = label_asserts(context, &mut infos, &mut axiom_infos, &expr);
            for info in axiom_infos {
                crate::typecheck::add_decl(context, &info.decl, true).unwrap();
                context
                    .axiom_infos
                    .insert(info.label.clone(), Arc::new(info.clone()))
                    .expect("internal error: duplicate assert_info");
                smt_add_decl(context, &info.decl);
            }
            context.smt_log.log_assert(named, &labeled_expr);
        }
    }
}

impl SmtSolver {
    pub fn reason_unknown_canceled_str(&self) -> &str {
        match self {
            SmtSolver::Z3 | SmtSolver::OxiZ => "(:reason-unknown \"canceled\")",
            SmtSolver::Cvc5 => "(:reason-unknown resourceout)",
            SmtSolver::Adsmt => "(:reason-unknown \"canceled\")",
        }
    }

    pub fn reason_unknown_incomplete_str(&self) -> &str {
        match self {
            SmtSolver::Z3 | SmtSolver::OxiZ => "(:reason-unknown \"(incomplete",
            SmtSolver::Cvc5 => "(:reason-unknown incomplete)",
            SmtSolver::Adsmt => "(:reason-unknown \"(incomplete",
        }
    }
}

pub type ReportLongRunning<'a> =
    (std::time::Duration, Box<dyn FnMut(std::time::Duration, bool) -> () + 'a>);

const GET_VERSION_RESPONSE_PREFIX: &str = "(:version";

pub(crate) fn smt_check_assertion<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
    only_check_earlier: bool,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    let disabled_expr = if only_check_earlier {
        // disable all labels that come after the first known error
        let mut disabled: Vec<Expr> = Vec::new();
        let mut found_disabled = false;
        let mut found_enabled = false;
        for info in infos.iter_mut() {
            if found_disabled && !info.disabled {
                info.disabled = true;
                disabled.push(mk_not(&ident_var(&info.label)));
            }
            if info.disabled {
                found_disabled = true;
            } else {
                found_enabled = true;
            }
        }
        if only_check_earlier && !found_enabled {
            // no earlier assertions to check
            return ValidityResult::Valid(crate::context::UsageInfo::None);
        }
        Some(mk_and(&disabled))
    } else {
        None
    };

    context.smt_log.log_get_info("version");
    let smt_init_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let early_smt_output = context.get_smt_process().send_commands(smt_data);
    context.time_smt_init += smt_init_start_time.elapsed();
    for line in early_smt_output {
        if line.starts_with(GET_VERSION_RESPONSE_PREFIX) {
            if let Some(expected_version) = &context.expected_solver_version {
                let value: &str = &line[GET_VERSION_RESPONSE_PREFIX.len()..line.len() - 1];
                let version = value.trim_matches(&[' ', '"'][..]);
                if version != expected_version.as_str() {
                    diagnostics.report(
                        &context
                            .message_interface
                            .unexpected_z3_version(&expected_version, version),
                    );
                    panic!(
                        "The verifier expects z3 version \"{}\", found version \"{}\"",
                        expected_version, version
                    );
                }
            }
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if let Some(disabled_expr) = disabled_expr {
        context.smt_log.log_assert(&None, &disabled_expr);
    }

    if context.solver.is_z3_compatible() || matches!(context.solver, SmtSolver::Adsmt) {
        // Adsmt's lu-smt option dispatcher recognises
        // `(set-option :rlimit N)` and routes it into
        // `check_sat_with_deadline`, so the same emit path serves
        // both Z3 / OxiZ and Adsmt; only Cvc5 takes its limit at
        // process spawn instead.
        context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
        context.set_z3_param_u32("rlimit", context.rlimit, false);
    }

    context.smt_log.log_word("check-sat");

    // Run SMT solver
    let smt_run_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let commands_handle = context.get_smt_process().send_commands_async(smt_data);
    let smt_output = if let Some((report_threshold, report_fn)) = report_long_running {
        match commands_handle.wait_timeout(*report_threshold) {
            Ok(smt_output) => smt_output,
            Err(handle) => {
                report_fn(smt_run_start_time.elapsed(), false);
                let smt_output = handle.wait();
                report_fn(smt_run_start_time.elapsed(), true);
                smt_output
            }
        }
    } else {
        commands_handle.wait()
    };
    context.time_smt_run += smt_run_start_time.elapsed();

    enum SmtOutput {
        Unsat,
        Sat,
        Unknown,
        /// adsmt-only 4th verdict.  `lu-smt` prints the literal
        /// `abductive` followed by a single-line JSON object on the
        /// very next line — schema is pinned by Y4
        /// `smt-cross-validation-tracker.md` §9 and matches
        /// `adsmt-abduce::rank::RankedCandidate` +
        /// `Candidate { hypotheses, explanations, sources }` 1:1.
        Abductive(Vec<AbductiveCandidate>),
    }

    // Process SMT results
    let mut unsat: Option<SmtOutput> = None;
    let mut expect_abductive_json = false;
    for line in smt_output {
        if expect_abductive_json {
            match parse_abductive_candidates_line(&line) {
                Ok(candidates) => {
                    unsat = Some(SmtOutput::Abductive(candidates));
                }
                Err(why) => {
                    return ValidityResult::UnexpectedOutput(format!(
                        "malformed adsmt abductive JSON ({}): {}",
                        why, line
                    ));
                }
            }
            expect_abductive_json = false;
        } else if line == "unsat" {
            assert!(unsat.is_none());
            unsat = Some(SmtOutput::Unsat);
        } else if line == "sat" {
            assert!(unsat.is_none());
            unsat = Some(SmtOutput::Sat);
        } else if line == "unknown" || line == "cvc5 interrupted by timeout." {
            assert!(unsat.is_none());
            unsat = Some(SmtOutput::Unknown);
        } else if line == "abductive" && matches!(context.solver, SmtSolver::Adsmt) {
            assert!(unsat.is_none());
            // The next line of stdout is the lu-smt single-line JSON
            // payload describing the ranked candidates.  Switch the
            // loop into "expect JSON" mode so we route it to the
            // parser rather than the unexpected-output path.
            expect_abductive_json = true;
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }
    if expect_abductive_json {
        return ValidityResult::UnexpectedOutput(
            "adsmt emitted `abductive` verdict but no JSON payload followed".to_string(),
        );
    }

    if context.solver.is_z3_compatible() || matches!(context.solver, SmtSolver::Adsmt) {
        // Clear the deadline on adsmt the same way we clear it on
        // Z3/OxiZ — lu-smt treats `:rlimit 0` as "unlimited".
        context.smt_log.log_set_option("rlimit", "0");
        context.set_z3_param_u32("rlimit", 0, false);
    }

    let unsat = unsat.expect("expected sat/unsat/unknown from SMT solver");

    enum ResultDetermination<T> {
        Determined(ValidityResult),
        Undetermined(T),
    }

    let unsat_result = match unsat {
        SmtOutput::Unsat => ResultDetermination::Undetermined(true),
        SmtOutput::Sat => ResultDetermination::Undetermined(false),
        SmtOutput::Abductive(candidates) => {
            // adsmt's 4th verdict.  The candidates are propagated
            // verbatim through `ValidityResult::Abductive` so the
            // Verus reporter (P-vb.7) can emit them under the
            // `-V report-abductive-on-unknown` flag.  Mark the
            // context state mirroring the other terminal-but-
            // not-decided paths (Canceled).
            context.state = ContextState::Canceled;
            ResultDetermination::Determined(ValidityResult::Abductive { candidates })
        }
        SmtOutput::Unknown => {
            context.smt_log.log_get_info("reason-unknown");
            let smt_data = context.smt_log.take_pipe_data();
            let smt_output = context.get_smt_process().send_commands(smt_data);

            #[derive(PartialEq, Eq)]
            enum SmtReasonUnknown {
                Canceled,
                Incomplete,
                Unknown,
            }

            let mut reason = None;
            for line in smt_output {
                if line == context.solver.reason_unknown_canceled_str() {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Canceled);
                } else if line == "(:reason-unknown \"unknown\")" {
                    // it appears this sometimes happens when rlimit is exceeded
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Unknown);
                } else if line.starts_with(context.solver.reason_unknown_incomplete_str()) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if line
                    == "(:reason-unknown \"smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)\")"
                {
                    // longer message shows up when there's no push/pop around the query
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if context.ignore_unexpected_smt {
                    diagnostics.report(&context.message_interface.bare(
                        crate::messages::MessageLevel::Warning,
                        format!("warning: unexpected SMT output: {}", line).as_str(),
                    ));
                } else {
                    return ValidityResult::UnexpectedOutput(line);
                }
            }

            match reason.expect("expected :reason-unknown") {
                SmtReasonUnknown::Canceled | SmtReasonUnknown::Unknown => {
                    context.state = ContextState::Canceled;
                    ResultDetermination::Determined(ValidityResult::Canceled)
                }
                SmtReasonUnknown::Incomplete => ResultDetermination::Undetermined(false),
            }
        }
    };

    match unsat_result {
        ResultDetermination::Determined(r) => r,
        ResultDetermination::Undetermined(true) => {
            context.state = ContextState::FoundResult;

            let usage_info = if context.usage_info_enabled {
                context.smt_log.log_word("get-unsat-core");

                let smt_data = context.smt_log.take_pipe_data();
                let smt_output = context.get_smt_process().send_commands(smt_data);

                let mut smt_output = smt_output.into_iter();
                let unsat_core_str =
                    smt_output.next().expect("expected one line in the unsat core output");
                assert!(smt_output.next().is_none());

                let fun_names: Vec<Ident> = unsat_core_str
                    .strip_prefix('(')
                    .expect("invalid unsat core")
                    .strip_suffix(')')
                    .expect("invalid unsat core")
                    .split_terminator(' ')
                    .map(|x| Arc::new(x.to_owned()))
                    .collect();
                crate::context::UsageInfo::UsedAxioms(fun_names)
            } else {
                crate::context::UsageInfo::None
            };

            ValidityResult::Valid(usage_info)
        }
        ResultDetermination::Undetermined(false) => smt_get_model(context, infos, air_model),
    }
}

pub(crate) fn smt_get_rlimit_count(context: &mut Context) -> Result<u64, ValidityResult> {
    assert!(context.solver.is_z3_compatible()); // CVC5 and adsmt output format for statistics is different

    context.smt_log.log_get_info("all-statistics");
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let statistics = crate::parser::parse_sexpression(&smt_output);
    let stats_map = statistics
        .as_list()
        .unwrap()
        .chunks(2)
        .map(|chunk| {
            let [key, value] = chunk else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            let Some((key, value)) = key
                .as_atom()
                .map(|key| &key.as_str()[1..])
                .and_then(|key| value.as_atom().map(|value| (key, value.as_str())))
            else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            Ok((key, value))
        })
        .collect::<Result<HashMap<&str, &str>, ValidityResult>>()?;
    let Some(rlimit_count) = stats_map["rlimit-count"].parse().ok() else {
        return Err(ValidityResult::UnexpectedOutput(format!(
            "expected rlimit-count in smt statistics"
        )));
    };
    Ok(rlimit_count)
}

fn smt_get_model(
    context: &mut Context,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
) -> ValidityResult {
    let mut discovered_error: Option<AssertionInfo> = None;
    let mut discovered_assert_id: Option<Option<Arc<Vec<u64>>>> = None;
    let mut discovered_additional_info: Vec<ArcDynMessage> = Vec::new();

    context.smt_log.log_word("get-model");

    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);

    if smt_output.iter().any(|line| line.contains("model is not available")) {
        // when we don't use incremental solving, sometime the model is not available when the z3 result is unknown
        context.state = ContextState::FoundInvalid(infos, None);
        return ValidityResult::Invalid(None, None, None);
    };

    let model =
        crate::parser::Parser::new(context.message_interface.clone()).lines_to_model(&smt_output);
    let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
    for def in model.iter() {
        model_defs.insert(def.name.clone(), def.clone());
    }
    for info in infos.iter_mut() {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true" {
                discovered_error = Some(info.clone());
                discovered_assert_id = Some(info.assert_id.clone());

                // Disable this label in subsequent check-sat calls to get additional errors
                info.disabled = true;
                let disable_label = mk_not(&ident_var(&info.label));
                context.smt_log.log_assert(&None, &disable_label);

                break;
            }
        }
    }
    // A solver that answered `unknown` can hand back a `(get-model)` response
    // that parses but pins no assertion label to `true` — there is no real
    // counterexample to point at.  This is exactly adsmt's native
    // `(:reason-unknown "(incomplete …")` path: lu-smt returns `unknown` fast,
    // stays alive, and the follow-on `(get-model)` yields no falsified label
    // (and no literal "model is not available" line).  Rather than
    // `.expect()`-panicking here — which, mid-unwind, trips the
    // `PanicOnDropVec` #1044 guard in the verus driver and aborts the whole
    // run ("panic in a destructor during cleanup") instead of reporting one
    // not-verified obligation — fall back to the same plain not-verified
    // result as the "model is not available" branch above.
    let Some(discovered_error) = discovered_error else {
        context.state = ContextState::FoundInvalid(infos, None);
        return ValidityResult::Invalid(None, None, None);
    };
    let mut axiom_infos: Vec<Arc<AxiomInfo>> =
        context.axiom_infos.map().values().cloned().collect();
    axiom_infos.sort_by_key(|info| info.label.clone());
    // stabilize order
    for info in axiom_infos {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true"
                && (info.filter.is_none() || info.filter == discovered_error.filter)
            {
                discovered_additional_info.append(&mut info.labels.clone());
                break;
            }
        }
    }

    if context.debug {
        println!("Z3 model: {:?}", &model);
    }

    // Attach the additional info to the error
    // For example, the error might be something like "precondition not satisfied"
    // (an error which comes from the air assert statement)
    // and the additional info might tell you _which_ precondition failed
    // (a label that comes from one of the axioms associated
    // to the function precondition)

    let error = discovered_error.error;
    let e = context.message_interface.append_labels(&error, &discovered_additional_info);
    context.state = ContextState::FoundInvalid(infos, Some(air_model.clone()));
    ValidityResult::Invalid(Some(air_model), Some(e), discovered_assert_id.unwrap())
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    query: &Query,
    air_model: Model,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    if !context.disable_incremental_solving {
        context.smt_log.log_push();
        context.push_name_scope();
    }

    let rlimit_count_1 = if context.solver.is_z3_compatible() {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, _, _, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let assertion = elim_zero_args_expr(assertion);

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&context.message_interface.get_note(&info.error));
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled_assertion));

    // A2a: when abduction is requested, wrap the negated-goal assertion and
    // its `(check-sat)` in a nested `(push)`/`(pop)` so that — on a failed
    // query — we can `(pop)` the `¬goal` back off and run `(abduce <goal>)`
    // against `F` ALONE.  The abduce's consistency test (`SAT(F ∧ H)`) would
    // be vacuously false if `¬goal` were still on the stack.
    let do_abduce =
        context.request_abductive_on_unknown && matches!(context.solver, SmtSolver::Adsmt);
    if do_abduce {
        context.smt_log.log_push();
    }
    context.smt_log.log_assert(&None, &not_expr);

    let rlimit_count_2 = if context.solver.is_z3_compatible() {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    let mut result =
        smt_check_assertion(context, diagnostics, infos, air_model, false, report_long_running);

    if do_abduce {
        // Balance the nested push regardless of the verdict, dropping `¬goal`
        // (and any model-disabling label asserts) back to `F`.
        context.smt_log.log_pop();
        if matches!(result, ValidityResult::Invalid(..) | ValidityResult::Canceled) {
            let candidates = run_abduction(context, &assertion, &query.local);
            if !candidates.is_empty() {
                // Mirror the native `Abductive` verdict's bookkeeping.
                context.state = ContextState::Canceled;
                result = ValidityResult::Abductive { candidates };
            }
        }
    }

    if context.solver.is_z3_compatible() {
        let (ctx_rlimit_init, ctx_rlimit_run) = context.rlimit_count.unwrap();
        let rlimit_count_3 = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        let rlimit_init = rlimit_count_2.unwrap() - rlimit_count_1.unwrap();
        let rlimit_run = rlimit_count_3 - rlimit_count_2.unwrap();
        context.rlimit_count = Some((ctx_rlimit_init + rlimit_init, ctx_rlimit_run + rlimit_run));
    }

    result
}

/// A2a — the "verify-or-explain" abduction.  Called (Adsmt only) after a
/// query failed to verify and its `¬goal` has been popped back off the
/// stack, so the solver context is `F` alone.  Declares a focused abducible
/// vocabulary — sign/positivity predicates over the integer constants in
/// scope for this query — turns on the theory-aware search, and asks adsmt
/// for the minimal ranked hypothesis set `H` (drawn from those abducibles)
/// such that `F ∧ H ⊨ goal`.  Returns the parsed candidates (empty if adsmt
/// found none, or on any malformed payload — the caller then keeps the
/// original not-verified verdict).
/// Recursively peel verus's error-localization wrappers
/// (`LabeledAssertion` → `(location …)`, `LabeledAxiom` → `(axiom_location …)`)
/// off an expression, leaving the bare SMT-LIB term.  adsmt's `(abduce …)`
/// surface rejects the verus-only `location` operator.
fn strip_labels(expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(expr, &mut |e| match &**e {
        ExprX::LabeledAssertion(_, _, _, inner) => inner.clone(),
        ExprX::LabeledAxiom(_, _, inner) => inner.clone(),
        _ => e.clone(),
    })
}

fn run_abduction(
    context: &mut Context,
    goal: &Expr,
    local: &crate::ast::Decls,
) -> Vec<AbductiveCandidate> {
    // Theory-aware minimal-subset search (rc.36+), so the entailment /
    // consistency checks delegate through the same complete path the main
    // solve uses (verus's axiomatized `Add`/`Poly`/… encoding needs it).
    context.smt_log.log_set_option("abduct-theory", "true");
    // Focused vocabulary: `(>= v 0)` and `(> v 0)` for each integer constant
    // `v` declared local to this query (the parameters/locals the goal is
    // built from).  Kept deliberately tight — the search is
    // O(check-sat × subsets), so a small, goal-relevant basis is the point.
    for decl in local.iter() {
        if let DeclX::Const(id, typ) = &**decl {
            if matches!(&**typ, TypX::Int) {
                let v = ident_var(id);
                let ge0 = Arc::new(ExprX::Binary(BinaryOp::Ge, v.clone(), mk_nat("0")));
                let gt0 = Arc::new(ExprX::Binary(BinaryOp::Gt, v.clone(), mk_nat("0")));
                context.smt_log.log_declare_abducible(&ge0);
                context.smt_log.log_declare_abducible(&gt0);
            }
        }
    }
    // Strip verus's `LabeledAssertion`/`LabeledAxiom` wrappers (which the
    // printer renders as `(location …)` / `(axiom_location …)`) — adsmt's
    // `(abduce …)` parser only knows plain SMT-LIB operators, so the goal
    // must be the bare term `G`, exactly as the de-risk fed it.
    let bare_goal = strip_labels(goal);
    context.smt_log.log_abduce(&bare_goal);
    // Reset the option so it doesn't leak into the next function's queries
    // (set-option is not push/pop-scoped).
    context.smt_log.log_set_option("abduct-theory", "false");

    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);

    // adsmt prints the literal `abductive` then a single-line JSON payload.
    let mut expect_json = false;
    let mut candidates: Vec<AbductiveCandidate> = Vec::new();
    for line in smt_output {
        if expect_json {
            if let Ok(parsed) = parse_abductive_candidates_line(&line) {
                candidates = parsed;
            }
            expect_json = false;
        } else if line == "abductive" {
            expect_json = true;
        }
        // Any other line (set-option acks, blanks) is ignored.
    }
    candidates
}

#[cfg(test)]
mod abductive_parse_tests {
    use super::parse_abductive_candidates_line;

    /// Y4 `smt-cross-validation-tracker.md` §9 — single multi-field
    /// candidate, exact JSON shape lu-smt emits.
    #[test]
    fn parses_y4_single_candidate_example() {
        let line = r#"{"abductive_candidates":[
            {"rank":1,"score":1.025,
             "hypotheses":["forall c, revoked(c) implies not alive(owner(c).frame)"],
             "explanations":[null],
             "sources":["abducible-frame-revoke-chain"]}
        ]}"#;
        let candidates = parse_abductive_candidates_line(line).expect("parse");
        assert_eq!(candidates.len(), 1);
        let c = &candidates[0];
        assert_eq!(c.rank, 1);
        assert!((c.score - 1.025).abs() < f64::EPSILON);
        assert_eq!(c.hypotheses.len(), 1);
        assert_eq!(c.explanations, vec![None]);
        assert_eq!(c.sources, vec!["abducible-frame-revoke-chain".to_string()]);
    }

    /// Multi-candidate, ascending rank, with a mix of null / Some
    /// explanations.  Mirrors what `rank_candidates` produces for a
    /// real abductive Tier-4 escalation.
    #[test]
    fn parses_multi_candidate_with_explanations() {
        let line = r#"{"abductive_candidates":[
            {"rank":1,"score":2.013,
             "hypotheses":["P(x)","Q(x)"],
             "explanations":["from P", null],
             "sources":["src-a","src-b"]},
            {"rank":2,"score":3.001,
             "hypotheses":["R(y)"],
             "explanations":[null],
             "sources":["src-c"]}
        ]}"#;
        let candidates = parse_abductive_candidates_line(line).expect("parse");
        assert_eq!(candidates.len(), 2);
        assert_eq!(candidates[0].rank, 1);
        assert_eq!(candidates[0].hypotheses.len(), 2);
        assert_eq!(candidates[0].explanations[0].as_deref(), Some("from P"));
        assert_eq!(candidates[0].explanations[1], None);
        assert_eq!(candidates[1].rank, 2);
        assert_eq!(candidates[1].hypotheses, vec!["R(y)".to_string()]);
    }

    /// Malformed JSON must be rejected, not silently dropped.
    #[test]
    fn rejects_malformed_json() {
        let err = parse_abductive_candidates_line("not even json")
            .expect_err("must reject non-JSON");
        assert!(err.contains("not valid JSON"));
    }

    /// Lock-step invariant: `hypotheses`, `explanations`, `sources`
    /// must have equal lengths.  Spec drift would silently pair the
    /// wrong explanation with a hypothesis.
    #[test]
    fn rejects_lock_step_mismatch() {
        let line = r#"{"abductive_candidates":[
            {"rank":1,"score":1.0,
             "hypotheses":["a","b"],
             "explanations":[null],
             "sources":["s1","s2"]}
        ]}"#;
        let err = parse_abductive_candidates_line(line)
            .expect_err("must reject mismatched list lengths");
        assert!(err.contains("lock-step lists out of sync"));
    }

    /// Top-level missing the `abductive_candidates` key is a
    /// protocol violation — the engine always emits the wrapping
    /// object even for empty lists.
    #[test]
    fn rejects_missing_top_level_key() {
        let line = r#"{"verdict":"abductive"}"#;
        let err = parse_abductive_candidates_line(line)
            .expect_err("must reject missing top-level array");
        assert!(err.contains("abductive_candidates"));
    }

    /// Per-candidate missing fields surface descriptive errors so
    /// schema drift fails fast.
    #[test]
    fn rejects_missing_per_candidate_field() {
        let line = r#"{"abductive_candidates":[
            {"rank":1,"score":1.0,
             "hypotheses":["a"],
             "sources":["s1"]}
        ]}"#;
        let err = parse_abductive_candidates_line(line)
            .expect_err("must reject candidate missing `explanations`");
        assert!(err.contains("explanations"));
    }

    /// Empty candidate list is accepted (engine returned abductive
    /// but minimisation eliminated every candidate).  This is the
    /// degenerate but legitimate case.
    #[test]
    fn accepts_empty_candidate_list() {
        let line = r#"{"abductive_candidates":[]}"#;
        let candidates = parse_abductive_candidates_line(line).expect("parse");
        assert!(candidates.is_empty());
    }

    /// Verbatim output captured from `lu-smt 1.0.0-rc.8` for the
    /// quintessential abductive trigger
    /// `(assert (P a)) (assert (forall ((x U)) (=> (P x) (P (next x)))))`:
    /// each round produces a fresh instance `(P (next^k a))`, the
    /// quantifier-instantiation loop never fixpoints, so Tier-4
    /// escalation fires.  Pins the wire-level shape against
    /// silent schema drift on the adsmt side.
    #[test]
    fn parses_lu_smt_rc8_quant_tier4_output() {
        let line = r#"{"abductive_candidates":[{"explanations":["quantifier `∀x:U. or (not (P x)) (P (next x))` needs a witness instantiation the engine could not synthesize (tier 4 escalation)"],"hypotheses":["forall (λx:U. or (not (P x)) (P (next x)))"],"rank":1,"score":1.007,"sources":["quant-tier4"]}]}"#;
        let candidates = parse_abductive_candidates_line(line).expect("parse");
        assert_eq!(candidates.len(), 1);
        let c = &candidates[0];
        assert_eq!(c.rank, 1);
        assert!((c.score - 1.007).abs() < 1e-9);
        assert_eq!(c.hypotheses.len(), 1);
        assert!(c.hypotheses[0].contains("forall"));
        assert!(c.hypotheses[0].contains("(P (next x))"));
        assert_eq!(c.explanations.len(), 1);
        assert!(c.explanations[0].as_deref().unwrap().contains("tier 4 escalation"));
        assert_eq!(c.sources, vec!["quant-tier4".to_string()]);
    }
}
