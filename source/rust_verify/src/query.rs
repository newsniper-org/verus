#![allow(clippy::arc_with_non_send_sync)]

use crate::boundary_suggestions::build_boundary_suggestion;
use crate::config::Args;
use crate::context::{Context, ErasureInfo};
use crate::rust_to_vir::AnonConstToCheck;
use crate::rust_to_vir_func::FunctionOrConstInfo;
use crate::rust_to_vir_func::finish_item;
use crate::verifier::FuncDetails;
use air::messages::Diagnostics;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::Mutex;
use vir::ast::{CrateId, Datatype, Fun, Function, FunctionStub, Krate, Path, VirErr, VirErrAs};
use vir::context::WarningCtx;
use vir::messages::{MessageLevel, ToAny};
use vir::modes::ErasureModes;
use vir::resolution_inference::{ResolutionInfo, krate_infer_resolution};
use vir::traits::{DemoteTraitLookup, MergedTraits};
use vir::well_formed::{DynCompatabilityChecks, InitialWfResults};

/// Krate without the full functions (i.e., empty function list in the krate)
/// Instead we have FunctionOrConstInfos which contains FunctionStubs.
pub(crate) struct PreCrate<'tcx> {
    pub ctxt: Context<'tcx>,
    pub warning_ctx: Arc<WarningCtx>,
    pub krate_without_funs: Krate,
    pub infos: Vec<Arc<FunctionOrConstInfo<'tcx>>>,
    pub fun_name_to_info: HashMap<Fun, Arc<FunctionOrConstInfo<'tcx>>>,
    pub def_id_to_fun_name_for_erasure: HashMap<DefId, Option<Fun>>,
    /// Anonymous constants to be mode-checked. Unlike the items in `infos`, their
    /// `FunctionOrConstInfo`s are built on demand (see `Query::get_anon_const_info`).
    pub anon_consts: Vec<Arc<AnonConstToCheck>>,
    pub fun_name_to_anon_const: HashMap<Fun, Arc<AnonConstToCheck>>,
}

/// Used to guarantee that we emitted an error
#[derive(Clone, Copy)]
pub(crate) struct QueryError {
    pub _i_just_emitted_an_error: (),
}

pub(crate) type Res<T> = Result<T, QueryError>;

pub(crate) struct State<'tcx> {
    /// Imported crates
    cache_other_vir_crates: Option<Res<Arc<Vec<Krate>>>>,
    /// Pre-crate before functions are lowered to VIR and checked in full
    cache_pre_crate: Option<Res<Arc<PreCrate<'tcx>>>>,
    /// Info used for demoting external traits
    cache_demote_trait_lookup: Option<Res<Arc<DemoteTraitLookup>>>,
    /// Traits and Trait Impls from all crates, de-duplicated
    cache_merged_traits: Option<Res<MergedTraits>>,
    /// Info used for demoting external traits
    cache_initial_wf_results: Option<Res<InitialWfResults>>,
    /// All function stubs, across this crate and imported crates
    cache_all_function_stubs: Option<Res<Arc<HashMap<Fun, FunctionStub>>>>,
    /// FunctionOrConstInfos for anonymous constants, generated on demand
    cache_anon_const_infos: HashMap<Fun, Res<Arc<FunctionOrConstInfo<'tcx>>>>,
    /// Pre-check functions, immediately after translation from HIR
    cache_unchecked_functions: HashMap<Fun, Res<(Function, Arc<ErasureInfo>)>>,
    /// Completed functions
    cache_checked_functions: HashMap<
        Fun,
        Res<(Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks)>,
    >,
    /// Crate that can be exported
    cache_exportable_crate: Option<Res<Krate>>,
    /// Crate with trait demotion, resolution inference, merged with imported crates and pruned
    cache_merged_crate: Option<Res<(Krate, Arc<WarningCtx>)>>,

    /// Errors found along the way
    pub encountered_blocking_vir_error: bool,
}

pub(crate) struct Query<'tcx> {
    args: Args,
    reporter: Box<dyn Diagnostics + 'tcx>,
    crate_id: CrateId,
    state: RefCell<State<'tcx>>,
    pub deferred_errors: Arc<Mutex<Vec<VirErr>>>,
    pub func_details: Arc<Mutex<HashMap<Fun, FuncDetails>>>,
}

macro_rules! cache_or_compute {
    ( $self:ident, $name:ident, $fun_name:ident ( $( $args:expr ),* )  ) => {{
        let state = $self.state.borrow();
        if let Some(x) = &state.$name {
            x.clone()
        } else {
            std::mem::drop(state);
            let s = $self.$fun_name();
            let mut state = $self.state.borrow_mut();
            state.$name = Some(s.clone());
            s
        }
    }};
}

impl<'tcx> Query<'tcx> {
    pub fn new(
        args: Args,
        reporter: Box<dyn Diagnostics + 'tcx>,
        func_details: Arc<Mutex<HashMap<Fun, FuncDetails>>>,
        deferred_errors: Arc<Mutex<Vec<VirErr>>>,
        other_vir_crates: Vec<Krate>,
        pre_crate: PreCrate<'tcx>,
        crate_id: CrateId,
    ) -> Self {
        Self {
            args,
            reporter,
            crate_id,
            state: RefCell::new(State {
                cache_other_vir_crates: Some(Ok(Arc::new(other_vir_crates))),
                cache_pre_crate: Some(Ok(Arc::new(pre_crate))),
                cache_demote_trait_lookup: None,
                cache_merged_traits: None,
                cache_initial_wf_results: None,
                cache_all_function_stubs: None,
                cache_anon_const_infos: HashMap::new(),
                cache_unchecked_functions: HashMap::new(),
                cache_checked_functions: HashMap::new(),
                cache_exportable_crate: None,
                cache_merged_crate: None,

                encountered_blocking_vir_error: false,
            }),
            deferred_errors,
            func_details,
        }
    }

    fn emit_errors(&self, errs: Vec<VirErr>) -> QueryError {
        let mut state = self.state.borrow_mut();
        assert!(errs.len() > 0);
        state.encountered_blocking_vir_error = true;
        // Report pending warnings before the errors
        if let Some(Ok(pre_crate)) = &state.cache_pre_crate {
            pre_crate.ctxt.flush_diagnostics(&*self.reporter);
        }
        for err in errs {
            self.reporter.report_now(&err.to_any());
        }
        QueryError { _i_just_emitted_an_error: () }
    }

    pub(crate) fn emit_error(&self, err: VirErr) -> QueryError {
        self.emit_errors(vec![err])
    }

    fn handle_wf_error(
        &self,
        ctxt: &Context<'tcx>,
        fun: Option<Fun>,
        wf_err: vir::well_formed::WFErr,
    ) -> QueryError {
        let vir::well_formed::WFErr { errors, boundary_errors, func_failed_proof_notes } = wf_err;
        assert!(errors.len() > 0 || boundary_errors.len() > 0);
        if errors.len() > 0 {
            self.emit_errors(errors);
        }
        for (path, mut err) in boundary_errors.into_iter() {
            let map = ctxt.name_def_id_map.borrow();
            let did = map.get(&path);
            if let Some(did) = did {
                if let Ok(s) = build_boundary_suggestion(&ctxt, *did, &path) {
                    err = err
                        .help(format!("the following declaration may resolve this error:\n{}", s));
                }
            }
            self.emit_error(err);
        }
        if let Some(fun) = fun {
            self.record_func_failed_proof_notes(&fun, func_failed_proof_notes);
        } else {
            assert!(func_failed_proof_notes.is_empty());
        }
        QueryError { _i_just_emitted_an_error: () }
    }

    fn record_func_failed_proof_notes(&self, func: &Fun, failed_proof_notes: HashSet<String>) {
        use std::collections::hash_map::Entry;
        let mut func_details = self.func_details.lock().unwrap();
        match func_details.entry(func.clone()) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.get_mut().failed_proof_notes.extend(failed_proof_notes);
            }
            Entry::Vacant(vacant_entry) => {
                let _ = vacant_entry.insert(FuncDetails {
                    failed_proof_notes: failed_proof_notes,
                    ..Default::default()
                });
            }
        }
    }

    fn emit_non_blocking_errors(&self, errs: Vec<VirErr>) {
        self.deferred_errors.lock().unwrap().extend(errs);
    }

    fn emit_diags(&self, diags: Vec<VirErrAs>) {
        for diag in diags.into_iter() {
            match diag {
                vir::ast::VirErrAs::Warning(err) => {
                    self.reporter.report_as(&err.to_any(), MessageLevel::Warning)
                }
                vir::ast::VirErrAs::Note(err) => {
                    self.reporter.report_as(&err.to_any(), MessageLevel::Note)
                }
            }
        }
    }

    //// Import crate

    pub fn get_other_vir_crates(&self) -> Res<Arc<Vec<Krate>>> {
        let state = self.state.borrow();
        if let Some(imported) = &state.cache_other_vir_crates {
            return imported.clone();
        }
        unreachable!();
    }

    //// Pre-crate

    pub fn get_pre_crate(&self) -> Res<Arc<PreCrate<'tcx>>> {
        let state = self.state.borrow();
        if let Some(pre_crate) = &state.cache_pre_crate {
            return pre_crate.clone();
        }
        unreachable!();
        //self.cache_pre_crate = Some(self._compute_pre_crate());
        //self.cache_pre_crate.clone().unwrap()
    }

    //// Get all function stubs

    pub fn get_all_function_stubs(&self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        cache_or_compute!(self, cache_all_function_stubs, _compute_all_function_stubs())
    }

    fn _compute_all_function_stubs(&self) -> Res<Arc<HashMap<Fun, FunctionStub>>> {
        // combine all the function stubs from our crate and the external crates
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let mut stubs = HashMap::new();
        for stub in pre_crate.infos.iter().flat_map(|info| info.iter_stubs()) {
            let found = stubs.insert(stub.x.name.clone(), stub.clone());
            if let Some(found) = found {
                return Err(self.emit_error(vir::well_formed::func_conflict_error(&stub, &found)));
            }
        }
        for krate in other_vir_crates.iter() {
            for function in krate.functions.iter() {
                let stub = vir::ast_util::function_to_stub(function);
                let found = stubs.insert(stub.x.name.clone(), stub.clone());
                if let Some(found) = found {
                    return Err(
                        self.emit_error(vir::well_formed::func_conflict_error(&stub, &found))
                    );
                }
            }
        }

        Ok(Arc::new(stubs))
    }

    //// DemoteTraitsLookup

    pub fn get_demote_trait_lookup(&self) -> Res<Arc<DemoteTraitLookup>> {
        cache_or_compute!(self, cache_demote_trait_lookup, _compute_demote_trait_lookup())
    }

    pub fn _compute_demote_trait_lookup(&self) -> Res<Arc<DemoteTraitLookup>> {
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        let function_stubs = self.get_all_function_stubs()?;
        Ok(Arc::new(vir::traits::DemoteTraitLookup::new(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            &function_stubs,
        )))
    }

    //// Merged traits

    pub fn get_merged_traits(&self) -> Res<MergedTraits> {
        cache_or_compute!(self, cache_merged_traits, _compute_merged_traits())
    }

    pub fn _compute_merged_traits(&self) -> Res<MergedTraits> {
        let other_vir_crates = self.get_other_vir_crates()?;
        let pre_crate = self.get_pre_crate()?;
        vir::traits::merge_external_traits(&pre_crate.krate_without_funs, &other_vir_crates)
            .map_err(|e| self.emit_error(e))
    }

    //// check_crate_initial

    pub fn get_initial_wf_results(&self) -> Res<InitialWfResults> {
        cache_or_compute!(self, cache_initial_wf_results, _compute_initial_wf_results())
    }

    fn _compute_initial_wf_results(&self) -> Res<InitialWfResults> {
        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let other_vir_crates = self.get_other_vir_crates()?;
        let function_stubs = self.get_all_function_stubs()?;
        let merged_traits = self.get_merged_traits()?;

        let (wf, non_blocking_errors, diags) = vir::well_formed::check_crate_initial(
            &pre_crate.krate_without_funs,
            &other_vir_crates,
            function_stubs.clone(),
            merged_traits.clone(),
            self.args.no_cheating,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        wf.map_err(|e| self.handle_wf_error(ctxt, None, e))
    }

    //// datatypes map

    pub fn get_datatypes_map(&self) -> Res<Arc<HashMap<Path, Datatype>>> {
        Ok(self.get_initial_wf_results()?.lookup.dts.clone())
    }

    //// Anonymous constants
    ////
    //// Anonymous constants are translated to VIR and checked (so that we can reject
    //// ghost code inside them) but they are never verified, since Rust's own const
    //// evaluator already checks them.
    ////
    //// Unlike for the other items, we build the `FunctionOrConstInfo` here rather than
    //// in `crate_to_vir`: asking for the type of an anonymous constant ICEs unless its
    //// enclosing item has been type-checked first, and type-checking the enclosing item
    //// may require mode-checking results, which are only available once the query
    //// system is up and running.

    fn get_anon_const_info(&self, fun: &Fun) -> Res<Arc<FunctionOrConstInfo<'tcx>>> {
        let state = self.state.borrow();
        if let Some(info) = state.cache_anon_const_infos.get(fun) {
            return info.clone();
        }
        std::mem::drop(state);
        let res = self._compute_anon_const_info(fun);
        let mut state = self.state.borrow_mut();
        state.cache_anon_const_infos.insert(fun.clone(), res.clone());
        res
    }

    fn _compute_anon_const_info(&self, fun: &Fun) -> Res<Arc<FunctionOrConstInfo<'tcx>>> {
        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let tcx = ctxt.tcx;
        let anon_const = &pre_crate.fun_name_to_anon_const[fun];

        // `type_of` on an anonymous constant requires that the item containing it
        // has already been type-checked.
        if tcx.hir_node_by_def_id(anon_const.owner_def_id).associated_body().is_some() {
            tcx.typeck(anon_const.owner_def_id);
        } else if tcx.check_well_formed(anon_const.owner_def_id).is_err() {
            return Err(QueryError { _i_just_emitted_an_error: () });
        }

        let body = tcx.hir_body_owned_by(anon_const.def_id);
        let span = body.value.span;
        let mid_typ = tcx.type_of(anon_const.def_id).skip_binder();

        let result = (|| {
            let typ = ctxt.mid_ty_to_vir(anon_const.def_id.to_def_id(), span, &mid_typ, None)?;
            // `check_item_const_or_static` only uses the `State` to record warning
            // configs; for an anonymous constant that was already done up front in
            // `collect_anon_consts`, so a throw-away `State` is fine here.
            let mut state = crate::rust_to_vir::State {
                external_info: crate::rust_to_vir_impl::ExternalInfo::new(),
                fun_warn_configs: HashMap::new(),
            };
            let mut infos: Vec<FunctionOrConstInfo<'tcx>> = Vec::new();
            let name = crate::rust_to_vir_func::check_item_const_or_static(
                ctxt,
                &mut state,
                &mut infos,
                span,
                anon_const.def_id.to_def_id(),
                vir::ast::Visibility { restricted_to: Some(anon_const.module_path.clone()) },
                &anon_const.module_path,
                &[],
                &typ,
                &body.id(),
                false,
                None,
            )?;
            assert!(&name == fun);
            assert!(infos.len() == 1);
            Ok(Arc::new(infos.pop().unwrap()))
        })();

        ctxt.flush_diagnostics(&*self.reporter);
        result.map_err(|e| self.emit_error(e))
    }

    //// Translating an individual function from HIR -> VIR

    pub fn get_unchecked_function(&self, fun: &Fun) -> Res<Function> {
        Ok(self.get_unchecked_function_pair(fun)?.0.clone())
    }

    pub fn get_erasure_info(&self, fun: &Fun) -> Res<Arc<ErasureInfo>> {
        Ok(self.get_unchecked_function_pair(fun)?.1.clone())
    }

    pub fn get_unchecked_function_pair(&self, fun: &Fun) -> Res<(Function, Arc<ErasureInfo>)> {
        let state = self.state.borrow();
        if let Some(f) = state.cache_unchecked_functions.get(fun) {
            return f.clone();
        }
        std::mem::drop(state);

        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;
        let anon_const_info;
        let info = match pre_crate.fun_name_to_info.get(fun) {
            Some(info) => info,
            None => {
                anon_const_info = self.get_anon_const_info(fun)?;
                &anon_const_info
            }
        };
        let mut new_functions = vec![];
        let result = finish_item(ctxt, &info, &mut new_functions);
        ctxt.flush_diagnostics(&*self.reporter);

        match result {
            Ok(()) => {
                let mut state = self.state.borrow_mut();
                for (new_function, erasure_info) in new_functions.into_iter() {
                    let found = state.cache_unchecked_functions.insert(
                        new_function.x.name.clone(),
                        Ok((new_function, Arc::new(erasure_info))),
                    );
                    assert!(found.is_none());
                }
                // Sanity check we got all the functions we expected
                for stub in info.iter_stubs() {
                    assert!(state.cache_unchecked_functions.contains_key(&stub.x.name));
                }
                state.cache_unchecked_functions.get(fun).unwrap().clone()
            }
            Err(err) => {
                let err = self.emit_error(err);
                let mut state = self.state.borrow_mut();
                for stub in info.iter_stubs() {
                    let found =
                        state.cache_unchecked_functions.insert(stub.x.name.clone(), Err(err));
                    assert!(found.is_none());
                }
                Err(err)
            }
        }
    }

    //// Checking an individual function

    pub fn get_checked_function(
        &self,
        fun: &Fun,
    ) -> Res<(Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks)>
    {
        let state = self.state.borrow();
        if let Some(f) = state.cache_checked_functions.get(fun) {
            return f.clone();
        }
        std::mem::drop(state);
        let res = self._compute_checked_function(fun);
        let mut state = self.state.borrow_mut();
        state.cache_checked_functions.insert(fun.clone(), res.clone());
        res
    }

    fn _compute_checked_function(
        &self,
        fun: &Fun,
    ) -> Result<
        (Function, Arc<ErasureModes>, Option<Arc<ResolutionInfo>>, DynCompatabilityChecks),
        QueryError,
    > {
        let function = self.get_unchecked_function(fun)?;
        let lookup = self.get_demote_trait_lookup()?;
        let pre_crate = self.get_pre_crate()?;
        let ctxt = &pre_crate.ctxt;

        // Demote external traits

        let function = vir::traits::demote_external_traits_function_calls(&lookup, &function)
            .map_err(|e| self.emit_error(e))?;

        // WF checking

        let initial_wf = self.get_initial_wf_results()?;
        let function_stubs = self.get_all_function_stubs()?;
        let (wf, non_blocking_errors, diags) = vir::well_formed::check_function(
            &pre_crate.krate_without_funs,
            function_stubs.clone(),
            initial_wf.lookup.clone(),
            &lookup,
            &function,
            &pre_crate.warning_ctx,
            self.args.no_cheating,
            self.args.no_verify,
        );
        self.emit_non_blocking_errors(non_blocking_errors);
        self.emit_diags(diags);
        let wf = wf.map_err(|e| self.handle_wf_error(ctxt, Some(fun.clone()), e))?;
        let vir::well_formed::PerFunctionCheckResults {
            func_failed_proof_notes,
            dyn_compatability_checks,
        } = wf;
        self.record_func_failed_proof_notes(fun, func_failed_proof_notes);

        // Autospec

        let function = vir::autospec::resolve_autospec_in_function(&function_stubs, &function)
            .map_err(|e| self.emit_error(e))?;

        // Mode checking

        let (function, erasure_modes, resolution_info) = vir::modes::check_function(
            function_stubs.clone(),
            initial_wf.lookup.clone(),
            &function,
            &lookup,
        )
        .map_err(|e| self.emit_errors(e))?;
        let erasure_modes = Arc::new(erasure_modes);
        let resolution_info = resolution_info.map(Arc::new);

        Ok((function, erasure_modes, resolution_info, dyn_compatability_checks))
    }

    //// Getting the completed krate

    pub fn get_exportable_crate(&self) -> Res<Krate> {
        cache_or_compute!(self, cache_exportable_crate, _compute_exportable_crate())
    }

    pub fn _compute_exportable_crate(&self) -> Res<Krate> {
        let initial_wf_results = self.get_initial_wf_results()?;
        let _ = self.get_initial_wf_results()?;
        let pre_crate = self.get_pre_crate()?;
        let mut cratex = (*pre_crate.krate_without_funs).clone();
        let mut found_err = None;
        let mut all_dyn_compatability_checks = vec![initial_wf_results.dyn_compatability_checks];
        for stub in pre_crate.infos.iter().flat_map(|info| info.iter_stubs()) {
            match self.get_checked_function(&stub.x.name) {
                Ok((function, _, _, dyn_compatability_checks)) => {
                    cratex.functions.push(function);
                    all_dyn_compatability_checks.push(dyn_compatability_checks);
                }
                Err(err) => found_err = Some(err),
            }
        }
        // Anonymous constants are translated only for mode checking.
        // Rust's const evaluator already checks them, so don't verify them;
        // their functions are deliberately left out of the crate.
        for anon_const in pre_crate.anon_consts.iter() {
            match self.get_checked_function(&anon_const.fun) {
                Ok(_) => {}
                Err(err) => found_err = Some(err),
            }
        }
        if let Some(err) = found_err {
            return Err(err);
        }

        let other_vir_crates = self.get_other_vir_crates()?;
        vir::traits::set_krate_dyn_compatibility(&other_vir_crates, &mut cratex);
        let krate = Arc::new(cratex);

        let mut krate = vir::ast_sort::sort_krate(&krate);
        Arc::make_mut(&mut krate).arch =
            vir::ast_simplify::krate_merge_arch(&krate, &other_vir_crates)
                .map_err(|e| self.emit_error(e))?;

        let (check, diags) = vir::well_formed::check_crate_final(&krate, &pre_crate.warning_ctx);
        self.emit_diags(diags);
        let () = check.map_err(|e| self.emit_error(e))?;

        vir::well_formed::finish_dyn_compatability_checks(&krate, all_dyn_compatability_checks)
            .map_err(|e| self.emit_errors(e))?;

        Ok(krate)
    }

    //// Getting the merged krate

    pub fn get_merged_crate(&self) -> Res<Krate> {
        Ok(cache_or_compute!(self, cache_merged_crate, _compute_merged_crate())?.0)
    }

    pub fn get_updated_warning_ctx(&self) -> Res<Arc<WarningCtx>> {
        Ok(cache_or_compute!(self, cache_merged_crate, _compute_merged_crate())?.1)
    }

    pub fn _compute_merged_crate(&self) -> Res<(Krate, Arc<WarningCtx>)> {
        let pre_crate = self.get_pre_crate()?;
        let _flush = pre_crate.ctxt.flush_diagnostics_on_drop(&*self.reporter);
        let krate = self.get_exportable_crate()?;
        let demote_trait_lookup = self.get_demote_trait_lookup()?;
        let other_vir_crates = self.get_other_vir_crates()?;
        let merged_traits = self.get_merged_traits()?;

        // Merge
        let my_crate = krate.clone();
        let mut vir_crates: Vec<Krate> = (*other_vir_crates).clone();
        vir_crates.push(krate);
        let unpruned_crate = vir::ast_simplify::merge_krates(vir_crates, &merged_traits)
            .map_err(|e| self.emit_error(e))?;

        let (krate, _) = vir::prune::prune_krate_for_module_or_krate(
            &unpruned_crate,
            &self.crate_id,
            Some(&my_crate),
            None,
            None,
            false,
            false,
        );
        if self.args.alloc_check {
            // (checked on the whole merged crate: an imported impl can matter here without being
            // in the pruned crate. Restricting it to the traits the pruned crate mentions is not
            // sound: an imported function's body, which may dispatch through further traits (e.g.
            // via the bounds of an impl it uses), is not available here.)
            vir::alloc_check::check_merged_krate(&unpruned_crate)
                .map_err(|e| self.emit_error(e))?;
            check_impls_outside_vir(&pre_crate.ctxt, &unpruned_crate)
                .map_err(|e| self.emit_error(e))?;
        }
        if self.args.fip_lint {
            for msg in vir::fip_lint::lint_krate(&unpruned_crate) {
                self.reporter.report_as(&msg.to_any(), MessageLevel::Warning);
            }
            crate::fip_trmc::report(
                &pre_crate.ctxt,
                &pre_crate.fun_name_to_info,
                &unpruned_crate,
                self.args.fip_lint_fix,
            );
        }

        // Demote external traits
        let krate = vir::traits::demote_external_traits(
            &*self.reporter,
            &pre_crate.warning_ctx,
            &krate,
            &demote_trait_lookup,
        )
        .map_err(|e| self.emit_error(e))?;

        // Inherit default bodies
        let mut new_warning_ctx = (*pre_crate.warning_ctx).clone();
        let krate = vir::traits::inherit_default_bodies(&krate, &mut new_warning_ctx)
            .map_err(|e| self.emit_error(e))?;

        // Resolution inference
        // Make sure to do this before the res_info goes stale
        let mut res_infos = HashMap::<Fun, Arc<ResolutionInfo>>::new();
        for stub in pre_crate.infos.iter().flat_map(|info| info.iter_stubs()) {
            match self.get_checked_function(&stub.x.name) {
                Ok((_, _, Some(res_info), _)) => {
                    let found = res_infos.insert(stub.x.name.clone(), res_info.clone());
                    assert!(found.is_none());
                }
                Ok((_, _, None, _)) => {}
                Err(_) => unreachable!(),
            }
        }
        let krate = krate_infer_resolution(&krate, &res_infos).map_err(|e| self.emit_errors(e))?;

        vir::well_formed::check_crate_merged(&krate).map_err(|e| self.emit_error(e))?;

        Ok((krate, Arc::new(new_warning_ctx)))
    }

    //// Erasure modes

    pub fn get_erasure_modes_for_def_id(
        &self,
        def_id: DefId,
    ) -> Res<Option<(Arc<ErasureInfo>, Arc<ErasureModes>)>> {
        let pre_crate = self.get_pre_crate()?;
        let fun = pre_crate.def_id_to_fun_name_for_erasure.get(&def_id);
        let Some(fun) = fun else {
            panic!("get_erasure_modes_for_def_id: missing DefId {:?}", def_id);
        };

        match fun {
            Some(fun) => {
                let (_, erasure_modes, _, _) = self.get_checked_function(fun)?;
                let erasure_info = self.get_erasure_info(fun)?;
                Ok(Some((erasure_info.clone(), erasure_modes.clone())))
            }
            None => Ok(None),
        }
    }
}

std::thread_local! {
    static QUERY: RefCell<Option<Rc<Query<'static>>>> = const { RefCell::new(None) };
}

pub fn set_global_query<'tcx>(query: Rc<Query<'tcx>>) {
    // SAFETY: We coerce 'tcx to 'static here, and we immediately coerce
    // back to 'tcx when retrieving the Query<'_> from the global
    let query: Rc<Query<'static>> = unsafe { std::mem::transmute(query) };
    QUERY.with_borrow_mut(|q| {
        assert!(q.is_none());
        *q = Some(query);
    })
}

pub fn get_global_query<'tcx>(_tcx: TyCtxt<'tcx>) -> Option<Rc<Query<'tcx>>> {
    // SAFETY: We coerce 'static back to 'tcx here.
    // The _tcx argument ensures 'tcx is instantiated with the correct lifetime variable.
    QUERY.with_borrow(|q| match q {
        Some(q) => {
            let query: Rc<Query<'static>> = q.clone();
            let query: Rc<Query<'tcx>> = unsafe { std::mem::transmute(query) };
            Some(query)
        }
        None => None,
    })
}

/// -V alloc-check: the merged crate only shows the impls that Verus translated, but rustc uses
/// every impl in the program. An impl that Verus does not see (one outside `verus!` that Verus
/// does not import, or one in a dependency whose .vir is not imported) is unchecked, so it is
/// rejected if it
/// - implements `vstd::alloc_check::AllocFreeDrop` or `vstd::alloc_check::BoundedAllocator` (the
///   drop rule trusts these bounds), or
/// - defines a method whose trait declaration has an `allocates` bound (callers rely on the
///   bound for every implementation).
/// (No impl in the toolchain can implement these traits. The traits that vstd specifies are not
/// among them: vstd's bounds on their declarations constrain only std's own implementations.)
fn check_impls_outside_vir(ctxt: &Context, krate: &Krate) -> Result<(), VirErr> {
    let tcx = ctxt.tcx;
    let bounded_decls: HashSet<&Path> = krate
        .functions
        .iter()
        .filter(|f| {
            f.x.allocates.is_some()
                && matches!(f.x.kind, vir::ast::FunctionKind::TraitMethodDecl { .. })
        })
        .map(|f| &f.x.name.path)
        .collect();
    // (vstd's bounds on the method declarations of the traits it specifies, std's, are
    // per-implementation cost terms, constrained only for std's own types: see
    // `vstd::std_specs::iter::iter_adapter_cost`; other `external_trait_specification`s may not
    // have bounds, see `check_merged_krate`)
    let vstd_specified: HashSet<&Path> = krate
        .traits
        .iter()
        .filter(|t| t.x.proxy.as_ref().is_some_and(|px| px.x.is_vstd_path()))
        .map(|t| &t.x.name)
        .collect();
    let mut traits_of_interest: HashSet<Path> = krate
        .functions
        .iter()
        .filter(|f| bounded_decls.contains(&f.x.name.path))
        .filter_map(|f| match &f.x.kind {
            vir::ast::FunctionKind::TraitMethodDecl { trait_path, .. } => Some(trait_path.clone()),
            _ => None,
        })
        .filter(|p| !vstd_specified.contains(p))
        .collect();
    // the vstd marker traits that the drop rule trusts
    let marker_paths: HashSet<Path> = krate
        .traits
        .iter()
        .map(|t| &t.x.name)
        .filter(|p| {
            let name = vir::ast_util::path_as_friendly_rust_name(p);
            name == "vstd::alloc_check::AllocFreeDrop"
                || name == "vstd::alloc_check::BoundedAllocator"
                || vir::alloc_check::op_marker(p).is_some()
        })
        .cloned()
        .collect();
    traits_of_interest.extend(marker_paths.iter().cloned());
    if traits_of_interest.is_empty() {
        return Ok(());
    }
    let vir_funs: HashSet<&Path> = krate.functions.iter().map(|f| &f.x.name.path).collect();
    let vir_impls: HashSet<&Path> = krate.trait_impls.iter().map(|i| &i.x.impl_path).collect();
    for trait_def_id in tcx.all_traits_including_private() {
        let trait_path = ctxt.def_id_to_vir_path(trait_def_id);
        if !traits_of_interest.contains(&trait_path) {
            continue;
        }
        let is_afd = marker_paths.contains(&trait_path);
        for impl_def_id in tcx.all_impls(trait_def_id) {
            let span = tcx.def_span(impl_def_id);
            let unchecked = if is_afd {
                !vir_impls.contains(&ctxt.def_id_to_vir_path(impl_def_id))
            } else {
                tcx.associated_items(impl_def_id).in_definition_order().any(|item| {
                    item.trait_item_def_id().is_some_and(|t| {
                        bounded_decls.contains(&ctxt.def_id_to_vir_path(t))
                            && !vir_funs.contains(&ctxt.def_id_to_vir_path(item.def_id))
                    })
                })
            };
            if unchecked {
                let msg = if is_afd {
                    format!(
                        "-V alloc-check: this `{}` impl is not checked by Verus (every impl of it must be one that Verus checks)",
                        vir::ast_util::path_as_friendly_rust_name(&trait_path)
                            .rsplit("::")
                            .next()
                            .unwrap_or_default()
                    )
                } else {
                    format!(
                        "-V alloc-check: this impl defines a method of `{}` whose declaration has an `allocates` bound, but Verus does not check this impl",
                        vir::ast_util::path_as_friendly_rust_name(&trait_path)
                    )
                };
                return Err(vir::messages::error(&crate::spans::err_air_span(span), msg));
            }
        }
    }
    // A `BoundedAllocator`'s `Clone` impls must be ones that Verus checks too: std's containers
    // clone their allocator where Verus does not see it, which the marker rule bounds by the
    // clone impls that Verus sees (`vir::alloc_check::check_bounded_allocator_impls`). (All the
    // `Clone` impls of the allocator's type constructor, whatever their instance.)
    let bounded = tcx.all_traits_including_private().find(|t| {
        vir::ast_util::path_as_friendly_rust_name(&ctxt.def_id_to_vir_path(*t))
            == "vstd::alloc_check::BoundedAllocator"
    });
    if let (Some(bounded), Some(clone_trait)) = (bounded, tcx.lang_items().clone_trait()) {
        let mut adts: HashSet<DefId> = HashSet::new();
        for impl_def_id in tcx.all_impls(bounded) {
            if tcx.crate_name(impl_def_id.krate).as_str() == "vstd" {
                continue;
            }
            let mut ty = tcx.type_of(impl_def_id).instantiate_identity().skip_normalization();
            while let rustc_middle::ty::Ref(_, inner, _) = ty.kind() {
                ty = *inner;
            }
            if let Some(adt) = ty.ty_adt_def() {
                adts.insert(adt.did());
            }
        }
        if !adts.is_empty() {
            for impl_def_id in tcx.all_impls(clone_trait) {
                let ty = tcx.type_of(impl_def_id).instantiate_identity().skip_normalization();
                let Some(adt) = ty.ty_adt_def() else { continue };
                if !adts.contains(&adt.did()) {
                    continue;
                }
                let unchecked =
                    tcx.associated_items(impl_def_id).in_definition_order().any(|item| {
                        item.ident(tcx).as_str() == "clone"
                            && !vir_funs.contains(&ctxt.def_id_to_vir_path(item.def_id))
                    });
                if unchecked {
                    return Err(vir::messages::error(
                        &crate::spans::err_air_span(tcx.def_span(impl_def_id)),
                        format!(
                            "-V alloc-check: this `Clone` impl is for a `BoundedAllocator` (`{}`), so it must be one that Verus checks (std's containers clone their allocator where Verus does not see it)",
                            tcx.def_path_str(adt.did())
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}
