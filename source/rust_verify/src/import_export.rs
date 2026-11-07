use crate::config::Args;
use crate::spans::FileStartEndPos;
use crate::verifier::io_vir_err;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Krate, Mode, VirErr};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(crate) struct CrateMetadata {
    pub crate_id: u64,
    pub original_files: HashMap<Vec<u8>, FileStartEndPos>,
    /// The crate was verified as vstd (`--is-vstd`); -V alloc-check trusts vstd's types and
    /// drops, so it only accepts a crate named `vstd` that was
    pub built_as_vstd: bool,
    /// -V alloc-check: the SVH of the crate built from the same source (by the compilation pass
    /// of the same run). The bounds in this file are marked as checked only when it is set, and an
    /// importer only trusts them if the linked crate has this SVH (not a different build or
    /// version of it).
    pub crate_hash: Option<u128>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateWithMetadata {
    krate: Krate,
    metadata: CrateMetadata,
}

pub(crate) struct ImportOutput {
    pub(crate) vir_crates: Vec<Krate>,
    pub(crate) metadatas: Vec<CrateMetadata>,
}

pub(crate) fn import_crates(
    args: &Args,
    import_virs_via_cargo: Vec<(String, String)>,
) -> Result<ImportOutput, VirErr> {
    let mut metadatas = Vec::new();
    let mut vir_crates = Vec::new();
    for (_, file_path) in args.import.iter().chain(import_virs_via_cargo.iter()) {
        let mut file = std::io::BufReader::new(match std::fs::File::open(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not open imported library file `{file_path}`"),
                    err,
                ));
            }
        });
        let CrateWithMetadata { krate, metadata } = match bincode_next::serde::decode_from_std_read(
            &mut file,
            bincode_next::config::legacy(),
        ) {
            Ok(crate_with_metadata) => crate_with_metadata,
            Err(_e) => {
                return Err(crate::util::error(format!(
                    "failed to deserialize imported library file `{file_path}` - it may need to be rebuilt by Verus"
                )));
            }
        };
        //   let libcrate: Krate = serde_json::from_reader(file).expect("read crate from file");
        // We can also look at other packages: https://github.com/djkoloski/rust_serialization_benchmark
        vir_crates.push(krate);
        metadatas.push(metadata);
    }
    Ok(ImportOutput { vir_crates, metadatas })
}

pub(crate) fn export_crate(
    args: &Args,
    export_vir_path_via_cargo: &Option<std::path::PathBuf>,
    vir_metadata: CrateMetadata,
    vir_crate: Krate,
    alloc_checked: bool,
) -> Result<(), VirErr> {
    let export = args.export.as_ref().map(|s| s.clone().into());
    if let Some(file_path) = export.as_ref().or(export_vir_path_via_cargo.as_ref()) {
        // for efficiency's sake, prune out elements of AST that won't be needed by importers:
        let mut kratex = (*vir_crate).clone();
        // (computed while the bodies are still there)
        let touching = vir::alloc_heap::exported_touching(&vir_crate);
        kratex.functions.retain(|f| f.x.visibility.restricted_to.is_none());
        for func in kratex.functions.iter_mut() {
            let mut functionx = func.x.clone();
            if let Some(touching) = &touching {
                if functionx.mode == Mode::Exec
                    && functionx.body.is_some()
                    && !touching.contains(&functionx.name)
                {
                    let mut attrs = (*functionx.attrs).clone();
                    attrs.heap_preserving = true;
                    functionx.attrs = Arc::new(attrs);
                }
            }
            if !alloc_checked {
                let mut attrs = (*functionx.attrs).clone();
                attrs.alloc_checked_crate = false;
                functionx.attrs = Arc::new(attrs);
            }
            functionx.decrease_by = None;
            functionx.return_opaque_type_eqs = Arc::new(vec![]);
            if (functionx.mode != Mode::Spec || !functionx.body_visibility.is_public())
                && !matches!(&functionx.kind, vir::ast::FunctionKind::TraitMethodDecl { .. })
            {
                functionx.body = None;
            }
            *func = func.new_x(functionx);
        }
        let vir_crate = Arc::new(kratex);

        let mut file = std::io::BufWriter::new(match std::fs::File::create(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not create exported library file `{:?}`", file_path),
                    err,
                ));
            }
        });
        let krate_with_metadata = CrateWithMetadata { krate: vir_crate, metadata: vir_metadata };
        bincode_next::serde::encode_into_std_write(
            &krate_with_metadata,
            &mut file,
            bincode_next::config::legacy(),
        )
        .expect("write crate to file");
        //serde_json::to_writer(file, &vir_crate).expect("write crate to file");
        //serde_json::to_writer_pretty(file, &vir_crate).expect("write crate to file");
    }
    Ok(())
}
