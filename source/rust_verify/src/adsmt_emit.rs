//! Y4 R7.11 cert-emit bridge: after a 0-error `-V adsmt` run, turn the proof
//! certificates lu-smt wrote to `$ADSMT_CERT_DIR` into Isabelle/HOL or Rocq
//! source via the `adsmt-emit` runtime.
//!
//! Pipeline (all rc.32 adsmt surface, validated end-to-end):
//!
//! ```text
//! lu-smt --emit-cert-dir $ADSMT_CERT_DIR      (P2a, air::smt_process::solver_argv)
//!   -> $ADSMT_CERT_DIR/<seq>.cert.<ext>       (canonical adsmt-cert::Certificate)
//! adsmt-emit run <target> --cert <f> --out <o>   (this module)
//!   -> <out-dir>/<seq>.{thy,v}                (ITP source)
//! ```
//!
//! The `adsmt-emit` toolchain is NOT a per-prover binary; it is a single
//! package-manager binary (`adsmt-emit`) that runs WASM emitter modules
//! resolved from an `adsmt-emit.lock` in the working directory.  Installing the
//! emitters (`adsmt-emit install` against an `adsmt-emit.toml` manifest) is a
//! user-side precondition, exactly like having z3/cvc5 on `$PATH`.  This module
//! only invokes `adsmt-emit run`; a missing toolchain or lockfile is reported,
//! not fatal.
//!
//! Env knobs (mirroring the §3.5.I env-driven backend integration):
//! - `ADSMT_CERT_DIR`         — where lu-smt wrote the certs (required).
//! - `VERUS_ADSMT_CERT_FORMAT`— `cbor` (default) | `json`; the cert file ext.
//! - `VERUS_ADSMT_EMIT_PATH`  — the `adsmt-emit` binary (default `adsmt-emit`).

use crate::config::Args;
use air::context::SmtSolver;

struct EmitTarget {
    /// The `adsmt-emit run <name>` target id.
    name: &'static str,
    /// Output file extension for this prover.
    out_ext: &'static str,
    /// Per-run out-dir override (`-V emit-<name>=<dir>`), if any.
    out_dir: Option<String>,
}

/// Post-verification hook.  Call only on a successful (0-error) `-V adsmt` run;
/// it self-gates on the solver and on at least one `-V emit-*` request.
pub fn run_cert_emit(args: &Args) {
    if !matches!(args.solver, SmtSolver::Adsmt) {
        return;
    }

    let mut targets: Vec<EmitTarget> = Vec::new();
    if let Some(out) = &args.emit_isabelle {
        targets.push(EmitTarget { name: "isabelle", out_ext: "thy", out_dir: out.clone() });
    }
    if let Some(out) = &args.emit_rocq {
        targets.push(EmitTarget { name: "rocq", out_ext: "v", out_dir: out.clone() });
    }
    if targets.is_empty() {
        return;
    }

    let cert_dir = match std::env::var("ADSMT_CERT_DIR") {
        Ok(d) if !d.is_empty() => d,
        _ => {
            eprintln!(
                "warning: -V emit-* requested but ADSMT_CERT_DIR is unset; nothing to emit \
                 (set ADSMT_CERT_DIR so -V adsmt writes certs there)"
            );
            return;
        }
    };
    let cert_ext = match std::env::var("VERUS_ADSMT_CERT_FORMAT") {
        Ok(f) if !f.is_empty() => f,
        _ => "cbor".to_string(),
    };
    let emit_bin =
        std::env::var("VERUS_ADSMT_EMIT_PATH").unwrap_or_else(|_| "adsmt-emit".to_string());

    // Collect `<seq>.cert.<ext>` certs, sorted by name (== check-sat order).
    let suffix = format!(".cert.{}", cert_ext);
    let mut certs: Vec<std::path::PathBuf> = match std::fs::read_dir(&cert_dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| {
                p.file_name().and_then(|n| n.to_str()).map(|n| n.ends_with(&suffix)).unwrap_or(false)
            })
            .collect(),
        Err(e) => {
            eprintln!("warning: -V emit-*: cannot read ADSMT_CERT_DIR {}: {}", cert_dir, e);
            return;
        }
    };
    certs.sort();

    if certs.is_empty() {
        eprintln!(
            "warning: -V emit-*: no {} certs in {} (lu-smt emits a cert only per `unsat` \
             check-sat; a fully-trivial crate may produce none)",
            suffix, cert_dir
        );
        return;
    }

    for target in &targets {
        let out_dir = target
            .out_dir
            .clone()
            .unwrap_or_else(|| format!("{}/emit-{}", cert_dir, target.name));
        if let Err(e) = std::fs::create_dir_all(&out_dir) {
            eprintln!("warning: -V emit-{}: cannot create {}: {}", target.name, out_dir, e);
            continue;
        }

        let mut ok = 0usize;
        let mut failed = 0usize;
        for cert in &certs {
            // `<seq>.cert.<ext>` -> `<seq>.<out_ext>`
            let stem = cert
                .file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.trim_end_matches(&suffix))
                .unwrap_or("cert");
            let out_file = format!("{}/{}.{}", out_dir, stem, target.out_ext);

            let status = std::process::Command::new(&emit_bin)
                .arg("run")
                .arg(target.name)
                .arg("--cert")
                .arg(cert)
                .arg("--out")
                .arg(&out_file)
                .status();
            match status {
                Ok(s) if s.success() => ok += 1,
                Ok(s) => {
                    failed += 1;
                    eprintln!(
                        "warning: `{} run {} --cert {}` exited with {}",
                        emit_bin,
                        target.name,
                        cert.display(),
                        s.code().map(|c| c.to_string()).unwrap_or_else(|| "signal".into()),
                    );
                }
                Err(e) => {
                    failed += 1;
                    eprintln!(
                        "warning: could not run `{}` ({}); is the adsmt-emit toolchain installed \
                         and on PATH (or VERUS_ADSMT_EMIT_PATH)?",
                        emit_bin, e
                    );
                    // The binary is missing; further certs will fail the same way.
                    break;
                }
            }
        }
        println!(
            "adsmt-emit ({}):: {} emitted, {} failed -> {}",
            target.name, ok, failed, out_dir
        );
    }
}
