//! Bakes the `[package.metadata.adsmt] distinct_max_arity` knob from
//! `Cargo.toml` into a compile-time env var that `printer.rs` reads.
//!
//! This exists solely to make the temporary adsmt `distinct`
//! finite-domain soundness guard (see `[package.metadata.adsmt]` in
//! `Cargo.toml` and the `MultiOp::Distinct` arm in `printer.rs`)
//! fine-tunable from `Cargo.toml` without touching code.  No toml crate
//! dependency — AIR deliberately keeps its build graph minimal — so we
//! hand-scan the manifest for the one key we need.

use std::{env, fs, path::Path};

/// Falls back to this if the manifest key is absent or unparseable.
/// Chosen comfortably below lu-smt's empirical 52/53 spurious-UNSAT
/// cliff for `(distinct …)` over an uninterpreted sort.
const DEFAULT_DISTINCT_MAX_ARITY: usize = 48;

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
    let manifest = Path::new(&manifest_dir).join("Cargo.toml");
    println!("cargo:rerun-if-changed={}", manifest.display());

    let value = fs::read_to_string(&manifest)
        .ok()
        .and_then(|s| parse_distinct_max_arity(&s))
        .unwrap_or(DEFAULT_DISTINCT_MAX_ARITY);

    println!("cargo:rustc-env=VERUS_ADSMT_DISTINCT_MAX_ARITY={}", value);
}

/// Minimal scan for `distinct_max_arity = N` inside the
/// `[package.metadata.adsmt]` table.  Tolerates inline `# comments`,
/// surrounding whitespace, and ignores the key outside its table.
fn parse_distinct_max_arity(manifest: &str) -> Option<usize> {
    let mut in_table = false;
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_table = trimmed == "[package.metadata.adsmt]";
            continue;
        }
        if !in_table {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("distinct_max_arity") {
            let rest = rest.trim_start().strip_prefix('=')?.trim();
            let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
            return digits.parse().ok();
        }
    }
    None
}
