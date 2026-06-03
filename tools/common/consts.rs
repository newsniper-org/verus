pub const EXPECTED_Z3_VERSION: &str = "4.12.5";
pub const EXPECTED_CVC5_VERSION: &str = "1.1.2";
// Used by `rust_verify::verifier::set_expected_solver_version` via the
// `#[path(...)]` import of this file from rust_verify; the dead-code
// checker doesn't follow that link.
#[allow(dead_code)]
// Tracks the Honey-Be/oxiz fork (branch `0.2.3-feat/writer`,
// submodule pin per Y4 unified-toolkit-pin.toml). Bare version
// string from oxiz/Cargo.toml workspace package.
pub const EXPECTED_OXIZ_VERSION: &str = "0.2.2";
#[allow(dead_code)]
// Tracks newsniper-org/adsmt on the testing channel
// (Y4 unified-toolkit-pin §10.6, rolling). Bare workspace version
// from ~/AD1/Cargo.toml — `adsmt-cli` (lu-smt) shares the
// workspace version through `version.workspace = true`.
pub const EXPECTED_ADSMT_VERSION: &str = "1.0.0-rc.7-1";
#[allow(dead_code)] // actually used in `rust_verify/util.rs`, but missed by the dead code checker, possibly due to the use of `#[path(...)]` for this file
pub const VERUS_GITHUB_BUG_REPORT_URL: &str =
    "https://github.com/verus-lang/verus/issues/new?template=bug_report.md";
