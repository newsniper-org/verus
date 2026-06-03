pub const EXPECTED_Z3_VERSION: &str = "4.12.5";
pub const EXPECTED_CVC5_VERSION: &str = "1.1.2";
pub const EXPECTED_OXIZ_VERSION: &str = "0.0.0"; // placeholder, refined in P-vb.4
pub const EXPECTED_ADSMT_VERSION: &str = "0.0.0"; // placeholder, refined in P-vb.5
#[allow(dead_code)] // actually used in `rust_verify/util.rs`, but missed by the dead code checker, possibly due to the use of `#[path(...)]` for this file
pub const VERUS_GITHUB_BUG_REPORT_URL: &str =
    "https://github.com/verus-lang/verus/issues/new?template=bug_report.md";
