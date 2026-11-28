//! Lemmas that the steps of `assert(P) by(tactic) { .. }` scripts use (a fork extension).
//!
//! The `induct` step proves its two cases as `assert forall` statements whose bodies are the
//! base case and the step of the script, and then calls one of these lemmas, whose `requires`
//! are those statements: nothing is assumed.
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// Induction on a `nat` (the step `induct(n)`): `p(n)` holds if `p(0)` holds, and if `p(k)`
/// holds for every `k > 0` for which `p(k - 1)` holds.
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::tactic::lemma_induct_nat")]
pub proof fn lemma_induct_nat(p: spec_fn(nat) -> bool, n: nat)
    requires
        forall|k: nat| k == 0 ==> #[trigger] p(k),
        forall|k: nat| k > 0 && p((k - 1) as nat) ==> #[trigger] p(k),
    ensures
        p(n),
    decreases n,
{
    if n > 0 {
        lemma_induct_nat(p, (n - 1) as nat);
    }
}

/// Induction on an `int` from `lo` (the step `induct(i, from(lo))`): `p(i)` holds for `i >= lo`
/// if `p(lo)` holds, and if `p(k)` holds for every `k > lo` for which `p(k - 1)` holds.
pub proof fn lemma_induct_int_from(p: spec_fn(int) -> bool, lo: int, i: int)
    requires
        lo <= i,
        forall|k: int| k == lo ==> #[trigger] p(k),
        forall|k: int| k > lo && p(k - 1) ==> #[trigger] p(k),
    ensures
        p(i),
    decreases i - lo,
{
    if i > lo {
        lemma_induct_int_from(p, lo, i - 1);
    }
}

} // verus!
