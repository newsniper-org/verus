#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V triage: when a query fails or exceeds the rlimit, each of its proof obligations is checked
// alone, the others disabled, and the ones not proved alone are reported as notes, with the
// reason the solver gave. Diagnostics only: the errors are the same as without -V triage.

fn triage_notes(err: &TestErr) -> Vec<&Diagnostic> {
    err.notes.iter().filter(|n| n.message.starts_with("triage")).collect()
}

fn primary_text(d: &Diagnostic) -> String {
    d.spans
        .iter()
        .filter(|s| s.is_primary)
        .flat_map(|s| s.text.iter().map(|t| t.text.clone()))
        .collect::<Vec<_>>()
        .join("\n")
}

test_verify_one_file_with_options! {
    // one ensures clause of three fails; the row names that clause
    #[test] triage_names_failing_ensures ["-V triage"] => verus_code! {
        spec fn f(x: int) -> int { x + 1 }
        proof fn a(x: int)
            ensures
                f(x) == x + 1,
                f(x) > x + 1, // FAILS
                f(x) >= x,
        {
        }
    } => Err(err) => {
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.contains(
            "3 proof obligations, each checked alone with the others disabled: 2 proved, 1 not proved, 0 exceeded the rlimit"
        ));
        assert!(notes[1].message.starts_with("triage (2/3): postcondition not satisfied: not proved alone"));
        assert!(primary_text(notes[1]).contains("f(x) > x + 1"));
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // nonlinear arithmetic: the solver gives up on the arithmetic, not on quantifiers
    #[test] triage_nonlinear ["-V triage"] => verus_code! {
        proof fn c(x: int, y: int)
            requires x > 0, y > 0,
            ensures x * y > 0, // FAILS
        {
        }
    } => Err(err) => {
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.contains("1 proof obligation: 0 proved, 1 not proved"));
        assert!(notes[1].message.contains("the solver gave up on nonlinear arithmetic"));
        assert!(notes[1].rendered.contains("by(nonlinear_arith)"));
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // a `by(nonlinear_arith)` query is triaged in its own context too
    #[test] triage_nonlinear_arith_block ["-V triage"] => verus_code! {
        proof fn n2(x: int, y: int)
            requires x > 1, y > 1,
        {
            assert(x * y > x + y - 2) by(nonlinear_arith) requires x > 1; // FAILS
        }
    } => Err(err) => {
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.starts_with("triage of the `by(nonlinear_arith)` assertion: 1 proof obligation: 0 proved"));
        assert!(notes[1].message.starts_with("triage (1/1): assertion failed: not proved alone"));
        assert!(!notes[1].rendered.contains("use `assert(..) by(nonlinear_arith)`"));
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // an assertion that exceeds the rlimit alone, next to one that is proved
    #[test] triage_rlimit ["-V triage"] => verus_code! {
        uninterp spec fn g(x: int) -> int;
        uninterp spec fn h(x: int) -> int;
        #[verifier::rlimit(1)]
        proof fn t(n: int)
            requires
                forall|x: int| #[trigger] g(x) == g(2 * x) + g(2 * x + 1) + h(x),
                forall|x: int| #[trigger] h(x) == h(x + 3) + g(x + 5),
        {
            assert(n + 0 == n);
            assert(g(0) == 5);
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("rlimit"));
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.contains("1 proved, 0 not proved, 1 exceeded the rlimit"));
        assert!(notes[1].message.starts_with("triage (2/2): assertion failed: exceeded the rlimit alone"));
        assert!(primary_text(notes[1]).contains("g(0) == 5"));
    }
}

test_verify_one_file_with_options! {
    // loop invariants: the row is the invariant at the end of the loop body
    #[test] triage_loop_invariant ["-V triage"] => verus_code! {
        fn l(n: u32) {
            let mut i: u32 = 0;
            while i < n
                invariant
                    i <= n,
                    i < 1000, // FAILS
                decreases n - i,
            {
                i = i + 1;
            }
        }
    } => Err(err) => {
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.starts_with("triage of the while loop:"));
        assert!(notes[1].message.contains("invariant not satisfied at end of loop body: not proved alone"));
        assert!(primary_text(notes[1]).contains("i < 1000"));
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // a call's precondition, and an assertion inside `assert .. by`
    #[test] triage_precondition_and_assert_by ["-V triage"] => verus_code! {
        proof fn p(x: int) requires x > 0 {}
        proof fn q(x: int) {
            assert(x == x) by {
                assert(x + 1 > x);
            }
            p(x); // FAILS
        }
    } => Err(err) => {
        let notes = triage_notes(&err);
        assert_eq!(notes.len(), 2);
        assert!(notes[0].message.contains("1 not proved, 0 exceeded the rlimit"));
        assert!(notes[1].message.contains("precondition not satisfied: not proved alone"));
        assert!(primary_text(notes[1]).contains("p(x)"));
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // nothing fails: no triage
    #[test] triage_nothing_to_do ["-V triage"] => verus_code! {
        proof fn a(x: int) ensures x + 1 > x {}
    } => Ok(err) => {
        assert!(triage_notes(&err).is_empty());
        assert_eq!(err.warnings.len(), 0);
    }
}

test_verify_one_file_with_options! {
    // without -V triage, no triage notes
    #[test] triage_off_by_default [] => verus_code! {
        proof fn a(x: int)
            ensures x + 1 > x + 1, // FAILS
        {
        }
    } => Err(err) => {
        assert!(triage_notes(&err).is_empty());
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // a `by(bit_vector)` query has one obligation and no push/pop: not triaged
    #[test] triage_bit_vector ["-V triage"] => verus_code! {
        proof fn b(x: u8) {
            assert(x & 1 == 1) by(bit_vector); // FAILS
        }
    } => Err(err) => {
        assert!(triage_notes(&err).is_empty());
        assert_one_fails(err);
    }
}
