#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `assert(P) by(tactic) { .. }`: the steps expand into ordinary proof code before the rest of
// `verus!` sees them, and that code is checked as usual; `P` is still asserted at the end.

const DEFS: &str = verus_code_str! {
    spec fn f(x: int) -> int { x + 1 }
    spec fn sum(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum((n - 1) as nat) } }
    proof fn lemma_f(x: int) ensures f(x) > x {}
    // opaque, so that only the lemma proves something about it
    #[verifier::opaque]
    spec fn g(x: int) -> int { x + 1 }
    proof fn lemma_g(x: int) ensures g(x) > x { reveal(g); }
};

test_verify_one_file! {
    #[test] split_conjunction DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) requires x > 0, y > 0 {
            assert(x > 0 && y > 0 && x + y > 0) by(tactic) { split(); }
            assert({ &&& x > 0 &&& y > 0 }) by(tactic) { split(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // the failing part is the one reported, with the step it comes from
    #[test] split_reports_the_part DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) requires x > 0 {
            assert(x > 0 && y > 0) by(tactic) { split(); } // FAILS
        }
    } => Err(err) => {
        assert!(err.errors[0].rendered.contains("from the tactic step `split` (part 2 of 2)"));
        assert_one_fails(err);
    }
}

test_verify_one_file! {
    #[test] split_with_blocks DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) {
            assert(g(x) > x && g(y) > y) by(tactic) {
                split({ apply(lemma_g(x)); }, { apply(lemma_g(y)); });
            }
        }
        proof fn u(x: int, y: int) {
            assert(g(x) > x && g(y) > y) by(tactic) { split({ apply(lemma_g(x)); }, { }); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] split_equiv_and_if DEFS.to_string() + verus_code_str! {
        proof fn t(b: bool, x: int) requires x > 0 {
            assert(x > 0 <==> 0 < x) by(tactic) { split(); intro(); }
            assert(if b { x > 0 } else { x >= 0 }) by(tactic) { split(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // the steps after `intro()` prove the body, with the bound variable in scope
    #[test] intro_forall DEFS.to_string() + verus_code_str! {
        proof fn t() {
            assert(forall|i: int| 0 <= i < 5 ==> #[trigger] f(i) > i) by(tactic) {
                intro();
                apply(lemma_f(i));
            }
            assert(forall|i: int| #![trigger g(i)] g(i) > i) by(tactic) {
                intro();
                apply(lemma_g(i));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] intro_implies_and_cases DEFS.to_string() + verus_code_str! {
        enum E { A(int), B }
        proof fn t(x: int, o: E) {
            assert(x > 0 ==> f(x) > 1) by(tactic) { intro(); }
            assert(x * x >= 0) by(tactic) {
                cases(x >= 0, { smt(nonlinear_arith, x >= 0); }, { smt(nonlinear_arith, x < 0); });
            }
            assert(o is A || o is B) by(tactic) {
                cases(match o { E::A(v) => { have(o == E::A(v)); }, E::B => smt() });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // without the step, the default fuel is not enough
    #[test] unfold_fuel DEFS.to_string() + verus_code_str! {
        proof fn t() {
            assert(sum(3) == 6) by(tactic) { unfold(sum, 4); }
            assert(sum(3) == 6) by(tactic) { compute(); }
        }
        proof fn u() {
            assert(sum(3) == 6) by(tactic) { show(); } // FAILS
        }
    } => Err(err) => {
        let shown = err.notes.iter().filter(|n| n.message.starts_with("tactic: the goal here is")).count();
        assert_eq!(shown, 1);
        assert_one_fails(err);
    }
}

test_verify_one_file! {
    #[test] inst_forall DEFS.to_string() + verus_code_str! {
        uninterp spec fn p(i: int) -> bool;
        uninterp spec fn r(i: int) -> bool;
        proof fn t(n: int)
            requires forall|i: int| #[trigger] r(i), forall|i: int| #[trigger] r(i) ==> p(i),
        {
            // only the instances give the solver the terms r(1) and r(2)
            assert(p(1) && p(2)) by(tactic) {
                inst(forall|i: int| #[trigger] r(i) ==> p(i), 1);
                inst(forall|i: int| #[trigger] r(i) ==> p(i), 2);
            }
        }
        proof fn u(n: int)
            requires forall|i: int| #[trigger] r(i), forall|i: int| #[trigger] r(i) ==> p(i),
        {
            assert(p(1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // several variables: a term that names a bound variable means the outer one
    #[test] inst_several_variables DEFS.to_string() + verus_code_str! {
        uninterp spec fn q(i: int, j: int) -> bool;
        uninterp spec fn r(i: int, j: int) -> bool;
        proof fn t(i: int, j: int)
            requires
                forall|a: int, b: int| #[trigger] r(a, b),
                forall|i: int, j: int| #[trigger] r(i, j) ==> q(i, j),
        {
            // only the instance at (j, i) gives the solver the term r(j, i)
            assert(q(j, i)) by(tactic) {
                inst(forall|i: int, j: int| #[trigger] r(i, j) ==> q(i, j), j, i);
            }
        }
        proof fn u(i: int, j: int)
            requires
                forall|a: int, b: int| #[trigger] r(a, b),
                forall|i: int, j: int| #[trigger] r(i, j) ==> q(i, j),
        {
            assert(q(j, i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // nested scripts, and ordinary proof code mixed with the steps
    #[test] nested_and_mixed DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) requires x > 0 {
            assert(f(x) > x && (y > 0 ==> f(y) > 1)) by(tactic) {
                lemma_f(x);
                assert(f(x) == x + 1);
                split({ }, { assert(y > 0 ==> f(y) > 1) by(tactic) { intro(); } });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // the steps never change what is proved
    #[test] goal_still_checked DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) { apply(lemma_f(x)); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] no_assume DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) { assume(false); }
        }
    } => Err(err) => assert_vir_error_msg(err, "are not allowed in a `by(tactic)` script")
}

test_verify_one_file! {
    // a macro that hides `admit` is caught too
    #[test] no_admit_through_macro DEFS.to_string() + verus_code_str! {
        macro_rules! cheat { () => { admit() } }
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) { have(x == x); cheat!(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "are not allowed in a `by(tactic)` script")
}

test_verify_one_file! {
    // a nested function would be checked on its own, outside the script
    #[test] no_nested_fn DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) {
                proof fn cheat() ensures false { admit(); }
                cheat();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "may not be declared in a `by(tactic)` script")
}

test_verify_one_file! {
    #[test] error_split_shape DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x > 0 ==> x >= 0) by(tactic) { split(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`split`: the goal `x > 0 ==> x >= 0` is not a conjunction")
}

test_verify_one_file! {
    #[test] error_intro_shape DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x >= 0 || x < 0) by(tactic) { intro(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`intro`: the goal `x >= 0 || x < 0` is not a `forall` or an `==>`")
}

test_verify_one_file! {
    #[test] error_split_blocks DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x && x >= x) by(tactic) { split({ }); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`split`: the goal has 2 parts, but 1 block is given")
}

test_verify_one_file! {
    #[test] error_steps_after_smt DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) { smt(); have(x == x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "no steps may follow `smt(..)` or `compute()`")
}

test_verify_one_file! {
    #[test] error_requires DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) requires x == x { smt(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`by(tactic)` does not take a `requires` clause")
}

test_verify_one_file! {
    #[test] error_inst_terms DEFS.to_string() + verus_code_str! {
        uninterp spec fn p(i: int) -> bool;
        proof fn t() {
            assert(true) by(tactic) { inst(forall|i: int, j: int| p(i) && p(j), 1); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`inst`: the fact binds 2 variables, but 1 term is given")
}

test_verify_one_file! {
    // a function of the same name is still called with a path
    #[test] step_names_with_paths DEFS.to_string() + verus_code_str! {
        proof fn split(x: int) ensures f(x) > x { lemma_f(x); }
        proof fn t(x: int) {
            assert(f(x) > x) by(tactic) { self::split(x); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // in an exec function, as for any `assert`
    #[test] in_exec_fn DEFS.to_string() + verus_code_str! {
        fn e(x: u32) requires x > 0 {
            assert(x > 0 && x >= 1) by(tactic) { split(); }
            let y = x - 1;
            assert(y < x ==> y + 1 == x) by(tactic) { intro(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // the check reaches into the blocks that the steps generate (here, `assert forall`)
    #[test] no_assume_after_intro DEFS.to_string() + verus_code_str! {
        proof fn t() {
            assert(forall|i: int| f(i) > i + 1) by(tactic) { intro(); assume(f(i) > i + 1); }
        }
    } => Err(err) => assert_vir_error_msg(err, "are not allowed in a `by(tactic)` script")
}

test_verify_one_file! {
    // a list `{ &&& .. }` in a branch keeps its braces
    #[test] split_lists DEFS.to_string() + verus_code_str! {
        proof fn t(b: bool, x: int, y: int) requires x > 0, y == 1 {
            assert(if b { &&& x > 0 &&& y > 0 } else { x >= 0 }) by(tactic) { split({ split(); }, { }); }
            assert(x > 0 && { ||| y == 1 ||| y == 2 }) by(tactic) { split(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] error_if_let DEFS.to_string() + verus_code_str! {
        enum E { A(int), B }
        proof fn t(o: E) {
            assert(if let E::A(v) = o { v == v } else { true }) by(tactic) { split(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`split`: an `if let` goal is not supported")
}

test_verify_one_file! {
    // the goal is asserted in the arm, where `x` would be the pattern's variable
    #[test] error_cases_pattern_binds_goal_name DEFS.to_string() + verus_code_str! {
        enum E { A(int), B }
        proof fn t(x: int, o: E) requires x > 0 {
            assert(x > 0) by(tactic) { cases(match o { E::A(x) => { }, E::B => { } }); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`cases`: the pattern binds `x`, which the goal also uses")
}

test_verify_one_file_with_options! {
    // the one setting where inline AIR could add an assumption
    #[test] no_inline_air ["-V allow-inline-air"] => DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) { inline_air_stmt("(assume false)"); }
        }
    } => Err(err) => assert_vir_error_msg(err, "are not allowed in a `by(tactic)` script")
}

test_verify_one_file! {
    #[test] no_nested_const DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x) by(tactic) {
                const C: u64 = 0;
                apply(lemma_f(x));
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "may not be declared in a `by(tactic)` script")
}

test_verify_one_file! {
    // the mark is only for the block a script expands to: on a `proof` block in executable code,
    // that block would otherwise be lowered without being ghost code
    #[test] tactic_mark_outside_script DEFS.to_string() + verus_code_str! {
        fn f2(y: u64) -> (r: u64) ensures r == y {
            let mut x: u64 = 0;
            proof { #![verus::internal(tactic)] x = y; }
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "is only for the block that a `by(tactic)` script expands to")
}

// `isolate(..)`: the proof of the goal (the rest of the script) is a part of the function's
// query of its own, checked with the other parts' assertions disabled, and with its own rlimit

const SUM: &str = verus_code_str! {
    spec fn sum(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum((n - 1) as nat) } }
};

test_verify_one_file! {
    // a proof that exceeds the function's rlimit passes in a part with a larger one; the rest of
    // the function keeps the function's rlimit
    #[test] isolate_rlimit SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        proof fn isolated() {
            assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
        }
        #[verifier::rlimit(0.02)]
        proof fn not_isolated() { // FAILS
            assert(sum(12) == 78) by { reveal_with_fuel(sum, 13); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("resource limit (rlimit) exceeded"));
        assert!(!err.errors[0].message.contains("isolated"));
    }
}

test_verify_one_file! {
    // the part exceeds its own rlimit: the error is at the isolated proof
    #[test] isolate_rlimit_exceeded SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(10)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) { isolate(rlimit = 0.02); unfold(sum, 13); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
        assert!(err.errors[0].spans.iter().any(|s| s.text.iter().any(|t| t.text.contains("sum(12) == 78"))));
    }
}

test_verify_one_file! {
    // a false assertion inside the isolated proof fails
    #[test] isolate_inside_fails DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x) by(tactic) {
                isolate();
                assert(f(x) > x + 1); // FAILS
                apply(lemma_f(x));
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // a false isolated goal fails
    #[test] isolate_goal_fails DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x + 1) by(tactic) { isolate(); apply(lemma_f(x)); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    // false assertions before and after the isolated proof fail too (the other part)
    #[test] isolate_outside_fails DEFS.to_string() + verus_code_str! {
        proof fn before(x: int) {
            assert(f(x) > x + 1); // FAILS
            assert(f(x) > x) by(tactic) { isolate(); apply(lemma_f(x)); }
        }
        proof fn after(x: int) {
            assert(f(x) > x) by(tactic) { isolate(); apply(lemma_f(x)); }
            assert(f(x) > x + 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    // the isolated goal holds afterwards, and the facts before it hold inside
    #[test] isolate_facts DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) requires y == x + 1 {
            lemma_g(x);
            assert(g(x) > x && y > x) by(tactic) { isolate(); split(); }
            assert(g(x) > x);
        }
    } => Ok(())
}

test_verify_one_file! {
    // parts in parts, and a part for each part of a split
    #[test] isolate_nested_and_split DEFS.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) {
            assert(g(x) > x && g(y) > y) by(tactic) {
                split({ isolate(); apply(lemma_g(x)); }, { isolate(rlimit = 5); apply(lemma_g(y)); });
            }
            assert(g(x) > x) by(tactic) {
                isolate();
                assert(g(y) > y) by(tactic) { isolate(); apply(lemma_g(y)); }
                apply(lemma_g(x));
            }
        }
        proof fn u(x: int, y: int) {
            assert(g(x) > x && g(y) > y) by(tactic) { split({ isolate(); apply(lemma_g(x)); }, { isolate(); }); } // FAILS
        }
    } => Err(err) => {
        assert!(err.notes.iter().any(|n| n.message.contains("the parts after the one that failed were not checked")));
        assert_one_fails(err);
    }
}

test_verify_one_file! {
    // inside a loop body, which is a query of its own
    #[test] isolate_in_loop DEFS.to_string() + verus_code_str! {
        fn l(n: u32) {
            let mut i: u32 = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                proof {
                    assert(g(i as int) > i) by(tactic) { isolate(); apply(lemma_g(i as int)); }
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] isolate_no_cheating ["--no-cheating"] => DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(g(x) > x) by(tactic) { isolate(rlimit = 5); apply(lemma_g(x)); }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // -V triage on a query checked in parts
    #[test] isolate_with_triage ["-V triage"] => DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(g(x) > x + 1) by(tactic) { isolate(); apply(lemma_g(x)); } // FAILS
        }
    } => Err(err) => {
        assert!(err.notes.iter().any(|n| n.message.starts_with("triage of the function body check")));
        assert_one_fails(err);
    }
}

test_verify_one_file! {
    #[test] error_isolate_option DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) { isolate(time = 3); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`isolate`: expected `isolate()`, with the options")
}

test_verify_one_file! {
    #[test] error_isolate_twice DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) { isolate(rlimit = 1, rlimit = 2); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`isolate`: expected `isolate()`, with the options")
}

test_verify_one_file! {
    // the mark is only for the block that `isolate(..)` expands to
    #[test] isolate_mark_outside_script DEFS.to_string() + verus_code_str! {
        fn f2(y: u64) -> (r: u64) ensures r == y {
            let mut x: u64 = 0;
            #[verus::internal(isolate())] { x = y; }
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "is only for the block that `isolate(..)` in a `by(tactic)` script expands to")
}

test_verify_one_file! {
    // the rest of the function keeps the function's rlimit
    #[test] isolate_rlimit_rest SUM.to_string() + verus_code_str! {
        spec fn sum2(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum2((n - 1) as nat) } }
        #[verifier::rlimit(0.02)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
            assert(sum2(12) == 78) by { reveal_with_fuel(sum2, 13); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("resource limit (rlimit) exceeded"));
        assert!(!err.errors[0].message.contains("isolated"));
    }
}

test_verify_one_file! {
    // each assertion is in the part of its innermost isolate, with that part's rlimit
    #[test] isolate_rlimit_nested SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) {
                isolate(rlimit = 0.02);
                assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // a loop body's query is checked in parts too
    #[test] isolate_rlimit_in_loop SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        fn l(n: u32) {
            let mut i: u32 = 0;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                proof {
                    assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
                }
                i = i + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // and the body of a `#[verifier::nonlinear]` function
    #[test] isolate_rlimit_nonlinear_fn SUM.to_string() + verus_code_str! {
        #[verifier::nonlinear]
        #[verifier::rlimit(0.02)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
        }
    } => Ok(())
}

test_verify_one_file! {
    // an isolated part that exceeds its rlimit is reported at its goal, not at an assertion before
    #[test] isolate_rlimit_exceeded_at_goal SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(10)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) {
                isolate(rlimit = 0.02);
                have(sum(0) == 0);
                unfold(sum, 13);
            }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
        assert!(err.errors[0].spans.iter().any(|s| s.text.iter().any(|t| t.text.contains("sum(12) == 78"))));
    }
}

// `isolate(backend = ..)`: an isolated proof checked by another solver, in a context of its own

test_verify_one_file_with_options! {
    // with the encoding for cvc5, cvc5 checks the isolated proof; the query counts only if both
    // solvers find their parts valid
    #[test] isolate_backend_cvc5 ["-V cvc5-smtlib"] => DEFS.to_string() + verus_code_str! {
        proof fn ok(x: int) {
            assert(f(x) > x) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); }
            assert(f(x) > x) by(tactic) { isolate(backend = z3, rlimit = 5); apply(lemma_f(x)); }
        }
        proof fn bad_in(x: int) {
            assert(f(x) > x + 1) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); } // FAILS
        }
        proof fn bad_out(x: int) {
            assert(f(x) > x) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); }
            assert(f(x) > x + 1); // FAILS
        }
        // and the attribute form
        proof fn ens_ok(x: int)
            ensures
                #![verifier::tactic(isolate(backend = cvc5))]
                f(x) > x,
        {
            lemma_f(x);
        }
        proof fn ens_bad(x: int)
            ensures
                #![verifier::tactic(isolate(backend = cvc5))]
                f(x) > x + 1, // FAILS
        {
            lemma_f(x);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    // the count of verified functions: one whose part for cvc5 fails is not verified
    #[test] isolate_backend_count ["-V cvc5-smtlib", "--output-json"] => verus_code! {
        spec fn f(x: int) -> int { x + 1 }
        proof fn lemma_f(x: int) ensures f(x) > x {}
        proof fn ok(x: int) {
            assert(f(x) > x) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); }
        }
        proof fn bad(x: int) {
            assert(f(x) > x + 1) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); } // FAILS
        }
    } => Err(err) => {
        let json = err.json_output.as_ref().unwrap();
        let results = &json["verification-results"];
        // lemma_f and ok
        assert_eq!(results["verified"], 2);
        assert_eq!(results["errors"], 1);
        assert_one_fails(err);
    }
}

test_verify_one_file_with_options! {
    // a cvc5 run cannot set the rlimit of its own context once it has started: a part with an
    // rlimit is checked in a cvc5 context of its own; `backend = z3` goes to Z3
    #[test] isolate_cvc5_run ["cvc5"] => SUM.to_string() + verus_code_str! {
        spec fn f(x: int) -> int { x + 1 }
        proof fn lemma_f(x: int) ensures f(x) > x {}
        proof fn ok(x: int) {
            assert(f(x) > x) by(tactic) { isolate(backend = z3); apply(lemma_f(x)); }
            assert(f(x) > x) by(tactic) { isolate(rlimit = 5); apply(lemma_f(x)); }
        }
        proof fn tiny() {
            assert(sum(12) == 78) by(tactic) { isolate(rlimit = 0.0001); unfold(sum, 13); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.starts_with("isolated proof, checked by cvc5: "));
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
        assert!(err.warnings.is_empty());
    }
}

test_verify_one_file_with_options! {
    // the part's rlimit, set when its context starts (cvc5 takes it only then)
    #[test] isolate_backend_cvc5_rlimit ["-V cvc5-smtlib"] => SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        proof fn t() {
            assert(sum(12) == 78) by(tactic) { isolate(backend = cvc5, rlimit = 10); unfold(sum, 13); }
        }
        #[verifier::rlimit(10)]
        proof fn u() {
            assert(sum(12) == 78) by(tactic) { isolate(backend = cvc5, rlimit = 0.001); unfold(sum, 13); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.starts_with("isolated proof, checked by cvc5: "));
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
    }
}

test_verify_one_file! {
    // with the encoding for Z3, cvc5 is refused, and the proof does not count as verified
    #[test] isolate_backend_needs_encoding DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(f(x) > x) by(tactic) { isolate(backend = cvc5); apply(lemma_f(x)); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`isolate(backend = cvc5)` needs the encoding for cvc5")
}

test_verify_one_file! {
    // the run's own solver: an ordinary part
    #[test] isolate_backend_same_solver DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(g(x) > x) by(tactic) { isolate(backend = z3); apply(lemma_g(x)); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] error_isolate_backend DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) { isolate(backend = yices); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`isolate`: expected `isolate()`, with the options")
}

// `#[verifier::tactic(isolate(..))]` on an `ensures` clause (its checks, at every return, are a
// part of their own) or on a function (all its `ensures` checks)

test_verify_one_file! {
    #[test] isolate_ensures_clause SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        proof fn clause(b: bool)
            ensures
                #![verifier::tactic(isolate(rlimit = 10))]
                sum(12) == 78,
        {
            if b { reveal_with_fuel(sum, 13); return; }
            reveal_with_fuel(sum, 13);
        }
        #[verifier::rlimit(0.02)]
        #[verifier::tactic(isolate(rlimit = 10))]
        proof fn whole_fn()
            ensures sum(12) == 78,
        {
            reveal_with_fuel(sum, 13);
        }
        #[verifier::rlimit(0.02)]
        proof fn not_isolated() // FAILS
            ensures sum(12) == 78,
        {
            reveal_with_fuel(sum, 13);
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("resource limit (rlimit) exceeded"));
        assert!(!err.errors[0].message.contains("isolated"));
    }
}

test_verify_one_file! {
    // an isolated clause that does not hold fails, and so does one that is not isolated
    #[test] isolate_ensures_fails DEFS.to_string() + verus_code_str! {
        proof fn t(x: int)
            ensures
                #![verifier::tactic(isolate())]
                f(x) > x + 1, // FAILS
                f(x) > x,
        {
            lemma_f(x);
        }
        proof fn u(x: int)
            ensures
                #![verifier::tactic(isolate())]
                f(x) > x,
                f(x) > x + 1, // FAILS
        {
            lemma_f(x);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] isolate_ensures_rlimit_exceeded SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(10)]
        proof fn t()
            ensures
                #![verifier::tactic(isolate(rlimit = 0.02))]
                sum(12) == 78,
        {
            reveal_with_fuel(sum, 13);
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
        assert!(err.errors[0].spans.iter().any(|s| s.text.iter().any(|t| t.text.contains("sum(12) == 78"))));
    }
}

test_verify_one_file! {
    #[test] error_isolate_attr_misplaced DEFS.to_string() + verus_code_str! {
        proof fn t(x: int) {
            assert(#[verifier::tactic(isolate())] (x == x));
        }
    } => Err(err) => assert_vir_error_msg(err, "is only allowed on an `ensures` clause or a function")
}

test_verify_one_file! {
    #[test] error_isolate_attr_option DEFS.to_string() + verus_code_str! {
        proof fn t(x: int)
            ensures
                #![verifier::tactic(isolate(time = 3))]
                x == x,
        {
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("`isolate`: expected `isolate()`, with the options")))
}

test_verify_one_file! {
    // a clause with its own attribute is a part of its own; the function's covers the others
    #[test] isolate_ensures_fn_and_clause SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        #[verifier::tactic(isolate(rlimit = 10))]
        proof fn t()
            ensures
                sum(12) == 78,
                #![verifier::tactic(isolate(rlimit = 0.001))]
                sum(12) == 78,
        {
            reveal_with_fuel(sum, 13);
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("rlimit) exceeded in the proof isolated here"));
    }
}

test_verify_one_file! {
    #[test] error_isolate_attr_returns DEFS.to_string() + verus_code_str! {
        fn r(x: u8) -> (y: u8)
            returns
                #![verifier::tactic(isolate())]
                x,
        {
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "is only allowed on an `ensures` clause or a function")
}

test_verify_one_file! {
    #[test] error_isolate_attr_trait_decl DEFS.to_string() + verus_code_str! {
        trait T {
            #[verifier::tactic(isolate(rlimit = 5))]
            proof fn p() ensures true;
        }
    } => Err(err) => assert_vir_error_msg(err, "is not allowed on a trait method declaration")
}

test_verify_one_file! {
    #[test] error_isolate_attr_struct DEFS.to_string() + verus_code_str! {
        #[verifier::tactic(isolate())]
        struct S { x: u8 }
    } => Err(err) => assert_vir_error_msg(err, "is only allowed on an `ensures` clause or a function")
}

test_verify_one_file! {
    // a clause of a function with parameter patterns
    #[test] isolate_ensures_param_pattern SUM.to_string() + verus_code_str! {
        #[verifier::rlimit(0.02)]
        proof fn t((a, b): (nat, nat))
            ensures
                a + b == b + a,
                #![verifier::tactic(isolate(rlimit = 10))]
                sum(12) + a == 78 + a,
        {
            reveal_with_fuel(sum, 13);
        }
    } => Ok(())
}

// `cases(e)` on a value of an enum: the rest of the script in an arm for each variant

const ENUM: &str = verus_code_str! {
    enum E { A, B(int), C { x: int } }
    spec fn f(e: E) -> int { match e { E::A => 1, E::B(n) => 2, E::C { x } => 3 } }
};

test_verify_one_file! {
    // each variant is a case of its own: the one that fails is named
    #[test] cases_enum ENUM.to_string() + verus_code_str! {
        proof fn ok(e: E) {
            assert(f(e) > 0) by(tactic) { cases(e); }
        }
        proof fn bad(e: E) {
            assert(f(e) < 3) by(tactic) { cases(e); } // FAILS
        }
        proof fn bad_b(e: E) {
            assert(f(e) != 2) by(tactic) { cases(e); } // FAILS
        }
        proof fn bad_rest(e: E) {
            assert(f(e) != 1) by(tactic) { cases(e); have(f(e) >= 1); smt(); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 3);
        let on = |goal: &str| err.errors.iter().find(|e| e.rendered.contains(goal)).expect(goal);
        assert!(on("f(e) < 3").rendered.contains("from the tactic step `cases` (`e` is `E::C`)"));
        assert!(on("f(e) != 2").rendered.contains("from the tactic step `cases` (`e` is `E::B`)"));
        // a step in the rest says in which case it failed
        assert!(on("f(e) != 1").rendered.contains("from the tactic step `smt`, where `e` is `E::A`"));
        assert!(!on("f(e) < 3").rendered.contains("`e` is `E::A`"));
    }
}

test_verify_one_file! {
    // the cases of a `bool` (as before), and of a generic enum
    #[test] cases_bool_and_generic verus_code! {
        enum O<T> { N, S(T) }
        spec fn n<T>(o: O<T>) -> int { match o { O::N => 0, O::S(_) => 1 } }
        proof fn t<T>(o: O<T>) {
            assert(n(o) >= 0) by(tactic) { cases(o); }
        }
        proof fn b(x: int) {
            assert(x * x >= 0) by(tactic) { cases(x >= 0); smt(nonlinear_arith); }
        }
        proof fn b_bad(x: int) {
            assert(x >= 0) by(tactic) { cases(x > 5); } // FAILS
        }
    } => Err(err) => {
        assert_one_fails(err.clone());
        assert!(err.errors[0].rendered.contains("from the tactic step `cases` (the condition does not hold)"));
    }
}

test_verify_one_file! {
    // the rest is copied into every arm: its own statements, an `assert forall`, a closure and
    // an isolated proof get through every copy
    #[test] cases_enum_copies ENUM.to_string() + SUM + verus_code_str! {
        proof fn t(e: E) {
            assert(f(e) > 0 && sum(3) == 6) by(tactic) {
                cases(e);
                let k: int = 2;
                assert forall|j: int| #[trigger] f(E::B(j)) == 2 by {}
                have(k + k == 4);
                split();
                isolate(rlimit = 10);
                unfold(sum, 4);
            }
        }
        proof fn nested(e: E, d: E) {
            assert(f(e) + f(d) > 1) by(tactic) { cases(e); cases(d); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] error_cases_not_enum verus_code! {
        struct P { a: int }
        enum One { X(int) }
        proof fn s(p: P) {
            assert(p.a == p.a) by(tactic) { cases(p); }
        }
    } => Err(err) => assert_vir_error_msg(err, "`cases(e)` takes a `bool` or a value of an enum")
}

test_verify_one_file! {
    #[test] error_cases_one_variant verus_code! {
        enum One { X(int) }
        proof fn s(o: One) {
            assert(o == o) by(tactic) { cases(o); }
        }
    } => Err(err) => assert_vir_error_msg(err, "has only one variant")
}

test_verify_one_file! {
    #[test] error_cases_marker_direct verus_code! {
        proof fn s(b: bool) {
            ::verus_builtin::tactic_cases(b, {});
        }
    } => Err(err) => assert_vir_error_msg(err, "is not used directly")
}

test_verify_one_file! {
    #[test] error_cases_assume_in_rest ENUM.to_string() + verus_code_str! {
        proof fn s(e: E) {
            assert(f(e) > 5) by(tactic) { cases(e); admit(); }
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("are not allowed in a `by(tactic)` script")))
}

test_verify_one_file! {
    // the block of a script outside the proof of an `assert .. by`: there, a step could move a
    // tracked value unseen by the borrow checker
    #[test] error_tactic_mark_outside_assert_by verus_code! {
        proof fn dup<T>(tracked t: T, tracked u: T) -> (tracked r: (T, T))
            ensures r.0 == t, r.1 == t
        {
            let tracked mut a = u;
            #[verus::internal(tactic)] { ::verus_builtin::tactic_cases(true, { a = t; }); }
            (a, t)
        }
    } => Err(err) => assert_vir_error_msg(err, "is only for the block that a `by(tactic)` script expands to")
}

test_verify_one_file! {
    #[test] error_tactic_mark_in_proof_block verus_code! {
        fn f(b: bool) {
            proof {
                #[verus::internal(tactic)] { ::verus_builtin::tactic_cases(b, { }); }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "is only for the block that a `by(tactic)` script expands to")
}

// `induct(n)` on a `nat`, `induct(i, from(lo))` on an `int`: the goal as a function of the
// variable, its base case and step proved by `assert forall`, and a vstd lemma

const POW2: &str = verus_code_str! {
    spec fn pow2(n: nat) -> int decreases n { if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) } }
};

test_verify_one_file_with_options! {
    // what a plain proof does not get
    #[test] induct_nat ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) {
            assert(pow2(n) >= 1) by(tactic) { induct(n); }
        }
        proof fn blocks(n: nat) {
            assert(pow2(n) >= 1) by(tactic) { induct(n, { smt(); }, { have(pow2(n) == 2 * pow2((n - 1) as nat)); }); }
        }
        proof fn without(n: nat) {
            assert(pow2(n) >= 1) by(tactic) { smt(); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // a wrong base case and a wrong step fail, each with its note
    #[test] induct_nat_fails ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn bad_base(n: nat) {
            assert(pow2(n) >= 2) by(tactic) { induct(n); } // FAILS
        }
        proof fn bad_step(n: nat) {
            assert(pow2(n) <= 1) by(tactic) { induct(n); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors.iter().any(|e| e.rendered.contains("from the tactic step `induct` (the base case, `n == 0`)")));
        assert!(err.errors.iter().any(|e| e.rendered.contains("from the tactic step `induct` (the step, `n > 0`")));
    }
}

test_verify_one_file_with_options! {
    // the base case and the step see the function's `requires` and the conditions around the
    // assertion; a bound variable, from `intro`, can be the one
    #[test] induct_context ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn r(n: nat, m: nat) requires m <= 1 {
            assert(pow2(n) >= m) by(tactic) { induct(n); }
        }
        proof fn s(n: nat, m: nat) {
            if m <= 1 {
                assert(pow2(n) >= m) by(tactic) { induct(n); }
            }
        }
        proof fn bound() {
            assert(forall|k: nat| pow2(k) >= 1) by(tactic) { intro(); induct(k); }
        }
        proof fn inner(n: nat) {
            // (the step needs `pow2(n - 1)`, for the goal for `n - 1` to apply)
            assert(forall|j: nat| j <= n ==> #[trigger] pow2(j) >= 1) by(tactic) {
                induct(n, { }, { have(pow2(n) == 2 * pow2((n - 1) as nat)); });
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] induct_int_from ["vstd"] => POW2.to_string() + verus_code_str! {
        spec fn tri(i: int) -> int decreases i when i >= 0 { if i <= 0 { 0 } else { i + tri(i - 1) } }
        proof fn t(i: int) requires i >= 0 {
            assert(tri(i) >= 0) by(tactic) { induct(i, from(0)); }
        }
        proof fn below(i: int) {
            assert(tri(i) >= 0) by(tactic) { induct(i, from(0)); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("precondition not satisfied"));
    }
}

test_verify_one_file_with_options! {
    #[test] error_induct_not_a_variable ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) {
            assert(pow2(n + 1) >= 1) by(tactic) { induct(n + 1); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("`induct`: expected the name of a variable"))
}

test_verify_one_file_with_options! {
    #[test] error_induct_not_nat ["vstd"] => verus_code! {
        proof fn t(x: int) {
            assert(x * 0 == 0) by(tactic) { induct(x); }
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("mismatched types")))
}

test_verify_one_file_with_options! {
    #[test] error_induct_from_uses_var ["vstd"] => verus_code! {
        proof fn t(x: int) {
            assert(x + 0 == x) by(tactic) { induct(x, from(x - 1)); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("may not use `x`"))
}

test_verify_one_file_with_options! {
    #[test] error_induct_assume_in_rest ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) {
            assert(pow2(n) >= 5) by(tactic) { induct(n); admit(); }
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("are not allowed in a `by(tactic)` script")))
}

test_verify_one_file_with_options! {
    // a variable start, with blocks; a hypothesis about the induction variable goes in the goal
    #[test] induct_from_var_and_hypothesis ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(i: int, lo: int) requires lo <= i, lo >= 0 {
            assert(i >= 0) by(tactic) { induct(i, from(lo), { }, { }); }
        }
        proof fn h(n: nat) requires n >= 1 {
            assert(n >= 1 ==> pow2(n) >= 2) by(tactic) {
                induct(n);
                intro();
                have(pow2(n) == 2 * pow2((n - 1) as nat));
                have(pow2(0) == 1);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // a fact about the induction variable does not hold in the cases (the variable is new there)
    #[test] induct_hypothesis_not_carried ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) requires n >= 1 {
            assert(pow2(n) >= 2) by(tactic) { induct(n); } // FAILS
        }
        proof fn u(i: int, lo: int) requires lo <= i {
            assert(i >= 0) by(tactic) { induct(i, from(lo)); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors.iter().any(|e| e.rendered.contains("(the base case, `n == 0`)")));
        assert!(err.errors.iter().any(|e| e.rendered.contains("(the base case, `i == lo`)")));
    }
}

test_verify_one_file_with_options! {
    #[test] error_induct_blocks_then_more ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) {
            assert(pow2(n) >= 1) by(tactic) { induct(n, { }, { }); smt(); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("no steps may follow `induct` with blocks"))
}

test_verify_one_file_with_options! {
    #[test] error_induct_arguments ["vstd"] => POW2.to_string() + verus_code_str! {
        proof fn t(n: nat) {
            assert(pow2(n) >= 1) by(tactic) { induct(n, { }); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("expected `induct(n)`"))
}

test_verify_one_file! {
    // inside a script (in the proof of an `assert .. by`), the mode checker allows no
    // assignment: the copies that `cases` makes cannot move a tracked value twice
    #[test] cases_no_tracked_assignment verus_code! {
        proof fn dup<T>(tracked t: T, tracked u: T) -> (tracked r: (T, T)) {
            let tracked mut a = u;
            assert(true) by(tactic) { cases(true); a = t; }
            (a, t)
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment is not allowed in `assert ... by` statement")
}

test_verify_one_file! {
    // `cases(e)` on a variable that `intro()` bound (inside the closure of an `assert forall`)
    #[test] cases_after_intro ENUM.to_string() + verus_code_str! {
        proof fn t() {
            assert(forall|e: E| f(e) > 0) by(tactic) { intro(); cases(e); }
        }
        proof fn u() {
            assert(forall|e: E| f(e) > 1) by(tactic) { intro(); cases(e); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].rendered.contains("`e` is `E::A`"));
    }
}

// `unfold(f)` followed by `split`: the goal with `f` unfolded (one level), split into its parts
// (rust_verify's `tactic_to_vir.rs`)

const INV: &str = verus_code_str! {
    #[verifier::opaque]
    spec fn inv(x: int) -> bool { x > 0 && x < 10 && x != 5 }
    spec fn sel(b: bool, x: int) -> bool { if b { x > 0 } else { x < 0 } }
    spec fn r(n: nat) -> bool decreases n { n >= 0 && (n > 0 ==> r((n - 1) as nat)) }
};

test_verify_one_file! {
    // a part that does not hold fails, with its note (the split of the text goal `inv(x)`, a
    // call, was an error before)
    #[test] unfold_split INV.to_string() + verus_code_str! {
        proof fn ok(x: int) requires x == 3 {
            assert(inv(x)) by(tactic) { unfold(inv); split(); }
        }
        proof fn bad(x: int) requires x == 5 {
            assert(inv(x)) by(tactic) { unfold(inv); split(); }
        }
        proof fn blocks(y: int) requires 0 < y < 4 {
            assert(inv(y + 1)) by(tactic) {
                unfold(inv);
                split({ }, { have(y + 1 < 10); }, { smt(); });
            }
        }
        proof fn ite(b: bool, x: int) requires b ==> x == 1, !b ==> x == -1 {
            assert(sel(b, x)) by(tactic) { unfold(sel); split(); }
        }
        // one level: `r(n - 1)` stays a call
        proof fn one_level(n: nat) requires n > 1 {
            assert(r(n)) by(tactic) { unfold(r); split(); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors.iter().any(|e| e.rendered.contains("from the tactic step `split` (part 3 of 3, after `unfold`)")));
        assert!(err.errors.iter().any(|e| e.rendered.contains("from the tactic step `split` (part 2 of 2, after `unfold`)")));
    }
}

test_verify_one_file! {
    // the steps after `unfold` and `split` (cases, and isolate in the rest shared by the parts),
    // in an exec function (erasure); the caller's argument has the source name of `f`'s bound
    // variable (a different variable)
    #[test] unfold_split_more INV.to_string() + SUM + verus_code_str! {
        #[verifier::opaque]
        spec fn allpos(s: spec_fn(int) -> int, n: int, i: int) -> bool {
            i >= 0 && forall|j: int| 0 <= j < n ==> #[trigger] s(j) > i
        }
        proof fn capture(j: int, s: spec_fn(int) -> int, n: int)
            requires j == 0, forall|k: int| 0 <= k < n ==> #[trigger] s(k) > 0
        {
            assert(allpos(s, n, j)) by(tactic) { unfold(allpos); split(); }
        }
        fn e(x: u64) requires x == 3 {
            proof {
                assert(inv(x as int)) by(tactic) { unfold(inv); split(); cases(x > 2); }
            }
        }
        #[verifier::rlimit(0.02)]
        proof fn isolated_shared(x: int) requires x == 3 {
            assert(inv(x)) by(tactic) { unfold(inv); split(); isolate(rlimit = 10); }
        }
        #[verifier::rlimit(0.02)]
        proof fn isolated(x: int) requires x == 3 {
            assert(inv(x) && sum(12) == 78) by(tactic) {
                split({ unfold(inv); split(); }, { isolate(rlimit = 10); unfold(sum, 13); });
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // a generic function of another crate (vstd)
    #[test] unfold_split_imported ["vstd"] => verus_code! {
        use vstd::relations::*;
        proof fn po(r: spec_fn(int, int) -> bool)
            requires reflexive(r), transitive(r), antisymmetric(r)
        {
            assert(partial_ordering(r)) by(tactic) { unfold(partial_ordering); split(); }
        }
        proof fn not_po(r: spec_fn(int, int) -> bool) requires reflexive(r), transitive(r) {
            assert(partial_ordering(r)) by(tactic) { unfold(partial_ordering); split(); }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].rendered.contains("from the tactic step `split` (part 3 of 3, after `unfold`)"));
    }
}

test_verify_one_file! {
    // a `split` of the goal as written expands the rest for each part: there, `unfold` and
    // `split` work on each part's goal
    #[test] unfold_split_after_text_split INV.to_string() + verus_code_str! {
        proof fn t(x: int, y: int) requires x == 3, y == 4 {
            assert(inv(x) && inv(y)) by(tactic) { split(); unfold(inv); split(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] error_unfold_split_shared_twice INV.to_string() + verus_code_str! {
        proof fn t(x: int) requires x == 3 {
            assert(inv(x)) by(tactic) { unfold(inv); split(); split(); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("give each part its own block"))
}

test_verify_one_file! {
    #[test] error_unfold_no_call INV.to_string() + verus_code_str! {
        proof fn t(x: int) requires x == 3 {
            assert(sel(true, x)) by(tactic) { unfold(inv); split(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "the goal has no call of `inv`")
}

test_verify_one_file! {
    #[test] error_unfold_not_visible verus_code! {
        mod m {
            use super::*;
            pub closed spec fn c(x: int) -> bool { x > 0 && x < 10 }
        }
        proof fn t(x: int) {
            assert(m::c(x)) by(tactic) { unfold(m::c); split(); }
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("`unfold(c)`: the body of `c` is not visible here")))
}

test_verify_one_file! {
    // the proofs of two spec functions unfold each other: an error, not an endless lowering
    #[test] error_unfold_cycle verus_code! {
        spec fn f(n: nat) -> bool decreases n {
            proof { assert(g(n) || true) by(tactic) { unfold(g); split(); } }
            n >= 0 && n >= 0
        }
        spec fn g(n: nat) -> bool decreases n {
            proof { assert(f(n) || true) by(tactic) { unfold(f); split(); } }
            n >= 0 && n >= 0
        }
    } => Err(err) => assert!(err.errors.iter().any(|e| e.message.contains("a cycle") || e.message.contains("its definition has errors")))
}

test_verify_one_file! {
    #[test] error_unfold_then_intro INV.to_string() + verus_code_str! {
        spec fn q(x: int) -> bool { forall|i: int| i > x ==> i > x - 1 }
        proof fn t(x: int) {
            assert(q(x)) by(tactic) { unfold(q); split({ intro(); }, { }); }
        }
    } => Err(err) => assert!(err.errors[0].message.contains("`intro()` on the goal after `unfold` is not supported yet"))
}

test_verify_one_file! {
    #[test] error_tactic_markers_direct verus_code! {
        proof fn t(x: int) {
            ::verus_builtin::tactic_split({ });
        }
    } => Err(err) => assert_vir_error_msg(err, "is a step of a `by(tactic)` script, and is not used directly")
}

test_verify_one_file! {
    // a parameter used several times, through fields, and an argument that is not a variable:
    // each copy of it gets its own ids
    #[test] unfold_split_fields verus_code! {
        struct P { a: u64, b: u64 }
        #[verifier::opaque]
        spec fn ok(p: P) -> bool { p.a > 0 && p.b > p.a && p.a + p.b < 100 }
        proof fn t(q: P) requires q.a == 1, q.b == 2 {
            assert(ok(q)) by(tactic) { unfold(ok); split(); }
            assert(ok(P { a: q.a, b: (q.b + 1) as u64 })) by(tactic) { unfold(ok); split(); }
        }
        fn e(x: u64) requires x == 1 {
            let p = P { a: x, b: 2 };
            proof {
                assert(ok(p)) by(tactic) { unfold(ok); split(); }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // `unfold(f)` before another `unfold` and `cases`: `f` is unfolded first (the goal calls it),
    // and the next `unfold` works on the result
    #[test] unfold_twice_and_cases verus_code! {
        #[verifier::opaque]
        spec fn g(x: int) -> bool { x > 0 && x < 10 }
        #[verifier::opaque]
        spec fn f(x: int) -> bool { g(x) && x != 5 }
        proof fn t(x: int) requires x == 3 {
            assert(f(x)) by(tactic) { unfold(f); unfold(g); split(); }
            assert(f(x)) by(tactic) { unfold(f); cases(x > 1); split(); }
        }
        proof fn u(x: int) requires x == 10 {
            assert(f(x)) by(tactic) { unfold(f); unfold(g); split(); } // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].rendered.contains("from the tactic step `split` (part 2 of 3, after `unfold`)"));
    }
}

test_verify_one_file! {
    #[test] error_unfold_when verus_code! {
        spec fn p(i: int) -> bool decreases i when i >= 0 { i >= 0 && (i == 0 || p(i - 1)) }
        proof fn t(x: int) requires x == 0 {
            assert(p(x)) by(tactic) { unfold(p); split(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "has a `decreases .. when` clause")
}

test_verify_one_file! {
    #[test] error_unfold_trigger_arg verus_code! {
        spec fn allpos(s: spec_fn(int) -> int, n: int) -> bool {
            n >= 0 && forall|j: int| 0 <= j < n ==> #[trigger] s(j) > 0
        }
        proof fn t(n: int) {
            assert(allpos(|k: int| k + 1, n)) by(tactic) { unfold(allpos); split(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "is used in a trigger of `allpos`'s body")
}

test_verify_one_file! {
    #[test] error_tactic_markers_in_script verus_code! {
        proof fn t(x: int) {
            assert(x == x) by(tactic) { ::verus_builtin::tactic_split({ }); }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not used directly")
}
