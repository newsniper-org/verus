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
