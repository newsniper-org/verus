#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Stage 1: the `allocates` clause is parsed and carried into VIR; it has no effect on verification yet.

test_verify_one_file! {
    #[test] allocates_literal_and_param_ok verus_code! {
        use vstd::prelude::*;
        fn make(x: u8) -> (r: Box<u8>)
            ensures *r == x
            allocates 1
        {
            Box::new(x)
        }

        fn fill(v: &mut Vec<u8>, n: usize)
            allocates n
        {
        }

        fn parenthesized(n: usize)
            allocates(n + 1)
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] allocates_on_external_body_ok verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn leaf(x: u8) -> Box<u8>
            allocates 1
        {
            Box::new(x)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] allocates_spec_fn_rejected verus_code! {
        spec fn f(x: nat) -> nat
            allocates 0
        {
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "an `allocates` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] allocates_proof_fn_rejected verus_code! {
        proof fn f(x: nat)
            allocates x
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `allocates` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] allocates_exec_expr_rejected verus_code! {
        fn g() -> u8 {
            3
        }

        fn f()
            allocates g()
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::g` with mode exec")
}

test_verify_one_file! {
    #[test] allocates_two_exprs_rejected verus_code! {
        fn f()
            allocates 1, 2
        {
        }
    } => Err(err) => assert_help_error_msg(err, "allocates takes exactly one expression, e.g. `allocates n`")
}

test_verify_one_file! {
    #[test] allocates_is_not_a_reserved_word verus_code! {
        fn allocates(allocates: u8) -> u8 {
            allocates
        }

        fn g() {
            let allocates = allocates(1);
        }
    } => Ok(())
}
