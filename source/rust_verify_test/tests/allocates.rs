#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Without -V alloc-check, the `allocates` clause is parsed and carried into VIR but not checked.

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

// With -V alloc-check: a ghost counter, charged with the callee's `allocates` bound at each exec
// call, must stay within the function's own bound at every normal return.

const ALLOC_LEAF: &str = verus_code_str! {
    use vstd::prelude::*;
    #[verifier::external_body]
    fn mk(x: u8) -> (r: Box<u8>)
        ensures *r == x
        allocates 1
    {
        Box::new(x)
    }
};

test_verify_one_file_with_options! {
    #[test] alloc_check_straight_line ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn zero(x: u8) -> (r: u8)
            ensures r == x
            allocates 0
        {
            x
        }

        fn two(x: u8)
            allocates 2
        {
            let _a = mk(x);
            let _b = mk(x);
        }

        fn two_wrong(x: u8)
            allocates 1 // FAILS
        {
            let _a = mk(x);
            let _b = mk(x);
        }

        fn branch(n: u8)
            allocates if n > 3 { 1int } else { 0int }
        {
            if n > 3 {
                let _a = mk(n);
            }
        }

        fn calls_zero()
            allocates 0
        {
            let _x = zero(1);
        }

        fn nested()
            allocates 3
        {
            two(1);
            let _c = mk(2);
        }

        fn nested_wrong()
            allocates 2 // FAILS
        {
            two(1);
            let _c = mk(2);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_unspecified_callee_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn no_spec(x: u8) -> u8 {
            x
        }

        fn calls_no_spec()
            allocates 0
        {
            let _y = no_spec(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot bound the allocations of this call: `test_crate::no_spec` has no `allocates` specification")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_loops_and_recursion ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        fn looped(n: u8)
            allocates n
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    allocated() == i,
                decreases n - i
            {
                let _a = mk(i);
                i = i + 1;
            }
        }

        fn looped_wrong(n: u8)
            allocates n // FAILS
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                    allocated() <= 2 * i,
                decreases n - i
            {
                let _a = mk(i);
                let _b = mk(i);
                i = i + 1;
            }
        }

        fn rec(n: u8)
            decreases n
            allocates n
        {
            if n > 0 {
                let _a = mk(n);
                rec(n - 1);
            }
        }

        fn mid()
            allocates 2
        {
            let _a = mk(1);
            assert(allocated() == 1);
            let _b = mk(2);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_loop_needs_counter_invariant ["vstd", "-V alloc-check"] => ALLOC_LEAF.to_string() + verus_code_str! {
        // The counter is havocked across the loop; without an invariant on it the bound cannot
        // be shown (it must not pass by accident).
        fn looped(n: u8)
            allocates n // FAILS
        {
            let mut i: u8 = 0;
            while i < n
                invariant
                    i <= n,
                decreases n - i
            {
                let _a = mk(i);
                i = i + 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] alloc_check_allocated_outside_checked_fn ["vstd", "-V alloc-check"] => verus_code! {
        fn no_bound() {
            assert(allocated() == 0);
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocated()` can only be used in the body of an exec function with an `allocates` specification")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_allocated_in_ensures_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn f()
            ensures allocated() == 0
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "`allocated()` can only be used in the body of an exec function with an `allocates` specification")
}

test_verify_one_file! {
    #[test] alloc_check_off_does_not_check verus_code! {
        fn no_spec(x: u8) -> u8 {
            x
        }

        fn wrong()
            allocates 0
        {
            let _y = no_spec(1);
        }
    } => Ok(())
}

// Drop rule: implicit drops leave no trace in VIR, so every `Drop::drop` that a checked function
// may run must be bounded by `allocates 0`.

const ALLOC_DROPS: &str = verus_code_str! {
    use vstd::prelude::*;
    pub struct Good {
        pub x: u8,
    }

    impl Drop for Good {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
            allocates 0
        {
        }
    }

    pub struct Bad {
        pub x: u8,
    }

    impl Drop for Bad {
        #[verifier::external_body]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
            let _b = Box::new(1u8);
        }
    }

    pub struct WrapBad {
        pub b: Bad,
    }

    #[verifier::external_body]
    fn mk_bad() -> Bad
        allocates 0
    {
        Bad { x: 0 }
    }
};

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_bounded_ok ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(g: Good, v: Vec<u8>, b: Box<u8>, o: Option<Box<u8>>)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_param ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(b: Bad)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_field ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(w: WrapBad)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_in_container ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p(v: Vec<Bad>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_unbounded_temporary ["vstd", "-V alloc-check"] => ALLOC_DROPS.to_string() + verus_code_str! {
        fn p() -> u8
            allocates 0
        {
            mk_bad().x
        }
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_drop_generic_rejected ["vstd", "-V alloc-check"] => verus_code! {
        fn p<T>(t: T)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "the drop of type parameter `T` cannot be bounded yet")
}

test_verify_one_file_with_options! {
    #[test] alloc_check_verified_drop_body_checked ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn mk(x: u8) -> (r: Box<u8>)
            ensures *r == x
            opens_invariants none
            no_unwind
            allocates 1
        {
            Box::new(x)
        }

        pub struct D {
            pub x: u8,
        }

        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0 // FAILS
            {
                let _b = mk(1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}
