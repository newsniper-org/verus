#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check, `#[verifier::fip]` (fully in-place, FP²): a fip function never deallocates on a
// normal return. Its calls are checked by the verifier (`deallocates_when` conditions of the
// callees); the drops that the compiler inserts, on the MIR of the compiled program.

test_verify_one_file_with_options! {
    #[test] fip_in_place_code_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        use vstd::std_specs::vec::spec_vec_capacity;

        pub struct Node { pub val: u64, pub next: Option<Box<Node>> }

        // reuses the box
        #[verifier::fip]
        fn halve(mut b: Box<Node>) -> (r: Box<Node>) {
            b.val = b.val / 2;
            b
        }

        // a match that moves the box out of the `Some` and builds a new `Some` around it
        #[verifier::fip]
        fn halve_opt(o: Option<Box<Node>>) -> (r: Option<Box<Node>>) {
            match o {
                Some(b) => Some(halve(b)),
                None => None,
            }
        }

        // a push into spare capacity neither allocates nor reallocates
        #[verifier::fip]
        fn push_spare(v: &mut Vec<u64>)
            requires
                old(v)@.len() < spec_vec_capacity(&*old(v)),
        {
            v.push(1);
            let _ = v.pop();
        }

        // dropping `u64`s frees nothing
        #[verifier::fip]
        fn clear(v: &mut Vec<u64>) {
            v.clear();
        }

        // fip(1): one allocation, no deallocation
        #[verifier::fip]
        fn make() -> (r: Box<u64>)
            allocates 1
        {
            Box::new(3)
        }

        #[verifier::fip]
        fn consume<T: NoDeallocDrop>(x: T) {
        }

        pub struct Handle { pub id: u64 }

        impl Drop for Handle {
            #[verifier::fip]
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }

        unsafe impl AllocFreeDrop for Handle {}

        unsafe impl NoDeallocDrop for Handle {}

        #[verifier::fip]
        fn drop_handle(h: Handle) {
            consume(h);
        }

        #[verifier::fip]
        fn drop_handle_here(h: Handle) {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_dropped_parameter_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(b: Box<u64>) {
        }
    } => Err(err) => assert_vir_error_msg(err, "a value of type `std::boxed::Box<u64>` is dropped here")
}

test_verify_one_file_with_options! {
    // moving the contents out of a box frees the box
    #[test] fip_move_out_of_box_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct N { pub v: u64 }
        #[verifier::fip]
        fn f(b: Box<N>) -> (r: N) {
            *b
        }
    } => Err(err) => assert_vir_error_msg(err, "its contents are moved out of it; reuse it instead")
}

test_verify_one_file_with_options! {
    #[test] fip_conditional_drop_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(c: bool, b: Box<u64>) -> (r: Option<Box<u64>>) {
            if c { Some(b) } else { None }
        }
    } => Err(err) => assert_vir_error_msg(err, "is dropped here")
}

test_verify_one_file_with_options! {
    // a growth from an existing buffer reallocates it (frees the old block)
    #[test] fip_push_may_reallocate ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(v: &mut Vec<u64>)
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_clear_of_boxes_fails ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f(v: &mut Vec<Box<u64>>) {
            v.clear();
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_calls_non_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn g(x: u64) -> (r: u64) allocates 0 { x }
        #[verifier::fip]
        fn f() -> (r: u64) {
            g(1)
        }
    } => Err(err) => assert_vir_error_msg(err, "is not `#[verifier::fip]` and has no `deallocates_when` condition")
}

test_verify_one_file_with_options! {
    // the drop rule only needs `AllocFreeDrop`, but dropping a `T` may deallocate
    #[test] fip_generic_drop_needs_marker ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f<T: vstd::alloc_check::AllocFreeDrop>(x: T) {
        }
    } => Err(err) => assert_vir_error_msg(err, "a value of type `T` is dropped here")
}

test_verify_one_file_with_options! {
    #[test] no_dealloc_drop_impl_checked ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct H { pub b: Box<u64> }
        unsafe impl vstd::alloc_check::AllocFreeDrop for H {}
        unsafe impl vstd::alloc_check::NoDeallocDrop for H {}
    } => Err(err) => assert_vir_error_msg(err, "this `NoDeallocDrop` impl is not accepted")
}

test_verify_one_file_with_options! {
    #[test] no_dealloc_drop_impl_needs_fip_drop ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub struct H { pub id: u64 }
        impl Drop for H {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 0
            {
            }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for H {}
        unsafe impl vstd::alloc_check::NoDeallocDrop for H {}
    } => Err(err) => assert_vir_error_msg(err, "its `Drop::drop` is not `#[verifier::fip]`")
}

test_verify_one_file_with_options! {
    #[test] deallocates_when_condition_proved ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        fn maybe_free(v: &mut Vec<u64>, b: bool)
            allocates deallocates_when(0int, b)
        {
        }
        #[verifier::fip]
        fn f(v: &mut Vec<u64>) {
            maybe_free(v, false);
        }
        #[verifier::fip]
        fn g(v: &mut Vec<u64>, b: bool) {
            maybe_free(v, b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] deallocates_when_needs_unverified_body ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(b: bool)
            allocates deallocates_when(0int, b)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "only a specification without a verified body")
}

test_verify_one_file_with_options! {
    #[test] fip_needs_alloc_check ["vstd"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn f() {}
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::fip]` needs -V alloc-check")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_not_supported_yet ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn f() {}
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::fip(strict)]` (constant stack space) is not supported yet")
}
