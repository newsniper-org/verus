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
    // (`explicit_tail_calls` is enabled by the test prelude)
    #[test] fip_strict_tail_recursion_accepted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn sum(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { become sum(n - 1, acc.wrapping_add(n)) }
        }
        #[verifier::fip(strict)]
        fn even(n: u64) -> (r: bool)
            decreases n
        {
            if n == 0 { true } else { become odd(n - 1) }
        }
        #[verifier::fip(strict)]
        fn odd(n: u64) -> (r: bool)
            decreases n
        {
            if n == 0 { false } else { become even(n - 1) }
        }
        // non-tail calls of functions that do not lead back here are fine
        #[verifier::fip(strict)]
        fn caller() -> (r: u64) {
            let a = sum(10, 0);
            if even(4) { a } else { 0 }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_non_tail_recursion_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn sum(n: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { 0 } else { sum(n - 1).wrapping_add(n) }
        }
    } => Err(err) => assert_vir_error_msg(err, "is not a tail call and can lead back to `sum`")
}

test_verify_one_file_with_options! {
    // a cycle with one non-tail call grows the stack by a frame per round
    #[test] fip_strict_mixed_cycle_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip(strict)]
        fn f(n: u64) -> (r: u64)
            decreases n, 1int
        {
            if n == 0 { 0 } else { become g(n) }
        }
        #[verifier::fip(strict)]
        fn g(n: u64) -> (r: u64)
            requires n > 0,
            decreases n, 0int
        {
            f(n - 1).wrapping_add(1)
        }
    } => Err(err) => assert_vir_error_msg(err, "this call of `f` is not a tail call and can lead back to `g`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_calls_non_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        fn plain(n: u64) -> (r: u64) { n }
        #[verifier::fip(strict)]
        fn f() -> (r: u64) { plain(1) }
    } => Err(err) => assert_vir_error_msg(err, "it calls `plain`, which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // a drop runs the type's destructor, which must be strict too
    #[test] fip_strict_destructor_must_be_strict ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
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
        #[verifier::fip(strict)]
        fn f(h: Handle) {
        }
    } => Err(err) => assert_vir_error_msg(err, "which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // `-V fip-lint`: suggestions for recursion that grows the stack
    #[test] fip_lint_suggestions ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }

        // in tail position, but not a tail call
        fn sum(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { sum(n - 1, acc.wrapping_add(n)) }
        }

        // in tail position with a drop pending after the call
        fn sum_v(n: u64, acc: u64, v: Vec<u8>) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { sum_v(n - 1, acc, Vec::new()) }
        }

        // recursion modulo a constructor
        fn range(n: u64) -> (r: List)
            decreases n
        {
            if n == 0 { List::Nil } else { List::Cons(n, Box::new(range(n - 1))) }
        }

        // already a tail call, and calls that are not recursive: nothing to suggest
        fn sum2(n: u64, acc: u64) -> (r: u64)
            decreases n
        {
            if n == 0 { acc } else { become sum2(n - 1, acc.wrapping_add(n)) }
        }
        fn h(n: u64) -> (r: u64) {
            sum(n, 0)
        }
    } => Ok(err) => {
        let msgs: Vec<&str> = err
            .warnings
            .iter()
            .map(|w| w.message.as_str())
            .filter(|m| m.starts_with("-V fip-lint"))
            .collect();
        assert_eq!(msgs.len(), 4, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("call of `sum` is in tail position but is not a tail call")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("call of `sum_v` is in tail position") && m.contains("a drop is pending after the call: `std::vec::Vec<u8>`")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("recursive call of `test_crate::range` is not a tail call") && m.contains("tail recursion modulo a constructor")), "{:?}", msgs);
        // the rewrite into a loop, as a suggestion
        let rewrite = err
            .warnings
            .iter()
            .find(|w| w.message.contains("`test_crate::range` can be rewritten into a loop"))
            .expect("rewrite warning");
        assert!(rewrite.rendered.contains("'__trmc: loop"), "{}", rewrite.rendered);
        assert!(rewrite.rendered.contains("__trmc_hole = match __trmc_hole"), "{}", rewrite.rendered);
    }
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }

        // a second recursive call that is not in tail position
        fn twice(n: u64) -> (r: List)
            decreases n
        {
            if n == 0 {
                List::Nil
            } else {
                let _ = twice(n - 1);
                List::Cons(n, Box::new(twice(n - 1)))
            }
        }

        // no variant without fields to hold the place of the value being built
        pub struct Cell { pub v: u64, pub next: Option<Box<Cell>> }
        fn cells(n: u64) -> (r: Cell)
            decreases n
        {
            if n == 0 { Cell { v: 0, next: None } } else { Cell { v: n, next: Some(Box::new(cells(n - 1))) } }
        }
    } => Ok(err) => {
        let msgs: Vec<&str> = err
            .warnings
            .iter()
            .map(|w| w.message.as_str())
            .filter(|m| m.contains("cannot be rewritten into a loop automatically"))
            .collect();
        assert_eq!(msgs.len(), 2, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("neither a tail call nor the only recursive call inside a constructor")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("must be an enum with a variant without fields")), "{:?}", msgs);
    }
}
