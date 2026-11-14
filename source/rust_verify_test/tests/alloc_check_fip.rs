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

/// A forwarding allocator for the fip allocator tests, with the given fip attributes on its
/// `allocate` and `clone` and the given fip marker impls
fn fip_allocator(alloc_fip: &str, clone_fip: &str, markers: &str) -> String {
    let code = verus_code_str! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator, NoDeallocDrop, FipAllocator, FipStrictAllocator};
        use vstd::std_specs::vec::spec_vec_capacity;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Fwd;

        impl Clone for Fwd {
            __CLONE_FIP__
            fn clone(&self) -> (r: Self)
                allocates 0
            {
                Fwd
            }
        }

        unsafe impl Allocator for Fwd {
            __ALLOC_FIP__
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                Global.allocate(layout)
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
                #[verifier::trusted_call] { unsafe { Global.deallocate(ptr, layout) } }
            }
        }

        unsafe impl AllocFreeDrop for Fwd {}
        unsafe impl NoDeallocDrop for Fwd {}
        unsafe impl BoundedAllocator for Fwd {
            open spec fn max_cost() -> int { 1 }
        }
        __MARKERS__
    };
    code.replace("__ALLOC_FIP__", alloc_fip)
        .replace("__CLONE_FIP__", clone_fip)
        .replace("__MARKERS__", markers)
}

const FIP_MARKER: &str = "unsafe impl FipAllocator for Fwd {}";
const STRICT_MARKERS: &str =
    "unsafe impl FipAllocator for Fwd {} unsafe impl FipStrictAllocator for Fwd {}";

test_verify_one_file_with_options! {
    // a vector without a buffer grows by calling its allocator's `allocate`, which for a user
    // allocator is user code: it must be fip (`FipAllocator`)
    #[test] fip_user_allocator_needs_marker ["vstd", "-V alloc-check"] => fip_allocator("", "", "") + verus_code_str! {
        #[verifier::fip]
        fn push_empty(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "only if it implements `vstd::alloc_check::FipAllocator`")
}

test_verify_one_file_with_options! {
    #[test] fip_user_allocator_generic_needs_marker ["vstd", "-V alloc-check"] => fip_allocator("", "", "") + verus_code_str! {
        #[verifier::fip]
        fn push_empty<A: Allocator + BoundedAllocator>(v: &mut Vec<u8, A>)
            requires spec_vec_capacity(&*old(v)) == 0, A::max_cost() <= 1,
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "only if it implements `vstd::alloc_check::FipAllocator`")
}

test_verify_one_file_with_options! {
    #[test] fip_allocator_accepted ["vstd", "-V alloc-check"] => fip_allocator("#[verifier::fip]", "#[verifier::fip]", FIP_MARKER) + verus_code_str! {
        #[verifier::fip]
        fn push_empty(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }

        #[verifier::fip]
        fn push_generic<A: FipAllocator>(v: &mut Vec<u8, A>)
            requires spec_vec_capacity(&*old(v)) == 0, A::max_cost() <= 1,
            allocates 1
        {
            v.push(1);
        }

        #[verifier::fip]
        fn mk() -> (r: Vec<u8, Fwd>)
            allocates 1
        {
            Vec::with_capacity_in(4, Fwd)
        }

        // the std allocators' `allocate` never deallocates
        #[verifier::fip]
        fn direct(l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            Global.allocate(l)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_allocator_allocate_not_fip ["vstd", "-V alloc-check"] => fip_allocator("", "#[verifier::fip]", FIP_MARKER) => Err(err) => assert_vir_error_msg(err, "`Fwd::allocate` must be a #[verifier::fip] function of this crate")
}

test_verify_one_file_with_options! {
    #[test] fip_allocator_clone_not_fip ["vstd", "-V alloc-check"] => fip_allocator("#[verifier::fip]", "", FIP_MARKER) => Err(err) => assert_vir_error_msg(err, "the `Clone::clone` of `Fwd` must be a #[verifier::fip] function")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_needs_strict_allocator ["vstd", "-V alloc-check"] => fip_allocator("#[verifier::fip]", "#[verifier::fip]", FIP_MARKER) + verus_code_str! {
        #[verifier::fip(strict)]
        fn push_empty(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }
    } => Err(err) => assert_vir_error_msg(err, "only if it implements `vstd::alloc_check::FipStrictAllocator`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_allocator_methods_not_strict ["vstd", "-V alloc-check"] => fip_allocator("#[verifier::fip]", "#[verifier::fip(strict)]", STRICT_MARKERS) => Err(err) => assert_vir_error_msg(err, "`Fwd::allocate` must be a #[verifier::fip(strict)] function of this crate")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_allocator_accepted ["vstd", "-V alloc-check"] => fip_allocator("#[verifier::fip(strict)]", "#[verifier::fip(strict)]", STRICT_MARKERS) + verus_code_str! {
        #[verifier::fip(strict)]
        fn push_empty(v: &mut Vec<u8, Fwd>)
            requires spec_vec_capacity(&*old(v)) == 0,
            allocates 1
        {
            v.push(1);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // the allocator's `allocate` could call back into a function that grows a vector with it
    #[test] fip_strict_allocator_reentry ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator, NoDeallocDrop, FipAllocator, FipStrictAllocator};
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Fwd;

        // (allowed to recurse, so that the cycle through the allocator is not rejected as a
        // possibly nonterminating one first)
        #[verifier::fip(strict)]
        #[verifier::exec_allows_no_decreases_clause]
        fn again() -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 5
        {
            let v: Vec<u8, Fwd> = Vec::with_capacity_in(1, Fwd);
            core::mem::forget(v);
            Err(AllocError)
        }

        unsafe impl Allocator for Fwd {
            #[verifier::fip(strict)]
            #[verifier::exec_allows_no_decreases_clause]
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 5
            {
                again()
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
            }
        }

        unsafe impl AllocFreeDrop for Fwd {}
        unsafe impl NoDeallocDrop for Fwd {}
        unsafe impl BoundedAllocator for Fwd {
            open spec fn max_cost() -> int { 5 }
        }
        unsafe impl FipAllocator for Fwd {}
        unsafe impl FipStrictAllocator for Fwd {}
    } => Err(err) => {
        // (the verifier already rejects the cycle through the allocator's impl; the compiler-side
        // check, which does not see that edge, rejects it too if it gets that far)
        assert!(err.errors.iter().any(|e| e.message.contains("cyclic self-reference")
            || e.message.contains("can reach `again`, which uses a user allocator itself")), "{:?}", err.errors);
    }
}

/// A type whose (fip, but not strict) `Drop` recurses
const RECURSIVE_DROP: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};

    #[verifier::fip]
    fn deep(n: u64) -> (r: u64)
        decreases n
        opens_invariants none
        no_unwind
    {
        if n == 0 { 0 } else { let r = deep(n - 1); if r < 1000 { r + 1 } else { r } }
    }

    pub struct H { pub n: u64 }

    impl Drop for H {
        #[verifier::fip]
        fn drop(&mut self)
            opens_invariants none
            no_unwind
        {
            let _ = deep(self.n);
        }
    }

    unsafe impl AllocFreeDrop for H {}
    unsafe impl NoDeallocDrop for H {}
};

test_verify_one_file_with_options! {
    // the drop of a value of a type parameter runs a destructor that is not known here
    #[test] fip_strict_generic_drop ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn sink<T: NoDeallocDrop>(x: T) {
        }
    } => Err(err) => assert_vir_error_msg(err, "it drops a value of type `T`, whose destructor is not known here")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_generic_copy_ok ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn sink<T: Copy>(x: T) {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // std code may drop values of its type arguments (`Vec::clear`), running their destructors
    #[test] fip_strict_std_call_runs_destructor ["vstd", "-V alloc-check"] => RECURSIVE_DROP.to_string() + verus_code_str! {
        #[verifier::fip(strict)]
        fn strict_clear(v: &mut Vec<H>) {
            v.clear();
        }
    } => Err(err) => assert_vir_error_msg(err, "which is not `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    // (both the MIR checks and the verifier must agree on the kind)
    #[test] fip_two_attributes ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        #[verifier::fip(strict)]
        fn f(n: u64) -> u64 {
            n
        }
    } => Err(err) => assert_vir_error_msg(err, "more than one `#[verifier::fip]` attribute")
}

/// The reasons `-V fip-lint` gives for not rewriting recursion modulo a constructor
fn trmc_reasons(err: &TestErr) -> Vec<String> {
    err.warnings
        .iter()
        .map(|w| w.message.clone())
        .filter(|m| m.contains("cannot be rewritten into a loop automatically"))
        .collect()
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable_order_and_names ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum T { Leaf, Node(Box<T>, u64) }
        pub enum L { Nil, Cons(u64, Box<L>) }

        fn tick() -> u64 { 7 }

        // a field after the recursive call that is not a literal or a name
        fn after(n: u64) -> (r: T)
            decreases n
        {
            if n == 0 { T::Leaf } else { T::Node(Box::new(after(n - 1)), tick()) }
        }

        // a parameter's name bound again
        fn shadow(k: u64, n: u64) -> (r: L)
            requires k < 1000,
            decreases n
        {
            let k = k + 1;
            if n == 0 { L::Nil } else { L::Cons(k, Box::new(shadow(k % 1000, n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 2, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("this field comes after the recursive call")), "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("binds a parameter's name again")), "{:?}", msgs);
    }
}

test_verify_one_file_with_options! {
    #[test] fip_lint_trmc_not_rewritable_user_drop ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        pub struct D(pub u64);
        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }

        // `d` is dropped after the recursive call returns
        fn with_drop(n: u64) -> (r: L)
            decreases n
        {
            let d = D(n);
            if n == 0 { L::Nil } else { L::Cons(n, Box::new(with_drop(n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 1, "{:?}", msgs);
        assert!(msgs[0].contains("dropping this value"), "{:?}", msgs);
    }
}

test_verify_one_file_with_options! {
    // temporaries whose drop runs user code (portable-fip, fip-beta 3eb69f3c3, N4), and a name the
    // rewrite reserves (N5)
    #[test] fip_lint_trmc_not_rewritable_temporaries_and_reserved_names ["vstd", "-V fip-lint"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        pub enum L2 { Nil, Cons(u64, u64, Box<L2>) }
        pub struct D(pub u64);
        impl Drop for D {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
            {
            }
        }
        fn mkd(n: u64) -> (r: D) ensures r.0 == n { D(n) }

        // a match scrutinee
        fn scrut(n: u64) -> (r: L)
            decreases n
        {
            match mkd(n) { D(v) => if v == 0 { L::Nil } else { L::Cons(v, Box::new(scrut(v - 1))) } }
        }

        // a field taken out of a temporary
        fn temp(n: u64) -> (r: L)
            decreases n
        {
            if n == 0 { L::Nil } else { L::Cons(mkd(n).0, Box::new(temp(n - 1))) }
        }

        // an argument of the recursive call
        fn arg(n: u64) -> (r: L)
            decreases n
        {
            if n == 0 { L::Nil } else { L::Cons(n, Box::new(arg(mkd(n - 1).0))) }
        }

        // a local named like the rewrite's temporaries
        fn named(n: u64) -> (r: L2)
            decreases n
        {
            let __trmc_t0: u64 = 7;
            if n == 0 { L2::Nil } else { L2::Cons(n, __trmc_t0, Box::new(named(n - 1))) }
        }
    } => Ok(err) => {
        let msgs = trmc_reasons(&err);
        assert_eq!(msgs.len(), 4, "{:?}", msgs);
        assert_eq!(msgs.iter().filter(|m| m.contains("dropping this value")).count(), 3, "{:?}", msgs);
        assert!(msgs.iter().any(|m| m.contains("a name starting with `__trmc`")), "{:?}", msgs);
    }
}

// fip(strict) takes `verus_builtin`'s functions as leaves, so a dependency of that name must be
// the one Verus provides: a look-alike (with a deep recursion) brought in under another extern
// name is rejected (portable-fip, fip-beta 3eb69f3c3, N3)
#[test]
fn fip_strict_fake_verus_builtin_rejected() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("vb.rs"),
        format!(
            "{pre}verus!{{ pub fn deep(n: u64) -> u64 decreases n {{ if n == 0 {{ 0 }} else {{ let r = deep(n - 1); if r < u64::MAX {{ r + 1 }} else {{ r }} }} }} }}\n"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("c.rs"),
        format!(
            "{pre}verus!{{ #[verifier::fip(strict)] fn s(n: u64) -> u64 {{ fb::deep(n) }} }}\n"
        ),
    )
    .expect("write");
    // (built without -V alloc-check: with it, the name is refused outright, see below)
    let fake = run_verus_raw(
        &[
            "--crate-type=lib",
            "--crate-name",
            "verus_builtin",
            "-C",
            "metadata=fake",
            "--export",
            "vb.vir",
            "--compile",
            "vb.rs",
            "-o",
            "libfakevb.rlib",
        ],
        dir,
    );
    assert!(fake.status.success(), "fake failed:\n{}", String::from_utf8_lossy(&fake.stderr));
    let c = run_verus_raw(
        &[
            "--crate-type=lib",
            "c.rs",
            "-V",
            "alloc-check",
            "--import",
            "fb=vb.vir",
            "--extern",
            "fb=libfakevb.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&c.stderr);
    assert!(!c.status.success(), "c should be rejected:\n{}", stderr);
    assert!(
        stderr
            .contains("trusts a crate named `verus_builtin` only if it is the one Verus provides"),
        "unexpected:\n{}",
        stderr
    );
    // and a crate of that name cannot itself be verified with -V alloc-check
    let named = run_verus_raw(
        &["--crate-type=lib", "--crate-name", "verus_builtin", "vb.rs", "-V", "alloc-check"],
        dir,
    );
    let stderr = String::from_utf8_lossy(&named.stderr);
    assert!(!named.status.success(), "should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("a crate named `verus_builtin` cannot be verified with -V alloc-check"),
        "unexpected:\n{}",
        stderr
    );
}

test_verify_one_file_with_options! {
    // the real `verus_builtin` stays trusted: `Ghost(..)` in a strict function compiles to a call
    // of `Ghost::assume_new_fallback`
    #[test] fip_strict_ghost_wrappers_accepted ["vstd", "-V alloc-check", "--compile"] => verus_code! {
        use vstd::prelude::*;
        pub enum L { Nil, Cons(u64, Box<L>) }
        spec fn len(l: &L) -> nat decreases l { match l { L::Nil => 0, L::Cons(_, t) => 1 + len(t) } }
        #[verifier::fip(strict)]
        fn bump(l: L, Ghost(g): Ghost<int>) -> (r: L)
            ensures len(&r) == len(&l)
            allocates 0
        {
            match l {
                L::Nil => L::Nil,
                L::Cons(x, tl) => {
                    let gh: Ghost<nat> = Ghost(len(&tl));
                    assert(len(&tl) == gh@);
                    L::Cons(x.wrapping_add(1), tl)
                }
            }
        }
    } => Ok(())
}

// A library may provide a `FipAllocator` (its impls were checked when it was compiled with
// -V alloc-check), and a crate using it need not have fip functions; a marker impl of a crate
// not verified with -V alloc-check is rejected (portable-fip, fip-beta 3eb69f3c3, §2)
#[test]
fn fip_allocator_from_library() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, BoundedAllocator, NoDeallocDrop, FipAllocator}};
use std::alloc::{{Allocator, AllocError, Global, Layout}};
use std::ptr::NonNull;
verus! {{
pub struct Fwd;
unsafe impl Allocator for Fwd {{
    #[verifier::fip]
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) allocates 1 {{ Global.allocate(layout) }}
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) allocates 0 {{
        #[verifier::trusted_call] {{ unsafe {{ Global.deallocate(ptr, layout) }} }}
    }}
}}
unsafe impl AllocFreeDrop for Fwd {{}}
unsafe impl NoDeallocDrop for Fwd {{}}
unsafe impl BoundedAllocator for Fwd {{ open spec fn max_cost() -> int {{ 1 }} }}
unsafe impl FipAllocator for Fwd {{}}
}}
"
        ),
    )
    .expect("write");
    std::fs::write(
        dir.join("m.rs"),
        format!("{pre}verus!{{ fn f(x: u64) -> (r: u64) allocates 0 {{ x }} }}\n"),
    )
    .expect("write");
    let lib = run_verus_raw(
        &["--crate-type=lib", "lib.rs", "-V", "alloc-check", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let m = run_verus_raw(
        &[
            "--crate-type=lib",
            "m.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "lib=lib.vir",
            "--extern",
            "lib=liblib.rlib",
        ],
        dir,
    );
    assert!(m.status.success(), "m:\n{}", String::from_utf8_lossy(&m.stderr));

    // a (false) `NoDeallocDrop` in a crate built without -V alloc-check
    std::fs::write(
        dir.join("lib3.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, NoDeallocDrop}};
verus! {{
pub struct S {{ pub b: Box<u8> }}
unsafe impl AllocFreeDrop for S {{}}
unsafe impl NoDeallocDrop for S {{}}
}}
"
        ),
    )
    .expect("write");
    let lib3 =
        run_verus_raw(&["--crate-type=lib", "lib3.rs", "--compile", "--export", "lib3.vir"], dir);
    assert!(lib3.status.success(), "lib3:\n{}", String::from_utf8_lossy(&lib3.stderr));
    std::fs::write(
        dir.join("m3.rs"),
        format!("{pre}verus!{{ #[verifier::fip] fn eat(s: lib3::S) -> (r: u64) allocates 0 {{ core::mem::forget(s); 0 }} }}\n"),
    )
    .expect("write");
    let m3 = run_verus_raw(
        &[
            "--crate-type=lib",
            "m3.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "lib3=lib3.vir",
            "--extern",
            "lib3=liblib3.rlib",
        ],
        dir,
    );
    let stderr = String::from_utf8_lossy(&m3.stderr);
    assert!(!m3.status.success(), "m3 should be rejected:\n{}", stderr);
    assert!(
        stderr.contains("which was not verified (and compiled) with -V alloc-check"),
        "unexpected:\n{}",
        stderr
    );
}

// A strict function may call a strict function of a crate verified and compiled with
// -V alloc-check, and drop a value of a type whose `Drop` is strict there (as leaves); other
// functions and destructors of other crates stay unknown (portable-fip, fip-beta 6f6975af2, §2)
#[test]
fn fip_strict_across_crates() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, NoDeallocDrop}};
verus! {{
pub struct H {{ pub n: u64 }}
impl Drop for H {{
    #[verifier::fip(strict)]
    fn drop(&mut self) opens_invariants none no_unwind {{}}
}}
unsafe impl AllocFreeDrop for H {{}}
unsafe impl NoDeallocDrop for H {{}}
pub struct G {{ pub n: u64 }}
impl Drop for G {{
    #[verifier::fip]
    fn drop(&mut self) opens_invariants none no_unwind {{}}
}}
unsafe impl AllocFreeDrop for G {{}}
unsafe impl NoDeallocDrop for G {{}}
#[verifier::fip(strict)]
pub fn inc(x: u64) -> (r: u64) allocates 0 {{ x.wrapping_add(1) }}
#[verifier::fip]
pub fn inc_loose(x: u64) -> (r: u64) allocates 0 {{ x.wrapping_add(1) }}
}}
"
        ),
    )
    .expect("write");
    let lib = run_verus_raw(
        &["--crate-type=lib", "lib.rs", "-V", "alloc-check", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let run = |name: &str, body: &str| {
        std::fs::write(dir.join(format!("{name}.rs")), format!("{pre}verus!{{ {body} }}\n"))
            .expect("write");
        let out = run_verus_raw(
            &[
                "--crate-type=lib",
                &format!("{name}.rs"),
                "-V",
                "alloc-check",
                "--compile",
                "--import",
                "lib=lib.vir",
                "--extern",
                "lib=liblib.rlib",
            ],
            dir,
        );
        (out.status.success(), String::from_utf8_lossy(&out.stderr).to_string())
    };
    let (ok, e) = run(
        "ok",
        "#[verifier::fip(strict)] fn s(x: u64, h: lib::H) -> (r: u64) allocates 0 { let y = lib::inc(x); y }",
    );
    assert!(ok, "{}", e);
    let (ok, e) = run(
        "bad1",
        "#[verifier::fip(strict)] fn s(x: u64) -> (r: u64) allocates 0 { lib::inc_loose(x) }",
    );
    assert!(!ok && e.contains("calls `lib::inc_loose` from another crate"), "{}", e);
    let (ok, e) = run("bad2", "#[verifier::fip(strict)] fn s(g: lib::G) { }");
    assert!(!ok && e.contains("<lib::G as std::ops::Drop>::drop` from another crate"), "{}", e);
    // a strict library function generic over the allocator, instantiated with an allocator whose
    // strict `allocate` calls back into it: VIR's recursion check rejects the cycle first (the
    // compiled-program check would too: the call counts as using a user allocator)
    std::fs::write(
        dir.join("glib.rs"),
        format!(
            "{pre}use vstd::alloc_check::FipStrictAllocator;
verus! {{
#[verifier::fip(strict)]
pub fn push_one<A: FipStrictAllocator + Copy>(v: &mut Vec<u8, A>)
    requires vstd::std_specs::vec::spec_vec_capacity(&*old(v)) == 0,
    allocates vstd::std_specs::rust_1_100::allocator_max_cost::<A>()
{{ v.push(1); }}
}}
"
        ),
    )
    .expect("write");
    let glib = run_verus_raw(
        &["--crate-type=lib", "glib.rs", "-V", "alloc-check", "--compile", "--export", "glib.vir"],
        dir,
    );
    assert!(glib.status.success(), "glib:\n{}", String::from_utf8_lossy(&glib.stderr));
    std::fs::write(
        dir.join("cyc.rs"),
        format!(
            "{pre}use vstd::alloc_check::{{AllocFreeDrop, BoundedAllocator, NoDeallocDrop, FipAllocator, FipStrictAllocator}};
use std::alloc::{{Allocator, AllocError, Global, Layout}};
use std::ptr::NonNull;
verus! {{
pub struct Re;
impl Clone for Re {{
    #[verifier::fip(strict)]
    fn clone(&self) -> (r: Self) allocates 0 {{ Re }}
}}
impl Copy for Re {{}}
#[verifier::fip(strict)]
fn g() allocates 1 {{
    let mut v: Vec<u8, Re> = Vec::new_in(Re);
    glib::push_one(&mut v);
    core::mem::forget(v);
}}
unsafe impl Allocator for Re {{
    #[verifier::fip(strict)]
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) allocates 1 {{
        g();
        Global.allocate(layout)
    }}
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) allocates 0 {{
        #[verifier::trusted_call] {{ unsafe {{ Global.deallocate(ptr, layout) }} }}
    }}
}}
unsafe impl AllocFreeDrop for Re {{}}
unsafe impl NoDeallocDrop for Re {{}}
unsafe impl BoundedAllocator for Re {{ open spec fn max_cost() -> int {{ 2 }} }}
unsafe impl FipAllocator for Re {{}}
unsafe impl FipStrictAllocator for Re {{}}
}}
"
        ),
    )
    .expect("write");
    let cyc = run_verus_raw(
        &[
            "--crate-type=lib",
            "cyc.rs",
            "-V",
            "alloc-check",
            "--compile",
            "--import",
            "glib=glib.vir",
            "--extern",
            "glib=libglib.rlib",
        ],
        dir,
    );
    let e = String::from_utf8_lossy(&cyc.stderr);
    assert!(!cyc.status.success(), "{}", e);
    assert!(
        e.contains("cyclic self-reference") || e.contains("uses a user allocator itself"),
        "{}",
        e
    );
}

test_verify_one_file_with_options! {
    // std's slice views (they reborrow the slice or move elements within it: nothing is dropped
    // or freed, and no user code runs) may be called from a fip function (portable-fip,
    // 2026-11-09 split_at_mut request)
    #[test] fip_slice_views ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::fip]
        pub fn swap_lt(xs: &mut [u64], i: usize, j: usize)
            requires i < j, j < old(xs)@.len(),
            ensures final(xs)@ == old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int]),
            no_unwind allocates 0
        {
            let (a, b) = <[u64]>::split_at_mut(xs, j);
            ::core::mem::swap(&mut a[i], &mut b[0]);
            proof { assert(final(xs)@ =~= old(xs)@.update(i as int, old(xs)@[j as int]).update(j as int, old(xs)@[i as int])); }
        }
        #[verifier::fip]
        fn views(xs: &mut [u64], v: &mut Vec<u64>) -> (r: u64)
            requires old(xs)@.len() >= 2, old(v)@.len() >= 1,
            allocates 0
        {
            let n = xs.len();
            let a = xs[0];
            let w = v[0];
            v[0] = a;
            xs.swap(0, 1);
            let _ = xs.split_last();
            let _ = xs.first();
            match xs.split_last_mut() { Some((l, _)) => { *l = w; } None => {} }
            match xs.split_at_mut_checked(1) { Some((p, q)) => { core::mem::swap(&mut p[0], &mut q[0]); } None => {} }
            match xs.get(0) { Some(x) => *x, None => 0 }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // std functions that drop no value of their type arguments (vstd's specifications say so
    // with `alloc_check_skip_drops`) may be called with a `T` whose destructor is not known
    // (portable-fip, 2026-11-09 strict-std-calls request)
    #[test] fip_strict_std_calls_drop_nothing ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        #[verifier::fip(strict)]
        pub fn swap_lt_any<T: AllocFreeDrop>(xs: &mut [T], i: usize, j: usize)
            requires i < j, j < old(xs)@.len(),
            no_unwind allocates 0
        {
            let (a, b) = <[T]>::split_at_mut(xs, j);
            ::core::mem::swap(&mut a[i], &mut b[0]);
        }
        #[verifier::fip(strict)]
        pub fn replace_any<T: AllocFreeDrop>(x: &mut T, y: T) -> (r: T)
            no_unwind allocates 0
        {
            ::core::mem::replace(x, y)
        }
        #[verifier::fip(strict)]
        pub fn views_any<T: AllocFreeDrop>(xs: &mut [T], v: &mut Vec<T>) -> (r: usize)
            requires old(xs)@.len() >= 2, old(v)@.len() >= 1,
            allocates 0
        {
            xs.swap(0, 1);
            let _ = xs.split_last_mut();
            let _ = xs.first();
            let _ = xs.get(0);
            let _ = &v[0];
            let _ = v.as_mut_slice();
            let _ = v.len();
            xs.len()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // (`Vec::clear` drops the elements)
    #[test] fip_strict_std_call_that_drops_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        #[verifier::fip(strict)]
        pub fn clear_any<T: AllocFreeDrop + NoDeallocDrop>(v: &mut Vec<T>)
            allocates 0
        {
            v.clear();
        }
    } => Err(err) => assert_vir_error_msg(err, "which may drop a value of type `T`, whose destructor is not known here")
}


test_verify_one_file_with_options! {
    // `&mut v[i]` calls `<Vec<T> as IndexMut<usize>>::index_mut`, which drops nothing; writing
    // over the element (`v[0] = x`) still drops the old one in this function, which is rejected
    // (portable-fip, 2026-11-10 vec-index-mut request)
    #[test] fip_strict_vec_index_mut ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::AllocFreeDrop;
        #[verifier::fip(strict)]
        pub fn via_index_mut<T: AllocFreeDrop>(v: &mut Vec<T>, w: &mut T)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            ::core::mem::swap(&mut v[0], w);
        }
        #[verifier::fip(strict)]
        pub fn range_index_mut<T: AllocFreeDrop>(v: &mut Vec<T>) -> (r: usize)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            let s = &mut v[0..1];
            s.len()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_vec_index_assign_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::{AllocFreeDrop, NoDeallocDrop};
        #[verifier::fip(strict)]
        pub fn overwrite<T: AllocFreeDrop + NoDeallocDrop>(v: &mut Vec<T>, x: T)
            requires old(v)@.len() >= 1,
            allocates 0
        {
            v[0] = x;
        }
    } => Err(err) => assert_vir_error_msg(err, "it drops a value of type `T`, whose destructor is not known here")
}

test_verify_one_file_with_options! {
    // the examples of the guide's "FIP and FBIP" page (docs/guide/src/fip-fbip.md)
    #[test] fip_guide_examples ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        pub enum List { Nil, Cons(u64, Box<List>) }
        pub open spec fn len(l: List) -> nat
            decreases l
        {
            match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
        }
        fn push_one(v: &mut Vec<u64>)
            allocates 1
        {
            v.push(1);
        }
        #[verifier::fip]
        fn halve(mut b: Box<List>) -> (r: Box<List>) {
            match &mut *b {
                List::Cons(x, _) => { *x = *x / 2; }
                List::Nil => {}
            }
            b
        }
        #[verifier::fip]
        fn reverse(l: List, acc: List) -> (r: List)
            ensures len(r) == len(l) + len(acc),
            decreases l
        {
            match l {
                List::Nil => acc,
                List::Cons(x, mut b) => {
                    let next = core::mem::replace(&mut *b, acc);
                    reverse(next, List::Cons(x, b))
                }
            }
        }
        #[verifier::fip]
        fn cons(x: u64, l: List) -> (r: List)
            allocates 1
        {
            List::Cons(x, Box::new(l))
        }
        #[verifier::fip(strict)]
        fn reverse_strict(l: List, acc: List) -> (r: List)
            ensures len(r) == len(l) + len(acc),
            decreases l
        {
            match l {
                List::Nil => acc,
                List::Cons(x, mut b) => {
                    let next = core::mem::replace(&mut *b, acc);
                    become reverse_strict(next, List::Cons(x, b))
                }
            }
        }
        #[verifier::fip]
        fn first<T: vstd::alloc_check::NoDeallocDrop>(a: T, b: T) -> (r: T) {
            a
        }
        #[verifier::fip(strict)]
        fn swap_ends<T: vstd::alloc_check::AllocFreeDrop>(xs: &mut [T])
            requires old(xs)@.len() >= 2,
            allocates 0
        {
            let n = xs.len();
            xs.swap(0, n - 1);
        }
        #[verifier::fip]
        fn fill(hole: &mut List, v: List)
            requires *old(hole) is Nil,
        {
            core::mem::forget(core::mem::replace(hole, v));
        }

        // fip-fbip.md, operator markers
        #[verifier::fip]
        fn larger<'a, T: vstd::alloc_check::FipOrd>(a: &'a T, b: &'a T) -> &'a T {
            if a < b { b } else { a }
        }

        // reference-allocates.md, operator traits
        #[verifier::fip]
        fn lt_gen<T: vstd::alloc_check::FipOrd>(a: &T, b: &T) -> bool {
            a < b
        }

        #[verifier::fip(strict)]
        fn eq_gen<T: vstd::alloc_check::FipStrictPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }
    } => Ok(())
}

// Marker traits for core's operator traits (`vstd::alloc_check::{FbipOp, FipOp, FipStrictOp}`): a
// generic call of an operator trait's method is charged 0 through `FbipOp`, may be made in a fip
// function through `FipOp`, and in a strict one through `FipStrictOp`
test_verify_one_file_with_options! {
    #[test] fip_op_markers_generic_calls ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;
        use vstd::std_specs::ops::AddSpec;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for L {
            open spec fn obeys_eq_spec() -> bool { false }
            open spec fn eq_spec(&self, other: &L) -> bool { self.x == other.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}

        #[verifier::fip]
        fn add_gen<T: FipAdd<Output = T> + NoDeallocDrop>(a: T, b: T) -> T
            requires a.add_req(b),
        {
            a + b
        }

        fn add_counted<T: FbipAdd<Output = T> + AllocFreeDrop>(a: T, b: T) -> T
            requires a.add_req(b),
            allocates 0
        {
            a + b
        }

        #[verifier::fip]
        fn eq_gen<T: FipPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }

        #[verifier::fip]
        fn lt_gen<T: FipOrd>(a: &T, b: &T) -> bool {
            a < b
        }

        #[verifier::fip]
        fn cmp_gen<T: FipOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip]
        fn uses() -> bool {
            let a = add_gen(1u64, 2u64);
            let l = L { x: a };
            let m = L { x: 3 };
            let _o = cmp_gen(&1u8, &2u8);
            eq_gen(&l, &m) && lt_gen(&1u8, &2u8)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_op_markers_missing_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn eq_gen<T: PartialEq>(a: &T, b: &T) -> bool {
            a == b
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_not_fip_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "this `vstd::alloc_check::FipPartialEq` impl is not accepted")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_allocates_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            fn eq(&self, o: &L) -> bool allocates 1 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be checked by Verus and bounded by `allocates 0`")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_derived_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[derive(PartialEq)]
        pub struct L { pub x: u64 }
        unsafe impl FbipPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "-V alloc-check: ")
}

test_verify_one_file_with_options! {
    #[test] fip_op_marker_impl_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
        unsafe impl FipStrictPartialEq for L {}
    } => Err(err) => assert_vir_error_msg(err, "must be `#[verifier::fip(strict)]`")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn cmp_gen<T: FipStrictOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip(strict)]
        fn eq_gen<T: FipStrictPartialEq>(a: &T, b: &T) -> bool {
            a == b
        }

        #[verifier::fip(strict)]
        fn uses() -> bool {
            let _o = cmp_gen(&1u64, &2u64);
            eq_gen(&1u8, &1u8)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn cmp_gen<T: FipOrd>(a: &T, b: &T) -> core::cmp::Ordering {
            a.cmp(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "whose callee is not known here")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_max_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn max_gen<T: FipStrictOrd + Copy>(a: T, b: T) -> T {
            a.max(b)
        }
    } => Err(err) => assert_vir_error_msg(err, "whose callee is not known here")
}

// `L::eq` calls `same::<L>`, which calls `L::eq` again: within one crate, the verifier already
// rejects the cycle (the compiled-program check would too: a strict generic function's call
// through a marker may reach any strict method of this crate's impls of the operator trait)
test_verify_one_file_with_options! {
    #[test] fip_strict_op_marker_cycle_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip(strict)]
            #[verifier::exec_allows_no_decreases_clause]
            fn eq(&self, o: &L) -> bool allocates 0 { same(self, o) }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}
        unsafe impl FipStrictPartialEq for L {}

        #[verifier::fip(strict)]
        #[verifier::exec_allows_no_decreases_clause]
        fn same<T: FipStrictPartialEq>(a: &T, b: &T) -> bool allocates 0 {
            let r = a == b;
            r
        }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition")
}

// A strict function of another crate, generic through a marker, instantiated with a type of this
// crate: its calls of the type's methods are calls back into this crate
#[test]
fn fip_strict_op_marker_across_crates() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let pre = format!("{}\nuse vstd::prelude::*;\nuse vstd::alloc_check::*;\n", FEATURE_PRELUDE);
    std::fs::write(
        dir.join("lib.rs"),
        format!(
            "{pre}verus! {{
#[verifier::fip(strict)]
pub fn same<T: FipStrictPartialEq>(a: &T, b: &T) -> (r: bool) allocates 0 {{ let r = a == b; r }}
}}
"
        ),
    )
    .expect("write");
    let lib = run_verus_raw(
        &["--crate-type=lib", "lib.rs", "-V", "alloc-check", "--compile", "--export", "lib.vir"],
        dir,
    );
    assert!(lib.status.success(), "lib:\n{}", String::from_utf8_lossy(&lib.stderr));
    let run = |name: &str, body: &str| {
        std::fs::write(dir.join(format!("{name}.rs")), format!("{pre}verus!{{ {body} }}\n"))
            .expect("write");
        let out = run_verus_raw(
            &[
                "--crate-type=lib",
                &format!("{name}.rs"),
                "-V",
                "alloc-check",
                "--compile",
                "--import",
                "lib=lib.vir",
                "--extern",
                "lib=liblib.rlib",
            ],
            dir,
        );
        (out.status.success(), String::from_utf8_lossy(&out.stderr).to_string())
    };
    let l = |eq_body: &str| {
        format!(
            "pub struct L {{ pub x: u64 }}
impl PartialEq for L {{
    #[verifier::fip(strict)]
    #[verifier::exec_allows_no_decreases_clause]
    fn eq(&self, o: &L) -> bool allocates 0 {{ {eq_body} }}
}}
impl vstd::std_specs::cmp::PartialEqSpecImpl for L {{
    open spec fn obeys_eq_spec() -> bool {{ false }}
    open spec fn eq_spec(&self, other: &L) -> bool {{ self.x == other.x }}
}}
unsafe impl FbipPartialEq for L {{}}
unsafe impl FipPartialEq for L {{}}
unsafe impl FipStrictPartialEq for L {{}}
"
        )
    };
    let (ok, e) = run(
        "ok",
        &format!(
            "{}
#[verifier::fip(strict)] fn s(a: &L, b: &L) -> (r: bool) allocates 0 {{ lib::same(a, b) }}",
            l("self.x == o.x")
        ),
    );
    assert!(ok, "{}", e);
    // (the verifier rejects the cycle through the trait bound first; the compiled-program check,
    // which follows `lib::same::<L>`'s bounds back to `L::eq`, would too)
    let (ok, e) = run("cyc", &l("let r = lib::same(self, o); r"));
    assert!(
        !ok && (e.contains("is not a tail call and can lead back to")
            || e.contains("found a cyclic self-reference in a definition")),
        "{}",
        e
    );
}

// std's functions that compare their arguments (`contains`, `Option::eq`, `sort_unstable`, ...)
// deallocate only if a comparison does: their `deallocates_when` conditions name the comparison
// markers (`partial_eq_is_fip`, `ord_is_fip`, ...)
test_verify_one_file_with_options! {
    #[test] fip_std_comparisons_through_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        pub struct L { pub x: u64 }
        impl PartialEq for L {
            #[verifier::fip]
            fn eq(&self, o: &L) -> bool allocates 0 { self.x == o.x }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for L {
            open spec fn obeys_eq_spec() -> bool { false }
            open spec fn eq_spec(&self, other: &L) -> bool { self.x == other.x }
        }
        unsafe impl FbipPartialEq for L {}
        unsafe impl FipPartialEq for L {}

        #[verifier::fip]
        fn has<T: FipPartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }

        #[verifier::fip]
        fn ends<T: FipPartialEq>(s: &[T], p: &[T]) -> bool {
            s.starts_with(p) && s.ends_with(p)
        }

        #[verifier::fip]
        fn opt_eq<T: FipPartialEq>(a: &Option<T>, b: &Option<T>) -> bool {
            a == b
        }

        #[verifier::fip]
        fn opt_cmp<T: FipOrd>(a: &Option<T>, b: &Option<T>) -> core::cmp::Ordering {
            a.cmp(b)
        }

        #[verifier::fip]
        fn sort_it<T: FipOrd>(v: &mut [T]) {
            v.sort_unstable();
        }

        #[verifier::fip]
        fn find<T: FipOrd>(v: &[T], x: &T) -> bool {
            match v.binary_search(x) {
                Ok(_) => true,
                Err(_) => false,
            }
        }

        #[verifier::fip]
        fn in_range(r: &core::ops::Range<u64>, x: &u64) -> bool {
            r.contains(x)
        }

        #[verifier::fip]
        fn bigger<T: FipOrd>(a: T, b: T) -> T {
            core::cmp::max(a, b)
        }

        #[verifier::fip]
        fn uses(v: &mut [u64], l: &[L], k: &L) -> bool {
            sort_it(v);
            has(l, k) && opt_eq(&Some(1u8), &None)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_std_comparison_without_marker_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::fip]
        fn has<T: PartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }
    } => Err(err) => assert_any_vir_error_msg(err, "this call may deallocate memory")
}

test_verify_one_file_with_options! {
    #[test] fip_strict_std_comparisons_through_markers ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn sort_it<T: FipStrictOrd>(v: &mut [T]) {
            v.sort_unstable();
        }

        #[verifier::fip(strict)]
        fn has<T: FipStrictPartialEq>(s: &[T], x: &T) -> bool {
            s.contains(x)
        }

        #[verifier::fip(strict)]
        fn uses(v: &mut [u64]) -> bool {
            sort_it(v);
            has(v, &1)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fip_strict_std_comparison_not_strict_rejected ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::alloc_check::*;

        #[verifier::fip(strict)]
        fn sort_it<T: FipOrd>(v: &mut [T]) {
            v.sort_unstable();
        }
    } => Err(err) => assert_any_vir_error_msg(err, "which may call the methods of `T: std::cmp::Ord`, which are not known here")
}
