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
