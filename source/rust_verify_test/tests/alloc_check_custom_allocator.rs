#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check with custom allocators (`core::alloc::Allocator`, stable since Rust 1.100):
// `vstd::alloc_check::BoundedAllocator` gives the cost of one allocation (counted at the leaves),
// and the allocator's `Allocator` impl is verified against it

/// An allocator that forwards to the global one (it defines only `allocate` and `deallocate`, so
/// `grow` and the others run std's default bodies), and an arena that hands out no new memory
const ALLOCATORS: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator};
    use vstd::std_specs::rust_1_100::allocator_allocate_cost;
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    pub struct Fwd;

    unsafe impl Allocator for Fwd {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
            allocates 0
        {
            unsafe { Global.deallocate(ptr, layout) }
        }
    }

    unsafe impl AllocFreeDrop for Fwd {}

    unsafe impl BoundedAllocator for Fwd {
        open spec fn allocate_cost() -> int { 1 }
    }

    pub struct Arena;

    unsafe impl Allocator for Arena {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 0
        {
            Err(AllocError)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
            allocates 0
        {
        }
    }

    unsafe impl AllocFreeDrop for Arena {}

    unsafe impl BoundedAllocator for Arena {
        open spec fn allocate_cost() -> int { 0 }
    }
};

test_verify_one_file_with_options! {
    #[test] forwarding_allocator ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        // `push` that grows calls `grow` (std's default body: one `allocate`)
        fn push_one(v: &mut Vec<u8, Fwd>)
            allocates 1
        {
            v.push(3);
        }

        fn build() -> (n: usize)
            allocates 2
        {
            let mut v: Vec<u8, Fwd> = Vec::new_in(Fwd);
            v.push(1);
            let b = Box::new_in(5u64, Fwd);
            v.len()
        }

        fn drop_it(v: Vec<u8, Fwd>, b: Box<u64, &Fwd>)
            allocates 0
        {
        }

        fn push_generic<A: Allocator + BoundedAllocator>(v: &mut Vec<u8, A>)
            allocates allocator_allocate_cost::<A>()
        {
            v.push(1);
        }

        fn push_via_generic()
            allocates 1
        {
            let mut v: Vec<u8, Fwd> = Vec::new_in(Fwd);
            push_generic(&mut v);
        }

        fn push_too_many(v: &mut Vec<u8, Fwd>)
            allocates 0 // FAILS
        {
            v.push(3);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] arena_allocator_allocates_nothing ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        fn use_arena(a: &Arena)
            allocates 0
        {
            let mut v: Vec<u8, &Arena> = Vec::new_in(a);
            v.push(1);
            v.push(2);
            let w = v.clone();
            let b = Box::new_in(5u64, a);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] std_allocators_through_references ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Global, System};
        fn f(v: &mut Vec<u8, &Global>, w: Vec<u8, &System>)
            allocates 1
        {
            v.push(1);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] allocator_without_marker_cannot_be_dropped ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        pub struct NoMark;
        unsafe impl Allocator for NoMark {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) { }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for NoMark {}
        fn drop_it(v: Vec<u8, NoMark>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "must implement `vstd::alloc_check::BoundedAllocator`")
}

test_verify_one_file_with_options! {
    #[test] generic_allocator_needs_marker ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::Allocator;
        fn drop_it<A: Allocator + vstd::alloc_check::AllocFreeDrop>(v: Vec<u8, A>)
            allocates 0
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "must implement `vstd::alloc_check::BoundedAllocator`")
}

test_verify_one_file_with_options! {
    #[test] marker_impl_outside_verus_rejected ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        unsafe impl vstd::alloc_check::BoundedAllocator for Evil {}
        verus! {
        pub struct Evil;
        unsafe impl vstd::alloc_check::AllocFreeDrop for Evil {}
        unsafe impl Allocator for Evil {
            fn allocate(&self, l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) { Err(AllocError) }
            unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) { }
        }
        fn drop_it(v: Vec<u8, Evil>) allocates 0 { }
        }
    } => Err(err) => assert_vir_error_msg(err, "this `BoundedAllocator` impl is not checked by Verus")
}

test_verify_one_file_with_options! {
    #[test] marker_needs_checked_allocator_impl ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        pub struct Evil;
        #[verifier::external]
        unsafe impl Allocator for Evil {
            fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> { Global.allocate(l) }
            unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) { let _b = Box::new(1u8); }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for Evil {}
        unsafe impl vstd::alloc_check::BoundedAllocator for Evil {
            open spec fn allocate_cost() -> int { 0 }
        }
        fn drop_it(v: Vec<u8, Evil>) allocates 0 { }
    } => Err(err) => assert_vir_error_msg(err, "needs its `core::alloc::Allocator` impl to be checked by Verus")
}

test_verify_one_file_with_options! {
    // the impl's bound must be within the cost that the marker gives
    #[test] allocator_impl_within_marker_cost ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        pub struct Two;
        unsafe impl Allocator for Two {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                let a = Global.allocate(layout);
                Global.allocate(layout) // fails: 2 > 1
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) { }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for Two {}
        unsafe impl vstd::alloc_check::BoundedAllocator for Two {
            open spec fn allocate_cost() -> int { 1 }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file_with_options! {
    #[test] allocator_deallocate_allocates_nothing ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        pub struct Leaky;
        unsafe impl Allocator for Leaky {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                let b = Box::new(1u8); // fails: the declaration says 0
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file_with_options! {
    // a negative cost is clamped at 0 (it does not contradict the costs being nonnegative)
    #[test] negative_marker_cost_is_clamped ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::rust_1_100::allocator_allocate_cost;
        use std::alloc::{Allocator, AllocError, Layout};
        use std::ptr::NonNull;
        pub struct Neg;
        unsafe impl Allocator for Neg {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) { }
        }
        unsafe impl vstd::alloc_check::AllocFreeDrop for Neg {}
        unsafe impl vstd::alloc_check::BoundedAllocator for Neg {
            open spec fn allocate_cost() -> int { -1 }
        }
        proof fn p() {
            assert(allocator_allocate_cost::<Neg>() == 0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // cloning a container clones its allocator, which costs an uninterpreted amount for an
    // allocator other than the global one or a reference
    #[test] container_clone_charges_allocator_clone ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        impl Clone for Fwd {
            fn clone(&self) -> (r: Self)
                allocates 0
            {
                Fwd
            }
        }
        fn clone_it(v: &Vec<u8, Fwd>) -> (r: Vec<u8, Fwd>)
            allocates 1 // FAILS
        {
            v.clone()
        }
    } => Err(err) => assert_one_fails(err)
}
