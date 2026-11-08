#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// `#[verifier::trusted_only]` functions may be called only inside `#[verifier::trusted_call]`
// blocks. vstd marks `Allocator::{deallocate, grow, grow_zeroed, shrink}` (std needs a live block
// of the same allocator, which a precondition cannot say) and
// `UnsafeCell::{as_ref_unchecked, as_mut_unchecked, replace}` (no other live reference).

const ERR: &str = "may be called only inside a `#[verifier::trusted_call]` block";

test_verify_one_file_with_options! {
    // a points-to permission outliving the block it points to (portable-fip, fip-beta 3eb69f3c3, N1)
    #[test] global_deallocate_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::raw_ptr::*;
        use std::alloc::{Allocator, Global, Layout};
        use std::ptr::NonNull;

        fn uaf(l: Layout) -> (r: u64)
            ensures r == 5
        {
            broadcast use vstd::layout::group_layout_axioms;
            vstd::layout::layout_for_type_is_valid::<u64>();
            let (p, Tracked(raw), Tracked(dealloc)) = allocate(
                core::mem::size_of::<u64>(), core::mem::align_of::<u64>());
            let tracked mut pt: PointsTo<u64> = raw.into_typed::<u64>(p as usize);
            let q = p as *mut u64;
            ptr_mut_write(q, Tracked(&mut pt), 5u64);
            match NonNull::new(p) {
                Some(nn) => unsafe { Global.deallocate(nn, l) },
                None => {}
            }
            let b: Box<u64> = Box::new(7u64);
            *ptr_ref(q, Tracked(&pt))
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] global_grow_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, Global, Layout};
        use std::ptr::NonNull;
        fn f(p: NonNull<u8>, a: Layout, b: Layout) {
            let _ = unsafe { Global.grow(p, a, b) };
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] system_shrink_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, System, Layout};
        use std::ptr::NonNull;
        fn f(p: NonNull<u8>, a: Layout, b: Layout) {
            let _ = unsafe { System.shrink(p, a, b) };
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] generic_deallocate_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, Layout};
        use std::ptr::NonNull;
        fn f<A: Allocator>(a: &A, p: NonNull<u8>, l: Layout) {
            unsafe { a.deallocate(p, l) }
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

/// An allocator that forwards to the global one, with its call to `Global.deallocate` trusted
const FWD: &str = verus_code_str! {
    use vstd::prelude::*;
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    pub struct Fwd;

    unsafe impl Allocator for Fwd {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
            Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            #[verifier::trusted_call] {
                unsafe { Global.deallocate(ptr, layout) }
            }
        }
    }
};

test_verify_one_file_with_options! {
    #[test] forwarding_allocator_in_trusted_call ["vstd"] => FWD.to_string() + verus_code_str! {
        fn f(v: Vec<u8, Fwd>) {}
    } => Ok(())
}

test_verify_one_file_with_options! {
    // implementations of a `trusted_only` trait method are `trusted_only` too
    #[test] user_allocator_deallocate_not_callable ["vstd"] => FWD.to_string() + verus_code_str! {
        fn f(a: &Fwd, p: NonNull<u8>, l: Layout) {
            unsafe { a.deallocate(p, l) }
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    // the body of a `trusted_only` method still needs the block for its own calls
    #[test] forwarding_without_trusted_call ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;
        pub struct Fwd;
        unsafe impl Allocator for Fwd {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Global.allocate(layout)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                unsafe { Global.deallocate(ptr, layout) }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    // two `&mut` to the same contents (portable-fip, fip-beta 3eb69f3c3, N2)
    #[test] unsafe_cell_as_mut_unchecked_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use core::cell::UnsafeCell;
        fn alias(c: &UnsafeCell<u64>) -> (r: u64)
            ensures r == 1
        {
            let a: &mut u64 = unsafe { c.as_mut_unchecked() };
            let b: &mut u64 = unsafe { c.as_mut_unchecked() };
            *a = 1;
            *b = 2;
            *a
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] unsafe_cell_as_ref_unchecked_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use core::cell::UnsafeCell;
        fn f(c: &UnsafeCell<u64>) -> u64 {
            *unsafe { c.as_ref_unchecked() }
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] unsafe_cell_replace_not_callable ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use core::cell::UnsafeCell;
        fn f(c: &UnsafeCell<u64>) -> u64 {
            unsafe { c.replace(1) }
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    // the block trusts only its calls: the rest is verified
    #[test] trusted_call_rest_verified ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use core::cell::UnsafeCell;
        fn f(c: &UnsafeCell<u64>) -> u64 {
            #[verifier::trusted_call] {
                let x = unsafe { c.replace(1) };
                assert(x == 1); // FAILS
                x
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // a value could be called anywhere, so not even a `trusted_call` block may take one
    #[test] trusted_only_not_a_value ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, Global, Layout};
        use std::ptr::NonNull;
        fn f(p: NonNull<u8>, l: Layout) {
            #[verifier::trusted_call] {
                let d = <Global as Allocator>::deallocate;
                unsafe { d(&Global, p, l) }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be used as a value")
}

test_verify_one_file_with_options! {
    #[test] user_trusted_only ["vstd"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::trusted_only]
        fn raw(x: u8) -> u8 { x }
        fn ok() -> u8 {
            #[verifier::trusted_call] { raw(1) }
        }
        fn not_ok() -> u8 {
            raw(2)
        }
    } => Err(err) => assert_vir_error_msg(err, ERR)
}

test_verify_one_file_with_options! {
    #[test] user_trusted_only_value ["vstd"] => verus_code! {
        use vstd::prelude::*;
        #[verifier::trusted_only]
        fn raw(x: u8) -> u8 { x }
        fn f() -> Option<u8> {
            Some(1u8).map(raw)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be used as a value")
}

test_verify_one_file_with_options! {
    #[test] trusted_call_no_cheating ["vstd", "--no-cheating"] => verus_code! {
        use vstd::prelude::*;
        use core::cell::UnsafeCell;
        fn f(c: &UnsafeCell<u64>) -> u64 {
            #[verifier::trusted_call] { unsafe { c.replace(1) } }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot be used with --no-cheating")
}

test_verify_one_file_with_options! {
    #[test] trusted_call_in_ghost ["vstd"] => verus_code! {
        use vstd::prelude::*;
        fn f() {
            proof {
                #[verifier::trusted_call] { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "only for executable code")
}
