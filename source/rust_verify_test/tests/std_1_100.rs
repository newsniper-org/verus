#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// vstd specifications of the std items stabilized in Rust 1.100 (vstd/std_specs/rust_1_100.rs)

test_verify_one_file_with_options! {
    #[test] bool_toggle ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(b: &mut bool)
            ensures *final(b) == !*old(b),
            allocates 0
        {
            b.toggle();
        }
        fn g() {
            let mut b = true;
            b.toggle();
            b.toggle();
            assert(b);
            b.toggle();
            assert(b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] vec_from_fn ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn sq(i: usize) -> (r: u64)
            allocates 0
        {
            (i as u64) & 7
        }
        fn f(n: usize) -> (v: Vec<u64>)
            ensures v@.len() == n,
            allocates 1
        {
            Vec::from_fn(n, sq)
        }
        fn g(n: usize) -> (v: Vec<u64>)
            allocates 0 // FAILS
        {
            Vec::from_fn(n, sq)
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] box_rc_arc_map ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        use std::sync::Arc;
        fn double(x: u64) -> (r: u64)
            requires x < 1000,
            ensures r == 2 * x,
            allocates 0
        {
            2 * x
        }
        fn f(b: Box<u64>) -> (r: Box<u64>)
            requires *b < 1000,
            ensures *r == 2 * *b,
            allocates 1
        {
            Box::map(b, double)
        }
        fn len_of(x: &Vec<u8>) -> (r: usize)
            ensures r == x@.len(),
            allocates 0
        {
            x.len()
        }
        fn g(r: Rc<Vec<u8>>, a: Arc<Vec<u8>>) -> (out: (Rc<usize>, Arc<usize>))
            ensures *out.0 == r@.len(), *out.1 == a@.len(),
            allocates 2
        {
            (Rc::map(r, len_of), Arc::map(a, len_of))
        }
        // the same layout: the allocation is reused
        fn same_layout(b: Box<u64>) -> (r: Box<u64>)
            requires *b < 1000,
            allocates 0
        {
            Box::map(b, double)
        }
        fn widen(x: u64) -> (r: u128)
            allocates 0
        {
            x as u128
        }
        fn h(b: Box<u64>) -> (r: Box<u128>)
            allocates 0 // FAILS
        {
            Box::map(b, widen)
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] box_take ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        fn f(b: Box<u64>) -> (r: u64)
            ensures r == *b,
            allocates 0
        {
            let (v, _rest) = Box::take(b);
            v
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] drop_guard ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use core::mem::DropGuard;
        fn f(x: u64) -> (r: u64)
            ensures r == x,
        {
            let g = DropGuard::new(x, |v: u64| {});
            let r: &u64 = &*g;
            assert(*r == x);
            DropGuard::dismiss(g)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // dropping a `DropGuard` runs its closure, which -V alloc-check does not trust
    #[test] drop_guard_drop_not_trusted ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use core::mem::DropGuard;
        fn f<F: FnOnce(u64) + vstd::alloc_check::AllocFreeDrop>(g: DropGuard<u64, F>) allocates 0 { }
    } => Err(err) => assert_vir_error_msg(err, "cannot bound the allocations of dropping a value of type")
}

test_verify_one_file_with_options! {
    #[test] global_and_system_allocator ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, Global, Layout, System};
        fn f(l: Layout) -> (ok: bool)
            allocates 2
        {
            let a = Global.allocate(l);
            let b = System.allocate_zeroed(l);
            a.is_ok() && b.is_ok()
        }
        fn g(l: Layout) -> (ok: bool)
            allocates 1 // FAILS
        {
            let a = Global.allocate(l);
            let b = System.allocate(l);
            a.is_ok() && b.is_ok()
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // std requires more than a zero size (the type must be inhabited, the value valid), which a
    // precondition cannot state: a zero-sized type whose invariant is `false` would prove anything
    #[test] conjure_zst_not_specified ["vstd"] => verus_code! {
        use vstd::prelude::*;
        pub struct Never { ghost g: int }
        impl Never {
            #[verifier::type_invariant]
            spec fn inv(&self) -> bool { false }
        }
        fn wrong() -> (r: u8)
            ensures r == 7
        {
            if core::mem::size_of::<Never>() == 0 {
                let n: Never = unsafe { core::mem::conjure_zst::<Never>() };
                proof { use_type_invariant(&n); }
                8
            } else {
                7
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "conjure_zst")
}

test_verify_one_file_with_options! {
    #[test] once_default_unsafe_cell ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::sync::Once;
        use core::cell::UnsafeCell;
        fn f() -> (r: Once)
            allocates 0
        {
            Once::default()
        }
        fn h(c: &UnsafeCell<u64>) -> (r: u64)
            allocates 0
        {
            #[verifier::trusted_call] { unsafe { c.replace(3) } }
        }
    } => Ok(())
}
