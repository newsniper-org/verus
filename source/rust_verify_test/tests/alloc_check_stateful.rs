#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check with an allocator whose costs depend on its state (vstd::alloc_heap): a pool
// that hands out `remaining` blocks without asking the global allocator, then asks it

const POOL: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::atomic_ghost::*;
    use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator};
    use vstd::alloc_heap::*;
    use vstd::resource::Loc;
    use vstd::resource::preorder_auth::Preorder;
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    pub struct Free(pub nat);
    impl Preorder for Free {
        open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
        proof fn le_refl(a: Self) {}
        proof fn le_trans(a: Self, b: Self, c: Self) {}
    }

    pub struct PoolPred;
    impl AtomicInvariantPredicate<Loc, u64, AllocAuth<Free>> for PoolPred {
        open spec fn atomic_inv(k: Loc, v: u64, g: AllocAuth<Free>) -> bool {
            g@ == Free(v as nat) && g.id() == k
        }
    }

    /// A pool that hands out `remaining` blocks without asking the global allocator (it returns
    /// `Err` for them here, to keep the example small), and then asks the global allocator
    pub struct Pool {
        remaining: AtomicU64<Loc, AllocAuth<Free>, PoolPred>,
        reg: Tracked<Registered<Free>>,
    }

    impl Pool {
        #[verifier::type_invariant]
        spec fn inv(&self) -> bool {
            self.remaining.well_formed() && self.remaining.constant() == self.reg@.loc()
        }

        pub closed spec fn id(&self) -> Loc { self.reg@.loc() }

        fn new(n: u64) -> (p: Self)
            ensures
                allocator_heap() == heap_register::<Free>(old_allocator_heap(), p.id(), Free(n as nat)),
            allocates 0
        {
            let tracked (auth, reg) = AllocAuth::register(Free(n as nat));
            let ghost l = reg.loc();
            let remaining = AtomicU64::new(Ghost(l), n, Tracked(auth));
            Pool { remaining, reg: Tracked(reg) }
        }
    }

    unsafe impl Allocator for Pool {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            proof { use_type_invariant(self); }
            let tracked reg = self.reg.borrow();
            let ghost s = heap_state::<Free>(allocator_heap(), reg.loc());
            let v = atomic_with_ghost!(&self.remaining => load(); ghost g => {
                g.lower_bound(reg);
            });
            if v > 0 {
                atomic_with_ghost!(&self.remaining => store(v - 1); ghost g => {
                    g.step(reg, Free((v - 1) as nat), if s.0 > 0 { Free((s.0 - 1) as nat) } else { s });
                });
                Err(AllocError)
            } else {
                Global.allocate(layout)
            }
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
            allocates 0
        {
        }
    }

    unsafe impl AllocFreeDrop for Pool {}

    unsafe impl BoundedAllocator for Pool {
        open spec fn max_cost() -> int { 1 }
    }

    unsafe impl StatefulAllocator for Pool {
        type State = Free;

        open spec fn loc(&self) -> Loc { self.id() }

        proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) {
            self.reg.borrow()
        }

        open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
            if s.0 > 0 { 0 } else { 1 }
        }

        open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
            if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
        }
    }
};

test_verify_one_file_with_options! {
    #[test] stateful_pool ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn two(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 2,
            ensures allocator_state(p).0 == old_allocator_state(p).0 - 2,
            allocates 0
        {
            let _ = p.allocate(l);
            let _ = p.allocate(l);
        }

        fn three(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 2,
            allocates 1
        {
            let _ = p.allocate(l);
            let _ = p.allocate(l);
            let _ = p.allocate(l);
        }

        fn top(l: Layout)
            allocates 0
        {
            let p = Pool::new(2);
            two(&p, l);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] stateful_pool_over_bound ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn three(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 2,
            allocates 0 // FAILS
        {
            let _ = p.allocate(l);
            let _ = p.allocate(l);
            let _ = p.allocate(l);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] stateful_pool_unknown_after_call ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn helper(p: &Pool, l: Layout)
            allocates 1
        {
            let _ = p.allocate(l);
        }

        fn lost(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 2,
            allocates 0 // FAILS
        {
            helper(p, l); // (charged 1 anyway; and the pool's state is unknown after it)
        }

        fn lost2(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 2,
        {
            helper(p, l);
            assert(allocator_state(p).0 >= 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] stateful_proof_fn_must_say ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        proof fn sneaky() {
            let tracked (a, r) = AllocAuth::register(Free(3)); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "this proof function changes the allocator heap")
}

test_verify_one_file_with_options! {
    #[test] stateful_step_down_rejected ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn bad() {
            let tracked (mut a, r) = AllocAuth::register(Free(3));
            proof { a.step(&r, Free(2), Free(3)); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] stateful_impl_over_cost ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::*;
        use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator};
        use vstd::alloc_heap::*;
        use vstd::resource::Loc;
        use vstd::resource::preorder_auth::Preorder;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Free(pub nat);
        impl Preorder for Free {
            open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
            proof fn le_refl(a: Self) {}
            proof fn le_trans(a: Self, b: Self, c: Self) {}
        }

        pub struct PoolPred;
        impl AtomicInvariantPredicate<Loc, u64, AllocAuth<Free>> for PoolPred {
            open spec fn atomic_inv(k: Loc, v: u64, g: AllocAuth<Free>) -> bool {
                g@ == Free(v as nat) && g.id() == k
            }
        }

        /// A pool that hands out `remaining` blocks without asking the global allocator (it returns
        /// `Err` for them here, to keep the example small), and then asks the global allocator
        pub struct Pool {
            remaining: AtomicU64<Loc, AllocAuth<Free>, PoolPred>,
            reg: Tracked<Registered<Free>>,
        }

        impl Pool {
            #[verifier::type_invariant]
            spec fn inv(&self) -> bool {
                self.remaining.well_formed() && self.remaining.constant() == self.reg@.loc()
            }

            pub closed spec fn id(&self) -> Loc { self.reg@.loc() }

            fn new(n: u64) -> (p: Self)
                ensures
                    allocator_heap() == heap_register::<Free>(old_allocator_heap(), p.id(), Free(n as nat)),
            {
                let tracked (auth, reg) = AllocAuth::register(Free(n as nat));
                let ghost l = reg.loc();
                let remaining = AtomicU64::new(Ghost(l), n, Tracked(auth));
                Pool { remaining, reg: Tracked(reg) }
            }
        }

        unsafe impl Allocator for Pool {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                proof { use_type_invariant(self); }
                let tracked reg = self.reg.borrow();
                let ghost s = heap_state::<Free>(allocator_heap(), reg.loc());
                let v = atomic_with_ghost!(&self.remaining => load(); ghost g => {
                    g.lower_bound(reg);
                });
                if v > 0 {
                    atomic_with_ghost!(&self.remaining => store(v - 1); ghost g => {
                        g.step(reg, Free((v - 1) as nat), if s.0 > 0 { Free((s.0 - 1) as nat) } else { s });
                    });
                    Global.allocate(layout)
                } else {
                    Global.allocate(layout)
                }
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
            }
        }

        unsafe impl AllocFreeDrop for Pool {}

        unsafe impl BoundedAllocator for Pool {
            open spec fn max_cost() -> int { 1 }
        }

        unsafe impl StatefulAllocator for Pool {
            type State = Free;

            open spec fn loc(&self) -> Loc { self.id() }

            proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) {
                self.reg.borrow()
            }

            open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
                if s.0 > 0 { 0 } else { 1 }
            }

            open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
                if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the allocations must be within `allocate_cost_at` of the state on entry")
}

test_verify_one_file_with_options! {
    #[test] stateful_impl_must_step ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::*;
        use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator};
        use vstd::alloc_heap::*;
        use vstd::resource::Loc;
        use vstd::resource::preorder_auth::Preorder;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Free(pub nat);
        impl Preorder for Free {
            open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
            proof fn le_refl(a: Self) {}
            proof fn le_trans(a: Self, b: Self, c: Self) {}
        }

        pub struct PoolPred;
        impl AtomicInvariantPredicate<Loc, u64, AllocAuth<Free>> for PoolPred {
            open spec fn atomic_inv(k: Loc, v: u64, g: AllocAuth<Free>) -> bool {
                g@ == Free(v as nat) && g.id() == k
            }
        }

        /// A pool that hands out `remaining` blocks without asking the global allocator (it returns
        /// `Err` for them here, to keep the example small), and then asks the global allocator
        pub struct Pool {
            remaining: AtomicU64<Loc, AllocAuth<Free>, PoolPred>,
            reg: Tracked<Registered<Free>>,
        }

        impl Pool {
            #[verifier::type_invariant]
            spec fn inv(&self) -> bool {
                self.remaining.well_formed() && self.remaining.constant() == self.reg@.loc()
            }

            pub closed spec fn id(&self) -> Loc { self.reg@.loc() }

            fn new(n: u64) -> (p: Self)
                ensures
                    allocator_heap() == heap_register::<Free>(old_allocator_heap(), p.id(), Free(n as nat)),
            {
                let tracked (auth, reg) = AllocAuth::register(Free(n as nat));
                let ghost l = reg.loc();
                let remaining = AtomicU64::new(Ghost(l), n, Tracked(auth));
                Pool { remaining, reg: Tracked(reg) }
            }
        }

        unsafe impl Allocator for Pool {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                proof { use_type_invariant(self); }
                let tracked reg = self.reg.borrow();
                let ghost s = heap_state::<Free>(allocator_heap(), reg.loc());
                let v = atomic_with_ghost!(&self.remaining => load(); ghost g => {
                    g.lower_bound(reg);
                });
                if v > 0 {
                    Err(AllocError)
                } else {
                    Global.allocate(layout)
                }
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
            }
        }

        unsafe impl AllocFreeDrop for Pool {}

        unsafe impl BoundedAllocator for Pool {
            open spec fn max_cost() -> int { 1 }
        }

        unsafe impl StatefulAllocator for Pool {
            type State = Free;

            open spec fn loc(&self) -> Loc { self.id() }

            proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) {
                self.reg.borrow()
            }

            open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
                if s.0 > 0 { 0 } else { 1 }
            }

            open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
                if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the heap must move as `allocate_next` says")
}

test_verify_one_file_with_options! {
    #[test] stateful_dealloc_must_preserve ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::*;
        use vstd::alloc_check::{AllocFreeDrop, BoundedAllocator};
        use vstd::alloc_heap::*;
        use vstd::resource::Loc;
        use vstd::resource::preorder_auth::Preorder;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Free(pub nat);
        impl Preorder for Free {
            open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
            proof fn le_refl(a: Self) {}
            proof fn le_trans(a: Self, b: Self, c: Self) {}
        }

        pub struct PoolPred;
        impl AtomicInvariantPredicate<Loc, u64, AllocAuth<Free>> for PoolPred {
            open spec fn atomic_inv(k: Loc, v: u64, g: AllocAuth<Free>) -> bool {
                g@ == Free(v as nat) && g.id() == k
            }
        }

        /// A pool that hands out `remaining` blocks without asking the global allocator (it returns
        /// `Err` for them here, to keep the example small), and then asks the global allocator
        pub struct Pool {
            remaining: AtomicU64<Loc, AllocAuth<Free>, PoolPred>,
            reg: Tracked<Registered<Free>>,
        }

        impl Pool {
            #[verifier::type_invariant]
            spec fn inv(&self) -> bool {
                self.remaining.well_formed() && self.remaining.constant() == self.reg@.loc()
            }

            pub closed spec fn id(&self) -> Loc { self.reg@.loc() }

            fn new(n: u64) -> (p: Self)
                ensures
                    allocator_heap() == heap_register::<Free>(old_allocator_heap(), p.id(), Free(n as nat)),
            {
                let tracked (auth, reg) = AllocAuth::register(Free(n as nat));
                let ghost l = reg.loc();
                let remaining = AtomicU64::new(Ghost(l), n, Tracked(auth));
                Pool { remaining, reg: Tracked(reg) }
            }
        }

        unsafe impl Allocator for Pool {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                proof { use_type_invariant(self); }
                let tracked reg = self.reg.borrow();
                let ghost s = heap_state::<Free>(allocator_heap(), reg.loc());
                let v = atomic_with_ghost!(&self.remaining => load(); ghost g => {
                    g.lower_bound(reg);
                });
                if v > 0 {
                    atomic_with_ghost!(&self.remaining => store(v - 1); ghost g => {
                        g.step(reg, Free((v - 1) as nat), if s.0 > 0 { Free((s.0 - 1) as nat) } else { s });
                    });
                    Err(AllocError)
                } else {
                    Global.allocate(layout)
                }
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
                let _ = self.allocate(layout);
            }
        }

        unsafe impl AllocFreeDrop for Pool {}

        unsafe impl BoundedAllocator for Pool {
            open spec fn max_cost() -> int { 1 }
        }

        unsafe impl StatefulAllocator for Pool {
            type State = Free;

            open spec fn loc(&self) -> Loc { self.id() }

            proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) {
                self.reg.borrow()
            }

            open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
                if s.0 > 0 { 0 } else { 1 }
            }

            open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
                if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "may change the allocator heap")
}

test_verify_one_file_with_options! {
    #[test] stateful_bare_statement ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        #[allow(unused_must_use)]
        fn one(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 1,
            allocates 0
        {
            p.allocate(l);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] stateful_drop_must_preserve ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        pub struct Holder<'a> { p: &'a Pool, l: Layout }

        impl<'a> Drop for Holder<'a> {
            fn drop(&mut self)
                opens_invariants none
                no_unwind
                allocates 1
            {
                let _ = self.p.allocate(self.l);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "may change the allocator heap")
}

test_verify_one_file_with_options! {
    #[test] stateful_no_heap_in_closure ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn f(p: &Pool, l: Layout) {
            let c = || {
                // (the closure runs later: the pool's state is unknown here)
                assert(allocator_state(p).0 >= 1); // FAILS
            };
        }

        fn g(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 1,
        {
            let c = || { assert(allocator_state(p).0 >= 1); }; // FAILS
            assert(allocator_state(p).0 >= 1);
        }

        fn h(p: &Pool) {
            let c = || { assert(old_allocator_state(p).0 >= 1); };
        }
    } => Err(err) => assert_vir_error_msg(err, "a closure body cannot use `old_allocator_state`")
}

test_verify_one_file_with_options! {
    #[test] stateful_pool_not_sync ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn need_sync<T: Sync>() {}
        fn f() { need_sync::<Pool>(); }
    } => Err(err) => assert_rust_error_msg(err, "cannot be shared between threads safely")
}

test_verify_one_file_with_options! {
    #[test] stateful_heap_in_closure_unknown ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn g(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 1,
        {
            let c = || { assert(allocator_state(p).0 >= 1); }; // FAILS
            assert(allocator_state(p).0 >= 1);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] stateful_grow_default_and_ref ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        // (Pool's `Allocator` impl does not define `grow`: std's default body allocates once with
        // the new layout, so the state moves as `allocate` says)
        fn grow_once(p: &Pool, ptr: NonNull<u8>, l1: Layout, l2: Layout)
            requires allocator_state(p).0 >= 1,
            ensures allocator_state(p).0 == old_allocator_state(p).0 - 1,
            allocates 0
        {
            let _ = unsafe { p.grow(ptr, l1, l2) };
        }

        // `&A` forwards every method to `A`
        fn through_ref(p: &Pool, l: Layout)
            requires allocator_state(p).0 >= 1,
            ensures allocator_state(p).0 == old_allocator_state(p).0 - 1,
            allocates 0
        {
            let _ = <&Pool as Allocator>::allocate(&p, l);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] stateful_override_needs_method ["vstd", "-V alloc-check"] => POOL.to_string().replace(
        "open spec fn allocate_next(",
        "open spec fn grow_next(&self, s: Free, ptr: NonNull<u8>, o: Layout, n: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free { s }\n    open spec fn allocate_next(",
    ) => Err(err) => assert_vir_error_msg(err, "defines `grow_next`, but its `Allocator` impl does not define `grow` and `grow_zeroed`")
}

test_verify_one_file_with_options! {
    #[test] stateful_effect_per_instantiation ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        fn push_generic<A: Allocator + BoundedAllocator>(v: &mut Vec<u8, A>) {
            v.push(1);
        }

        // (instantiated with the global allocator, push_generic cannot reach the pool)
        fn keeps(p: &Pool, v: &mut Vec<u8>)
            requires allocator_state(p).0 >= 1,
        {
            push_generic(v);
            assert(allocator_state(p).0 >= 1);
        }

        fn loses<'a>(p: &'a Pool, v: &mut Vec<u8, &'a Pool>)
            requires allocator_state(p).0 >= 1,
        {
            push_generic(v);
            assert(allocator_state(p).0 >= 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] stateful_vec_push ["vstd", "-V alloc-check"] => POOL.to_string() + verus_code_str! {
        use vstd::std_specs::vec::*;

        // a push that grows a vector with no buffer yet allocates once through the pool
        fn push_new<'a>(p: &'a Pool, v: &mut Vec<u64, &'a Pool>)
            requires
                allocator_state(p).0 >= 1,
                spec_vec_capacity(&*old(v)) == 0,
                *spec_vec_allocator(&*old(v)) == *p,
            ensures
                allocator_state(p).0 == old_allocator_state(p).0 - 1,
            allocates 0
        {
            v.push(7);
        }

        // and a push that does not grow leaves the pool alone
        fn push_room<'a>(p: &'a Pool, v: &mut Vec<u64, &'a Pool>)
            requires
                old(v)@.len() < spec_vec_capacity(&*old(v)),
            ensures
                allocator_state(p) == old_allocator_state(p),
            allocates 0
        {
            v.push(7);
        }

        // a global-allocator vector keeps the pool's state
        fn push_global(p: &Pool, v: &mut Vec<u64>)
            requires allocator_state(p).0 >= 1,
            ensures allocator_state(p) == old_allocator_state(p),
        {
            v.push(7);
        }
    } => Ok(())
}
