#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -V alloc-check with custom allocators (`core::alloc::Allocator`, stable since Rust 1.100). An
// allocator is the runtime (FP²'s memory manager): only the program's calls to an allocator are
// counted, one each (`allocate`, `allocate_zeroed`, `grow`, `grow_zeroed`, `shrink`), whatever
// the allocator. Its own code (its `Allocator`, `Clone` and `Drop` impls) is not checked for
// allocations, deallocations or stack.

/// An allocator that forwards to the global one (it defines only `allocate` and `deallocate`, so
/// `grow` and the others run std's default bodies), and an arena that hands out no new memory
const ALLOCATORS: &str = verus_code_str! {
    use vstd::prelude::*;
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    pub struct Fwd;

    unsafe impl Allocator for Fwd {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
            Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            #[verifier::trusted_call] { unsafe { Global.deallocate(ptr, layout) } }
        }
    }

    pub struct Arena;

    unsafe impl Allocator for Arena {
        fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
            Err(AllocError)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        }
    }
};

test_verify_one_file_with_options! {
    // every call to an allocator is one, whatever the allocator
    #[test] allocator_calls_count_one ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        // `push` that grows calls `grow` (std's default body: one `allocate`)
        fn push_one(v: &mut Vec<u8, Fwd>)
            allocates 1
        {
            v.push(3);
        }

        fn push_arena(v: &mut Vec<u8, Arena>)
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

        // (an empty vector and a zero-sized box do not call the allocator)
        fn sizes() -> (n: usize)
            allocates 1
        {
            let e: Vec<u64, Arena> = Vec::with_capacity_in(0, Arena);
            let z = Box::new_in((), Arena);
            let v: Vec<u64, Arena> = Vec::with_capacity_in(16, Arena);
            v.capacity()
        }

        fn generic<A: std::alloc::Allocator>(v: &mut Vec<u8, A>)
            allocates 1
        {
            v.push(3);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // an arena that hands out no new memory is still called: the call is the program's
    #[test] arena_calls_still_count ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        fn push_arena(v: &mut Vec<u8, Arena>)
            allocates 0 // FAILS
        {
            v.push(3);
        }
    } => Err(err) => assert_one_fails(err)
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
    // dropping a container calls its allocator's `deallocate` and drops the allocator: neither
    // allocates anything of the program's
    #[test] container_with_user_allocator_dropped ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        fn drop_it(v: Vec<u8, Fwd>, b: Box<u64, Arena>)
            allocates 0
        {
        }

        fn drop_generic<A: std::alloc::Allocator>(v: Vec<u8, A>, b: Box<u64, A>)
            allocates 0
        {
        }

        fn drop_allocator(a: Fwd)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // an allocator's own code is not checked: it may allocate (here twice) and free, and its
    // `Clone` may allocate; a call of it counts as the `Allocator` declaration says
    #[test] allocator_code_is_runtime ["vstd", "-V alloc-check"] => verus_code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        pub struct Twice;

        impl Clone for Twice {
            fn clone(&self) -> (r: Self) {
                let b = Box::new(1u8);
                Twice
            }
        }

        unsafe impl Allocator for Twice {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                let _ = Global.allocate(layout);
                Global.allocate(layout)
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                let b = Box::new(1u8);
            }
        }

        fn push_one(v: &mut Vec<u8, Twice>)
            allocates 1
        {
            v.push(3);
        }

        fn copy(v: &Vec<u8, Twice>) -> (r: Vec<u8, Twice>)
            allocates 1
        {
            v.clone()
        }

        fn copy_empty(v: &Vec<u8, Twice>) -> (r: Vec<u8, Twice>)
            requires v@.len() == 0,
            allocates 0
        {
            v.clone()
        }

        fn copy_allocator(a: &Twice) -> (r: Twice)
            allocates 0
        {
            a.clone()
        }

        fn direct(a: &Twice, l: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
            allocates 1
        {
            a.allocate(l)
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // an allocator need not be verified at all
    #[test] allocator_outside_verus ["vstd", "-V alloc-check"] => code! {
        use vstd::prelude::*;
        use std::alloc::{Allocator, AllocError, Global, Layout};
        use std::ptr::NonNull;

        unsafe impl Allocator for Ext {
            fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> {
                let _ = Global.allocate(l);
                Global.allocate(l)
            }
            unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) { unsafe { Global.deallocate(p, l) } }
        }

        impl Clone for Ext {
            fn clone(&self) -> Self { let _b = Box::new(1u8); Ext }
        }

        verus! {
        pub struct Ext;

        fn push_one(v: &mut Vec<u8, Ext>)
            allocates 1
        {
            v.push(3);
        }

        fn drop_it(v: Vec<u8, Ext>)
            allocates 0
        {
        }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // dropping a `BTreeMap` clones its allocator for every node it frees: the runtime's
    #[test] btree_drop_user_allocator ["vstd", "-V alloc-check"] => ALLOCATORS.to_string() + verus_code_str! {
        use std::collections::BTreeMap;
        impl Clone for Fwd {
            fn clone(&self) -> (r: Self) {
                let b = Box::new(1u8);
                Fwd
            }
        }
        #[verifier::external]
        unsafe impl core::alloc::AllocatorClone for Fwd {}

        fn f(m: BTreeMap<u8, u8, Fwd>)
            allocates 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // An allocator that frees, verified with --no-cheating. `allocate` gives up the permission of
    // the block it returns (`hand_out`, keeping the receipt and the block's `Dealloc` in a
    // `LocalInvariant`); `deallocate` reclaims it (`reclaim`, with the receipt) and frees it with
    // `raw_ptr::deallocate` if the address and layout are the ones it recorded (and leaves anything
    // else alone). (This test only verifies it. Compiled separately with a counting global
    // allocator, three `Box::new_in` made 3 allocations and 3 frees.)
    #[test] one_slot_allocator_frees_no_cheating ["vstd", "-V alloc-check", "--no-cheating"] => code! {
        use vstd::prelude::*;
        use vstd::raw_ptr;
        use vstd::cell::pcell::{PCell, PointsTo as CellPerm};
        use vstd::cell::CellId;
        use vstd::invariant::{LocalInvariant, InvariantPredicate};
        use vstd::open_local_invariant;
        use vstd::alloc_check::{AllocFreeDrop, Handout, hand_out, reclaim};
        use std::alloc::{Allocator, AllocError, Layout};
        use std::ptr::NonNull;

        verus! {

        pub tracked struct Slot {
            pub tracked perm: CellPerm<(*mut u8, usize, usize)>,
            pub tracked blk: Option<(raw_ptr::Dealloc, Handout)>,
        }

        pub struct SlotPred;

        impl InvariantPredicate<CellId, Slot> for SlotPred {
            open spec fn inv(k: CellId, s: Slot) -> bool {
                let (p, size, align) = *s.perm.value();
                &&& s.perm.id() == k
                &&& match s.blk {
                    None => p@.addr == 0,
                    Some((d, h)) => {
                        &&& p@.addr != 0
                        &&& d.addr() == p@.addr
                        &&& d.size() == size
                        &&& d.align() == align
                        &&& h.addr() == p@.addr
                        &&& h.len() == size
                        &&& h.provenance() == d.provenance()
                        &&& p@.provenance == d.provenance()
                    }
                }
            }
        }

        pub struct OneSlot {
            cell: PCell<(*mut u8, usize, usize)>,
            inv: Tracked<LocalInvariant<CellId, Slot, SlotPred>>,
        }

        impl OneSlot {
            #[verifier::type_invariant]
            spec fn wf(&self) -> bool {
                self.inv@.constant() == self.cell.id()
            }

            pub fn new() -> (r: OneSlot) {
                let (cell, Tracked(perm)) = PCell::new((core::ptr::null_mut(), 0usize, 0usize));
                let tracked slot = Slot { perm, blk: None };
                let tracked inv = LocalInvariant::new(cell.id(), slot, 0);
                OneSlot { cell, inv: Tracked(inv) }
            }
        }

        unsafe impl Allocator for OneSlot {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
                allocates 1
            {
                proof { use_type_invariant(self); }
                let size = layout.size();
                let align = layout.align();
                if size == 0 { return Err(AllocError); }
                let mut r = Err(AllocError);
                open_local_invariant!(self.inv.borrow() => slot => {
                    let tracked Slot { perm: mut perm, blk } = slot;
                    let cur = *self.cell.borrow(Tracked(&perm));
                    if cur.0.addr() == 0 {
                        let (p, Tracked(pt), Tracked(d)) = raw_ptr::allocate(size, align);
                        let sp = core::ptr::slice_from_raw_parts_mut(p, size);
                        match NonNull::new(sp) {
                            Some(nn) => {
                                let tracked h = hand_out(pt, nn);
                                let _ = self.cell.replace(Tracked(&mut perm), (p, size, align));
                                proof { slot = Slot { perm, blk: Some((d, h)) }; }
                                r = Ok(nn);
                            }
                            None => {
                                proof { slot = Slot { perm, blk }; }
                            }
                        }
                    } else {
                        proof { slot = Slot { perm, blk }; }
                    }
                });
                r
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
                allocates 0
            {
                proof { use_type_invariant(self); }
                let size = layout.size();
                let align = layout.align();
                let a = ptr.as_ptr().addr();
                open_local_invariant!(self.inv.borrow() => slot => {
                    let tracked Slot { perm: mut perm, blk } = slot;
                    let cur = *self.cell.borrow(Tracked(&perm));
                    if cur.0.addr() != 0 && cur.0.addr() == a && cur.1 == size && cur.2 == align {
                        let tracked (d, h) = blk.tracked_unwrap();
                        let tracked pt = reclaim(ptr, layout, h);
                        raw_ptr::deallocate(cur.0, size, align, Tracked(pt), Tracked(d));
                        let _ = self.cell.replace(Tracked(&mut perm), (core::ptr::null_mut(), 0usize, 0usize));
                        proof { slot = Slot { perm, blk: None }; }
                    } else {
                        // not the block this allocator handed out (std never does this): leave it alone
                        proof { slot = Slot { perm, blk }; }
                    }
                });
            }
        }

        unsafe impl AllocFreeDrop for OneSlot {}

        fn use_it(a: &OneSlot) -> (r: u64)
            ensures r == 5
            allocates 1
        {
            let b = Box::new_in(5u64, a);
            *b
        }

        } // verus!
    } => Ok(())
}
