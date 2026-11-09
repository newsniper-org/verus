#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// A user's `Allocator` impl must give up the permission of the block it returns
// (`vstd::alloc_check::hand_out`), since std's containers then own that memory, and may take
// back only the block that `deallocate` (or `grow`, `shrink`) frees (`vstd::alloc_check::reclaim`)
// (portable-fip, fip-beta 6f6975af2, §1: an allocator kept the `PointsToRaw` of a block it
// handed out and wrote to it while a `Box` owned it)

const RETURN_ERR: &str =
    "an `Allocator` may return a block only if it gave up the block's permission";

/// a block from `raw_ptr::allocate`, as a `NonNull<[u8]>`, with its permissions
const PRELUDE: &str = verus_code_str! {
    use vstd::prelude::*;
    use vstd::raw_ptr;
    use vstd::alloc_check::{Handout, hand_out, reclaim};
    use std::alloc::{Allocator, AllocError, Global, Layout};
    use std::ptr::NonNull;

    fn get_block(size: usize, align: usize) -> (r: (Option<NonNull<[u8]>>, Tracked<raw_ptr::PointsToRaw>, Tracked<raw_ptr::Dealloc>))
        requires vstd::layout::valid_layout(size, align), size != 0,
        ensures
            r.0 matches Some(nn) ==> r.1@.is_range(vstd::alloc_check::block_addr(nn) as int, vstd::alloc_check::block_len(nn) as int)
                && r.1@.provenance() == vstd::alloc_check::block_provenance(nn),
    {
        let (p, Tracked(pt), Tracked(d)) = raw_ptr::allocate(size, align);
        let sp = core::ptr::slice_from_raw_parts_mut(p, size);
        (NonNull::new(sp), Tracked(pt), Tracked(d))
    }
};

test_verify_one_file_with_options! {
    // the block's permission is kept (here simply not given up)
    #[test] return_without_hand_out ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                if layout.size() == 0 { return Err(AllocError); }
                let (b, Tracked(pt), Tracked(d)) = get_block(layout.size(), layout.align());
                match b { Some(nn) => Ok(nn), None => Err(AllocError) }
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
        }
    } => Err(err) => assert_vir_error_msg(err, RETURN_ERR)
}

test_verify_one_file_with_options! {
    #[test] hand_out_accepted ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                if layout.size() == 0 { return Err(AllocError); }
                let (b, Tracked(pt), Tracked(d)) = get_block(layout.size(), layout.align());
                match b {
                    Some(nn) => {
                        let tracked h = hand_out(pt, nn);
                        Ok(nn)
                    }
                    None => Err(AllocError),
                }
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
        }
        // forwarding to another allocator, and failing, need nothing
        pub struct Fwd;
        unsafe impl Allocator for Fwd {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                if layout.size() == 0 { Err(AllocError) } else { Global.allocate(layout) }
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                #[verifier::trusted_call] { unsafe { Global.deallocate(ptr, layout) } }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // a block handed out, but another one returned
    #[test] return_other_block ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                if layout.size() == 0 { return Err(AllocError); }
                let (b1, Tracked(pt1), Tracked(d1)) = get_block(layout.size(), layout.align());
                let (b2, Tracked(pt2), Tracked(d2)) = get_block(layout.size(), layout.align());
                match (b1, b2) {
                    (Some(n1), Some(n2)) => {
                        let tracked h = hand_out(pt1, n1);
                        Ok(n2)
                    }
                    _ => Err(AllocError),
                }
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
        }
    } => Err(err) => assert_vir_error_msg(err, RETURN_ERR)
}

test_verify_one_file_with_options! {
    #[test] hand_out_in_helper ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        fn helper(Tracked(pt): Tracked<raw_ptr::PointsToRaw>, nn: NonNull<u8>, b: NonNull<[u8]>)
            requires pt.is_range(vstd::alloc_check::block_addr(b) as int, vstd::alloc_check::block_len(b) as int),
                pt.provenance() == vstd::alloc_check::block_provenance(b),
        {
            let tracked h = hand_out(pt, b);
        }
    } => Err(err) => assert_vir_error_msg(err, "`hand_out` may be called only in the body of an `Allocator` impl")
}

test_verify_one_file_with_options! {
    #[test] reclaim_outside_deallocate ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        fn helper(ptr: NonNull<u8>, layout: Layout, Tracked(h): Tracked<Handout>)
            requires h.addr() == vstd::std_specs::ptr::spec_nonnull_as_ptr(ptr)@.addr,
                vstd::std_specs::rust_1_100::spec_layout_size(layout) <= h.len(),
        {
            let tracked pt = reclaim(ptr, layout, h);
        }
    } => Err(err) => assert_vir_error_msg(err, "`reclaim` may be called only in the body of an `Allocator` impl")
}

/// a receipt out of thin air (trusted), to reach the checks on `reclaim`'s use
const FAKE: &str = verus_code_str! {
    #[verifier::external_body]
    proof fn fake_handout(addr: usize, l: Layout) -> (tracked h: Handout)
        ensures h.addr() == addr, vstd::std_specs::rust_1_100::spec_layout_size(l) <= h.len(),
    {
        unimplemented!()
    }
    spec fn addr_of(p: NonNull<u8>) -> usize { vstd::std_specs::ptr::spec_nonnull_as_ptr(p)@.addr }
};

test_verify_one_file_with_options! {
    // a block other than the one being freed
    #[test] reclaim_wrong_ptr ["vstd"] => PRELUDE.to_string() + FAKE + verus_code_str! {
        pub struct A { other: NonNull<u8> }
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                let tracked h = fake_handout(addr_of(self.other), layout);
                let tracked pt = reclaim(self.other, layout, h);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`reclaim` takes back the block that this call frees")
}

test_verify_one_file_with_options! {
    #[test] reclaim_twice ["vstd"] => PRELUDE.to_string() + FAKE + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                let tracked h1 = fake_handout(addr_of(ptr), layout);
                let tracked h2 = fake_handout(addr_of(ptr), layout);
                let tracked pt1 = reclaim(ptr, layout, h1);
                let tracked pt2 = reclaim(ptr, layout, h2);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`reclaim` takes back the block that this call frees")
}

test_verify_one_file_with_options! {
    #[test] reclaim_then_fail ["vstd"] => PRELUDE.to_string() + FAKE + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                Err(AllocError)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
            unsafe fn shrink(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                let tracked h = fake_handout(addr_of(ptr), old_layout);
                let tracked pt = reclaim(ptr, old_layout, h);
                Err(AllocError)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a `grow` or `shrink` that fails must not reclaim the old block")
}

test_verify_one_file_with_options! {
    // a trusted (`external_body`) source of blocks is accepted (as trusted)
    #[test] external_body_source ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        #[verifier::external_body]
        fn chunk(layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
            std::alloc::System.allocate(layout)
        }
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                chunk(layout)
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // a closure may run any number of times, or after the method returns
    #[test] hand_out_in_closure ["vstd"] => PRELUDE.to_string() + verus_code_str! {
        pub struct A;
        unsafe impl Allocator for A {
            fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
                if layout.size() == 0 { return Err(AllocError); }
                let (b, Tracked(pt), Tracked(d)) = get_block(layout.size(), layout.align());
                match b {
                    Some(nn) => {
                        let f = move || { proof { let tracked h = hand_out(pt, nn); } };
                        Ok(nn)
                    }
                    None => Err(AllocError),
                }
            }
            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
        }
    } => Err(err) => assert_vir_error_msg(err, "`hand_out` may be called only in the body of an `Allocator` impl")
}
