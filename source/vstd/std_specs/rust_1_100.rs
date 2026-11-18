//! Specifications for the std (core, alloc and std) items that Rust 1.100.0 stabilizes.
//!
//! Collected in one module so that they can be compared with, or replaced by, upstream Verus's
//! own support for 1.100 when it lands. Covered here:
//!
//! - core (also `no_std`): `bool::toggle`, `mem::DropGuard` (`new`,
//!   `dismiss`, `Deref`, `DerefMut`), `cell::UnsafeCell::{as_ref_unchecked, as_mut_unchecked,
//!   replace}`, and `alloc::{Allocator, AllocError, Layout}` as types (`ptr::NonNull` is in
//!   `std_specs::ptr`)
//! - alloc (also `no_std` with `alloc`): `Vec::from_fn`, `Vec::allocator`, `Box::allocator`,
//!   `Box::new_in`, `Box::take`, `Box::map`, `Rc::map`, `Arc::map`, `Allocator for
//!   alloc::alloc::Global`
//! - std: `Allocator for std::alloc::System`, `Default for std::sync::Once`
//!
//! Not covered: `mem::conjure_zst` (std requires `T` to be zero-sized *and* inhabited, with
//! every value valid, which a precondition cannot state: conjuring a zero-sized type whose
//! invariant is `false` would prove anything). Also not covered (Verus cannot use them in
//! verified code yet): `str::{trim_prefix, trim_suffix}`
//! and the slice ones (vstd has no `Pattern`/`SlicePattern` specification), `Path::trim_prefix`
//! (no `Path` specification), `PartialEq` between slices and `Cow<[U]>`, the `Allocator` impls
//! that forward to an allocator they hold (`Box`, `Rc`, `Arc`, `Pin`: their cost is
//! uninterpreted; `&A` and `&mut A` cost what `A` costs), the raw-pointer
//! constructors and destructors with an allocator (`Box::from_raw_in`,
//! `Vec::into_raw_parts_with_allocator`, ...: vstd has no raw `Box`/`Vec` specifications), the
//! Windows process extensions, and the `alloc::fmt::NumBuffer` re-export. The never type `!` (now
//! stable) needs no specification; `core::convert::Infallible` is now an alias of it, so Verus
//! now rejects a datatype with a field of type `Infallible` ("never-to-any coercion is not allowed
//! in spec mode"), which it accepted with 1.99.1.
//!
//! Every function has an `allocates` bound (for `-V alloc-check`): an upper bound on the calls to
//! an allocator that obtain memory, see `vir/src/alloc_check.rs`. Only the program's calls to an
//! allocator are counted, one each (`allocate`, `allocate_zeroed`, `grow`, `grow_zeroed`,
//! `shrink`), whatever the allocator: an allocator's own code is the runtime, and what it
//! allocates itself is not counted (as in FP², where the memory manager is outside the calculus).
#![allow(unused_imports)]
use super::super::prelude::*;

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use alloc::rc::Rc;
#[cfg(feature = "alloc")]
use alloc::sync::Arc;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use core::alloc::{AllocError, Allocator, Layout};
use core::mem::DropGuard;
use core::ptr::NonNull;

verus! {

//////// core
pub assume_specification[ bool::toggle ](b: &mut bool)
    ensures
        *final(b) == !*old(b),
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// `DropGuard<T, F>` runs `f(inner)` when it is dropped. (Under -V alloc-check its drop is not
/// trusted, since it calls user code; `dismiss` returns the value without running `f`.)
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(F)]
pub struct ExDropGuard<T, F: FnOnce(T)>(DropGuard<T, F>);

pub uninterp spec fn drop_guard_inner<T, F: FnOnce(T)>(g: DropGuard<T, F>) -> T;

pub uninterp spec fn drop_guard_fn<T, F: FnOnce(T)>(g: DropGuard<T, F>) -> F;

pub assume_specification<T, F: FnOnce(T)>[ DropGuard::<T, F>::new ](inner: T, f: F) -> (g:
    DropGuard<T, F>)
    ensures
        drop_guard_inner(g) == inner,
        drop_guard_fn(g) == f,
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification<T, F: FnOnce(T)>[ DropGuard::<T, F>::dismiss ](
    guard: DropGuard<T, F>,
) -> (r: T)
    ensures
        r == drop_guard_inner(guard),
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification<T, F: FnOnce(T)>[ <DropGuard<T, F> as core::ops::Deref>::deref ](
    guard: &DropGuard<T, F>,
) -> (r: &T)
    ensures
        *r == drop_guard_inner(*guard),
    allocates
        0,
;

pub assume_specification<T, F: FnOnce(T)>[ <DropGuard<T, F> as core::ops::DerefMut>::deref_mut ](
    guard: &mut DropGuard<T, F>,
) -> (r: &mut T)
    ensures
        *r == drop_guard_inner(*old(guard)),
        drop_guard_inner(*final(guard)) == *final(r),
        drop_guard_fn(*final(guard)) == drop_guard_fn(*old(guard)),
    allocates
        0,
;

/// `UnsafeCell` as a type (its contents are not modeled); the methods stabilized in 1.100 are
/// `unsafe` and only access the contents. Their safety conditions (no other live reference to
/// the contents) cannot be written as preconditions, so they are `#[verifier::trusted_only]`:
/// verified code calls them only in a `#[verifier::trusted_call]` block (`vstd::cell::PCell` is
/// the verified alternative).
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExUnsafeCell<T: ?Sized>(core::cell::UnsafeCell<T>);

#[verifier::trusted_only]
pub assume_specification<T: ?Sized>[ core::cell::UnsafeCell::<T>::as_ref_unchecked ](
    cell: &core::cell::UnsafeCell<T>,
) -> &T
    opens_invariants none
    no_unwind
    allocates
        0,
;

#[verifier::trusted_only]
pub assume_specification<T: ?Sized>[ core::cell::UnsafeCell::<T>::as_mut_unchecked ](
    cell: &core::cell::UnsafeCell<T>,
) -> &mut T
    opens_invariants none
    no_unwind
    allocates
        0,
;

#[verifier::trusted_only]
pub assume_specification<T>[ core::cell::UnsafeCell::<T>::replace ](
    cell: &core::cell::UnsafeCell<T>,
    value: T,
) -> T
    opens_invariants none
    no_unwind
    allocates
        0,
;

//////// core::alloc (allocator_api, stable since 1.100)
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLayout(Layout);

#[verifier::external_type_specification]
pub struct ExAllocError(AllocError);

/// A model of `Layout`: its size and alignment (the two fields of a `Layout`)
pub uninterp spec fn spec_layout(size: nat, align: nat) -> Layout;

pub uninterp spec fn spec_layout_size(l: Layout) -> nat;

pub uninterp spec fn spec_layout_align(l: Layout) -> nat;

pub broadcast axiom fn axiom_spec_layout_size(size: nat, align: nat)
    ensures
        #[trigger] spec_layout_size(spec_layout(size, align)) == size,
;

pub broadcast axiom fn axiom_spec_layout_align(size: nat, align: nat)
    ensures
        #[trigger] spec_layout_align(spec_layout(size, align)) == align,
;

/// The layout of an array of `n` values of type `T` (`Layout::array::<T>(n)`, which is
/// `Layout::new::<T>()` for `n == 1`)
pub open spec fn spec_array_layout<T>(n: nat) -> Layout {
    spec_layout(n * super::super::layout::size_of::<T>(), super::super::layout::align_of::<T>())
}

/// A `Layout`'s alignment is a power of two and its size, rounded up to the alignment, is at most
/// `isize::MAX` (std's documented invariant, upheld by every constructor). Stated on the values
/// that `size` and `align` read from an executable `Layout`, not on `spec_layout`, which makes a
/// layout of any size and alignment.
pub assume_specification[ Layout::size ](l: &Layout) -> (r: usize)
    ensures
        r == spec_layout_size(*l),
        super::super::layout::valid_layout(r, spec_layout_align(*l) as usize),
        spec_layout_align(*l) <= usize::MAX,
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification[ Layout::align ](l: &Layout) -> (r: usize)
    ensures
        r == spec_layout_align(*l),
        super::super::layout::valid_layout(spec_layout_size(*l) as usize, r),
        spec_layout_size(*l) <= usize::MAX,
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub broadcast group group_rust_1_100_core_axioms {
    axiom_spec_layout_size,
    axiom_spec_layout_align,
}

/// The allocator trait. `deallocate`, `grow`, `grow_zeroed` and `shrink` need a live block of
/// this allocator with a fitting layout, which a precondition cannot say: they are
/// `#[verifier::trusted_only]` (so are their implementations), and verified code calls them only
/// in a `#[verifier::trusted_call]` block (`vstd::raw_ptr::deallocate` frees with a `Dealloc`
/// permission instead). -V alloc-check counts a call to an allocator, not what the allocator does:
/// `allocate` and `allocate_zeroed` are one allocation and do not deallocate; `grow`,
/// `grow_zeroed` and `shrink` are one allocation and may deallocate (they may move the block);
/// `deallocate` allocates nothing and deallocates. The bodies of `Allocator` impls (and of an
/// allocator type's `Clone` and `Drop` impls) are the runtime: their allocations, deallocations and
/// stack are not checked.
/// `Allocator`'s contract for a block it returns: "the returned block of memory meets the size and
/// alignment guarantees of `layout`" (std 1.100, `Allocator::allocate`; `grow` and `shrink` for
/// the new layout). std's containers rely on it, and use only the pointer.
pub open spec fn allocator_block_fits(
    r: Result<NonNull<[u8]>, AllocError>,
    layout: Layout,
) -> bool {
    r matches Ok(b) ==> super::super::alloc_check::block_len(b) >= spec_layout_size(layout)
        && super::super::alloc_check::block_addr(b) as nat % spec_layout_align(layout) == 0
}

#[verifier::external_trait_specification]
pub unsafe trait ExAllocator {
    type ExternalTraitSpecificationFor: core::alloc::Allocator;

    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        ensures
            allocator_block_fits(r, layout),
        allocates
            1int,
    ;

    fn allocate_zeroed(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        ensures
            allocator_block_fits(r, layout),
        allocates
            1int,
    ;

    #[verifier::trusted_only]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates
            0,
    ;

    #[verifier::trusted_only]
    unsafe fn grow(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> (r: Result<
        NonNull<[u8]>,
        AllocError,
    >)
        ensures
            allocator_block_fits(r, new_layout),
        allocates
            1int,
    ;

    #[verifier::trusted_only]
    unsafe fn grow_zeroed(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> (r:
        Result<NonNull<[u8]>, AllocError>)
        ensures
            allocator_block_fits(r, new_layout),
        allocates
            1int,
    ;

    #[verifier::trusted_only]
    unsafe fn shrink(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> (r: Result<
        NonNull<[u8]>,
        AllocError,
    >)
        ensures
            allocator_block_fits(r, new_layout),
        allocates
            1int,
    ;
}

} // verus!
// The std allocators (`Global` is the global allocator, `System` the system's; a
// `#[global_allocator]` replaces what `Global` calls), with the bounds of the `Allocator`
// declaration.
macro_rules! std_allocator_specs {
    ($cfg:meta, $a:ty) => {
        #[$cfg]
        verus! {
            pub assume_specification[ <$a as core::alloc::Allocator>::allocate ](
                a: &$a,
                layout: Layout,
            ) -> (r: Result<NonNull<[u8]>, AllocError>)
                ensures
                    allocator_block_fits(r, layout),
                allocates deallocates_when(1int, false)
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::allocate_zeroed ](
                a: &$a,
                layout: Layout,
            ) -> (r: Result<NonNull<[u8]>, AllocError>)
                ensures
                    allocator_block_fits(r, layout),
                allocates deallocates_when(1int, false)
            ;

            #[verifier::trusted_only]
            pub assume_specification[ <$a as core::alloc::Allocator>::deallocate ](
                a: &$a,
                ptr: NonNull<u8>,
                layout: Layout,
            )
                allocates 0
            ;

            #[verifier::trusted_only]
            pub assume_specification[ <$a as core::alloc::Allocator>::grow ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> (r: Result<NonNull<[u8]>, AllocError>)
                ensures
                    allocator_block_fits(r, new_layout),
            ;

            #[verifier::trusted_only]
            pub assume_specification[ <$a as core::alloc::Allocator>::grow_zeroed ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> (r: Result<NonNull<[u8]>, AllocError>)
                ensures
                    allocator_block_fits(r, new_layout),
            ;

            #[verifier::trusted_only]
            pub assume_specification[ <$a as core::alloc::Allocator>::shrink ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> (r: Result<NonNull<[u8]>, AllocError>)
                ensures
                    allocator_block_fits(r, new_layout),
            ;
        }
    };
}

std_allocator_specs!(cfg(feature = "alloc"), alloc::alloc::Global);

#[cfg(feature = "std")]
verus! {

#[verifier::external_type_specification]
pub struct ExSystem(std::alloc::System);

/// `std::sync::Once` as a type; `Once: Default` is new in 1.100
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExOnce(std::sync::Once);

pub assume_specification[ <std::sync::Once as core::default::Default>::default ]() -> std::sync::Once
    allocates
        0,
;

} // verus!
std_allocator_specs!(cfg(feature = "std"), std::alloc::System);

#[cfg(feature = "alloc")]
verus! {

//////// alloc
/// The allocations of the calls `f(0)`, ..., `f(length - 1)` that `Vec::from_fn(length, f)`
/// makes. It is 0 if they cannot allocate: for an `Fn` closure, every call is a call of the same
/// value `f`; an `FnMut` closure may change between calls, so then the premise is about every
/// value of its type.
pub uninterp spec fn vec_from_fn_cost<T, F>(f: F, length: usize) -> int;

pub broadcast axiom fn axiom_vec_from_fn_cost<T, F: FnOnce(usize) -> T>(f: F, length: usize)
    ensures
        #[trigger] vec_from_fn_cost::<T, F>(f, length) >= 0,
        (forall|g: F, i: usize| #[trigger] call_allocates(g, (i,)) == 0) ==> vec_from_fn_cost::<
            T,
            F,
        >(f, length) == 0,
;

pub broadcast axiom fn axiom_vec_from_fn_cost_fn<T, F: Fn(usize) -> T>(f: F, length: usize)
    requires
        forall|i: usize| #[trigger] call_allocates(f, (i,)) == 0,
    ensures
        #[trigger] vec_from_fn_cost::<T, F>(f, length) == 0,
;

pub broadcast group group_rust_1_100_axioms {
    axiom_vec_from_fn_cost,
    axiom_vec_from_fn_cost_fn,
}

// `(0..length).map(f).collect()`: `Map<Range<usize>, F>` is `TrustedLen`, so the vector is
// allocated once with capacity `length` (std 1.100 `alloc/src/vec/mod.rs`, `from_fn`)
pub assume_specification<T, F: FnMut(usize) -> T>[ Vec::<T>::from_fn::<F> ](
    length: usize,
    f: F,
) -> (v: Vec<T>)
    requires
        forall|i: usize| i < length ==> f.requires((i,)),
    ensures
        v@.len() == length,
    allocates
        (if length == 0 {
            0int
        } else {
            1int
        }) + vec_from_fn_cost::<T, F>(f, length),
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::allocator ](v: &Vec<T, A>) -> (r: &A)
    ensures
        *r == super::vec::spec_vec_allocator(v),
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// -V alloc-check: the allocator of a box (the containers' costs may depend on its value)
pub uninterp spec fn spec_box_allocator<T: ?Sized, A: Allocator>(b: &Box<T, A>) -> A;

pub assume_specification<T: ?Sized, A: Allocator>[ Box::<T, A>::allocator ](b: &Box<T, A>) -> (r:
    &A)
    ensures
        *r == spec_box_allocator(b),
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// `Box::new_in` allocates `Layout::new::<T>()` with the given allocator (or nothing for a
/// zero-sized `T`: std 1.100 `Box::try_new_uninit_in` gives it a dangling pointer, without calling
/// the allocator)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::new_in ](x: T, alloc: A) -> (b: Box<T, A>)
    ensures
        *b == x,
        spec_box_allocator(&b) == alloc,
    allocates
        if crate::layout::size_of::<T>() == 0 {
            0int
        } else {
            1int
        },
;

/// `Box::take` moves the value out and keeps the allocation (with uninitialized contents)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::take ](boxed: Box<T, A>) -> (r: (
    T,
    Box<core::mem::MaybeUninit<T>, A>,
))
    ensures
        r.0 == *boxed,
        spec_box_allocator(&r.1) == spec_box_allocator(&boxed),
    opens_invariants none
    no_unwind
    allocates
        0,
;

// `Box::map` reuses the allocation if `T` and `U` have the same layout, and otherwise frees it
// and allocates a new box (std 1.100 `alloc/src/boxed.rs`); `Rc::map`/`Arc::map` reuse it only
// if the pointer is also unique, and otherwise allocate a new one (and drop their reference).
pub assume_specification<T, A: Allocator, U, F: FnOnce(T) -> U>[ Box::<T, A>::map::<U> ](
    this: Box<T, A>,
    f: F,
) -> (r: Box<U, A>)
    requires
        f.requires((*this,)),
    ensures
        f.ensures((*this,), *r),
        spec_box_allocator(&r) == spec_box_allocator(&this),
    allocates
        (if super::super::layout::size_of::<T>() == super::super::layout::size_of::<U>()
            && super::super::layout::align_of::<T>() == super::super::layout::align_of::<U>() {
            0int
        } else {
            1int
        }) + call_allocates(f, (*this,)),
;

pub assume_specification<T, A: Allocator, U, F: FnOnce(&T) -> U>[ Rc::<T, A>::map::<U> ](
    this: Rc<T, A>,
    f: F,
) -> (r: Rc<U, A>)
    requires
        f.requires((&*this,)),
    ensures
        f.ensures((&*this,), *r),
    allocates
        1 + call_allocates(f, (&*this,)),
;

pub assume_specification<T, A: Allocator, U, F: FnOnce(&T) -> U>[ Arc::<T, A>::map::<U> ](
    this: Arc<T, A>,
    f: F,
) -> (r: Arc<U, A>)
    requires
        f.requires((&*this,)),
    ensures
        f.ensures((&*this,), *r),
    allocates
        1 + call_allocates(f, (&*this,)),
;

} // verus!
