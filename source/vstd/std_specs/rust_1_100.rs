//! Specifications for the std (core, alloc and std) items that Rust 1.100.0 stabilizes.
//!
//! Collected in one module so that they can be compared with, or replaced by, upstream Verus's
//! own support for 1.100 when it lands. Covered here:
//!
//! - core (also `no_std`): `bool::toggle`, `mem::conjure_zst`, `mem::DropGuard` (`new`,
//!   `dismiss`, `Deref`, `DerefMut`), `cell::UnsafeCell::{as_ref_unchecked, as_mut_unchecked,
//!   replace}`, and `alloc::{Allocator, AllocError, Layout}` and `ptr::NonNull` as types
//! - alloc (also `no_std` with `alloc`): `Vec::from_fn`, `Vec::allocator`, `Box::allocator`,
//!   `Box::take`, `Box::map`, `Rc::map`, `Arc::map`, `Allocator for alloc::alloc::Global`
//! - std: `Allocator for std::alloc::System`, `Default for std::sync::Once`
//!
//! Not covered (Verus cannot use them in verified code yet): `str::{trim_prefix, trim_suffix}`
//! and the slice ones (vstd has no `Pattern`/`SlicePattern` specification), `Path::trim_prefix`
//! (no `Path` specification), `PartialEq` between slices and `Cow<[U]>`, the `Allocator` impls
//! that forward to another allocator (`&A`, `&mut A`, `Box`, `Rc`, `Arc`), the raw-pointer
//! constructors and destructors with an allocator (`Box::from_raw_in`,
//! `Vec::into_raw_parts_with_allocator`, ...: vstd has no raw `Box`/`Vec` specifications), the
//! Windows process extensions, and the `alloc::fmt::NumBuffer` re-export. The never type `!` (now
//! stable) needs no specification; `core::convert::Infallible` is now an alias of it.
//!
//! Every function has an `allocates` bound (for `-V alloc-check`): an upper bound on the calls to
//! the allocator that obtain memory, see `vir/src/alloc_check.rs`. Custom allocators are not
//! supported by -V alloc-check yet (values with one are rejected by the drop rule), so the costs
//! of an allocator other than the global one are uninterpreted per-type terms.
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

/// `conjure_zst::<T>()` is only defined for zero-sized `T`
pub assume_specification<T>[ core::mem::conjure_zst::<T> ]() -> T
    requires
        super::super::layout::size_of::<T>() == 0,
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
/// `unsafe` and only access the contents
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExUnsafeCell<T: ?Sized>(core::cell::UnsafeCell<T>);

pub assume_specification<T: ?Sized>[ core::cell::UnsafeCell::<T>::as_ref_unchecked ](
    cell: &core::cell::UnsafeCell<T>,
) -> &T
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification<T: ?Sized>[ core::cell::UnsafeCell::<T>::as_mut_unchecked ](
    cell: &core::cell::UnsafeCell<T>,
) -> &mut T
    opens_invariants none
    no_unwind
    allocates
        0,
;

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

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExNonNull<T: core::marker::PointeeSized>(NonNull<T>);

/// The allocator trait. Its methods have no `allocates` bound on the declaration (a call through
/// a generic `A: Allocator` is not bounded); the std allocators' impls have bounds below.
/// (Custom allocators are not supported by -V alloc-check yet.)
#[verifier::external_trait_specification]
pub unsafe trait ExAllocator {
    type ExternalTraitSpecificationFor: core::alloc::Allocator;

    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);

    unsafe fn grow(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<
        NonNull<[u8]>,
        AllocError,
    >;

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>;

    unsafe fn shrink(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<
        NonNull<[u8]>,
        AllocError,
    >;
}

} // verus!
// The std allocators: each method is one call to the allocator (`deallocate` frees memory and is
// not counted). (`Global` is the global allocator, `System` the system's; a `#[global_allocator]`
// replaces what `Global` calls.)
macro_rules! std_allocator_specs {
    ($cfg:meta, $a:ty) => {
        #[$cfg]
        verus! {
            pub assume_specification[ <$a as core::alloc::Allocator>::allocate ](
                a: &$a,
                layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
                allocates 1
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::allocate_zeroed ](
                a: &$a,
                layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
                allocates 1
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::deallocate ](
                a: &$a,
                ptr: NonNull<u8>,
                layout: Layout,
            )
                allocates 0
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::grow ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
                allocates 1
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::grow_zeroed ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
                allocates 1
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::shrink ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
                allocates 1
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

/// The allocations of one allocation by an allocator of type `A` (`allocate` and the like): 1 for
/// the global allocator, an uninterpreted per-type cost for any other (custom allocators are not
/// supported by -V alloc-check yet; this keeps the specifications sound for them)
pub uninterp spec fn allocator_allocate_cost<A: ?Sized>() -> int;

pub broadcast axiom fn axiom_allocator_allocate_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_allocate_cost::<A>() >= 0,
;

pub broadcast axiom fn axiom_global_allocator_allocate_cost()
    ensures
        #[trigger] allocator_allocate_cost::<alloc::alloc::Global>() == 1,
;

pub broadcast group group_rust_1_100_axioms {
    axiom_vec_from_fn_cost,
    axiom_vec_from_fn_cost_fn,
    axiom_allocator_allocate_cost,
    axiom_global_allocator_allocate_cost,
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

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::allocator ](v: &Vec<T, A>) -> &A
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification<T: ?Sized, A: Allocator>[ Box::<T, A>::allocator ](b: &Box<T, A>) -> &A
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// `Box::take` moves the value out and keeps the allocation (with uninitialized contents)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::take ](boxed: Box<T, A>) -> (r: (
    T,
    Box<core::mem::MaybeUninit<T>, A>,
))
    ensures
        r.0 == *boxed,
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
    allocates
        allocator_allocate_cost::<A>() + call_allocates(f, (*this,)),
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
        allocator_allocate_cost::<A>() + call_allocates(f, (&*this,)),
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
        allocator_allocate_cost::<A>() + call_allocates(f, (&*this,)),
;

} // verus!
