//! Specifications for the std (core, alloc and std) items that Rust 1.100.0 stabilizes.
//!
//! Collected in one module so that they can be compared with, or replaced by, upstream Verus's
//! own support for 1.100 when it lands. Covered here:
//!
//! - core (also `no_std`): `bool::toggle`, `mem::conjure_zst`, `mem::DropGuard` (`new`,
//!   `dismiss`, `Deref`, `DerefMut`), `cell::UnsafeCell::{as_ref_unchecked, as_mut_unchecked,
//!   replace}`, and `alloc::{Allocator, AllocError, Layout}` and `ptr::NonNull` as types
//! - alloc (also `no_std` with `alloc`): `Vec::from_fn`, `Vec::allocator`, `Box::allocator`,
//!   `Box::new_in`, `Box::take`, `Box::map`, `Rc::map`, `Arc::map`, `Allocator for
//!   alloc::alloc::Global`
//! - std: `Allocator for std::alloc::System`, `Default for std::sync::Once`
//!
//! Not covered (Verus cannot use them in verified code yet): `str::{trim_prefix, trim_suffix}`
//! and the slice ones (vstd has no `Pattern`/`SlicePattern` specification), `Path::trim_prefix`
//! (no `Path` specification), `PartialEq` between slices and `Cow<[U]>`, the `Allocator` impls
//! that forward to an allocator they hold (`Box`, `Rc`, `Arc`, `Pin`: their cost is
//! uninterpreted; `&A` and `&mut A` cost what `A` costs), the raw-pointer
//! constructors and destructors with an allocator (`Box::from_raw_in`,
//! `Vec::into_raw_parts_with_allocator`, ...: vstd has no raw `Box`/`Vec` specifications), the
//! Windows process extensions, and the `alloc::fmt::NumBuffer` re-export. The never type `!` (now
//! stable) needs no specification; `core::convert::Infallible` is now an alias of it.
//!
//! Every function has an `allocates` bound (for `-V alloc-check`): an upper bound on the calls to
//! the allocator that obtain memory, see `vir/src/alloc_check.rs`. An allocation by an allocator
//! of type `A` costs `allocator_allocate_cost::<A>()`, which is 1 for the global and the system
//! allocator and what a custom allocator's `vstd::alloc_check::BoundedAllocator` impl says for it
//! (counted at the leaves); the specifications of the containers (`Vec<T, A>`, `VecDeque<T, A>`,
//! `Box<T, A>`, `HashMap<K, V, S, A>`, ...) charge it per allocation, and
//! `allocator_clone_cost::<A>()` when they clone their allocator.
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

/// -V alloc-check: the allocations of one call of `allocate`, `allocate_zeroed`, `grow`,
/// `grow_zeroed` or `shrink` of an allocator of type `A`, i.e. the bound of these methods on the
/// `Allocator` declaration. Allocations are counted at the leaves: a call to the global or the
/// system allocator is 1, and an allocator that implements `vstd::alloc_check::BoundedAllocator`
/// costs what its `allocate_cost` says (the leaf calls that one call of its methods makes), which
/// its verified `Allocator` impl must stay within. For any other type, this is an uninterpreted
/// per-type cost (like `iter_adapter_cost`: it does not constrain implementations that Verus does
/// not check).
pub uninterp spec fn allocator_allocate_cost<A: ?Sized>() -> int;

/// -V alloc-check: the allocations of cloning an allocator of type `A` (which the containers'
/// `clone` and `split_off` do): 0 for the global allocator and for references; for any other
/// allocator, an uninterpreted per-type cost.
pub uninterp spec fn allocator_clone_cost<A: ?Sized>() -> int;

pub broadcast axiom fn axiom_allocator_allocate_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_allocate_cost::<A>() >= 0,
;

/// (clamped at 0, like every bound)
#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_allocate_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>()
    ensures
        #[trigger] allocator_allocate_cost::<A>() == if A::allocate_cost() >= 0 {
            A::allocate_cost()
        } else {
            0
        },
;

// `&A` and `&mut A` forward every method to `A` (std 1.100 `core/src/alloc/mod.rs`)
pub broadcast axiom fn axiom_ref_allocator_allocate_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_allocate_cost::<&A>() == allocator_allocate_cost::<A>(),
;

pub broadcast axiom fn axiom_mut_ref_allocator_allocate_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_allocate_cost::<&mut A>() == allocator_allocate_cost::<A>(),
;

pub broadcast axiom fn axiom_allocator_clone_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_clone_cost::<A>() >= 0,
;

/// (cloning a shared reference copies it)
pub broadcast axiom fn axiom_ref_allocator_clone_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_clone_cost::<&A>() == 0,
;

pub broadcast group group_rust_1_100_core_axioms {
    axiom_allocator_allocate_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_allocate_cost,
    axiom_ref_allocator_allocate_cost,
    axiom_mut_ref_allocator_allocate_cost,
    axiom_allocator_clone_cost,
    axiom_ref_allocator_clone_cost,
}

/// The allocator trait. -V alloc-check: `deallocate` allocates nothing (the drop rule relies on
/// this: dropping a container calls it), and each of the others costs
/// `allocator_allocate_cost::<Self>()`. These bounds hold for the std allocators and for every
/// implementation that Verus checks, which `vstd::alloc_check::BoundedAllocator` requires; std's
/// default bodies of `allocate_zeroed`, `grow`, `grow_zeroed` and `shrink` call `allocate` or
/// `allocate_zeroed` once and `deallocate` at most once, so they stay within them.
#[verifier::external_trait_specification]
pub unsafe trait ExAllocator {
    type ExternalTraitSpecificationFor: core::alloc::Allocator;

    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_allocate_cost::<Self>(),
    ;

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_allocate_cost::<Self>(),
    ;

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates
            0,
    ;

    unsafe fn grow(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<
        NonNull<[u8]>,
        AllocError,
    >
        allocates
            allocator_allocate_cost::<Self>(),
    ;

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_allocate_cost::<Self>(),
    ;

    unsafe fn shrink(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<
        NonNull<[u8]>,
        AllocError,
    >
        allocates
            allocator_allocate_cost::<Self>(),
    ;
}

} // verus!
// The std allocators: each method is one call to the allocator (`deallocate` frees memory and is
// not counted), i.e. `allocator_allocate_cost` is 1 (`vstd::alloc_check::BoundedAllocator`); the
// specifications below have the bounds of the `Allocator` declaration. (`Global` is the global
// allocator, `System` the system's; a `#[global_allocator]` replaces what `Global` calls.)
macro_rules! std_allocator_specs {
    ($cfg:meta, $a:ty) => {
        #[$cfg]
        verus! {
            pub assume_specification[ <$a as core::alloc::Allocator>::allocate ](
                a: &$a,
                layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::allocate_zeroed ](
                a: &$a,
                layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
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
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::grow_zeroed ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
            ;

            pub assume_specification[ <$a as core::alloc::Allocator>::shrink ](
                a: &$a,
                ptr: NonNull<u8>,
                old_layout: Layout,
                new_layout: Layout,
            ) -> Result<NonNull<[u8]>, AllocError>
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

pub broadcast axiom fn axiom_system_allocator_cost()
    ensures
        #[trigger] allocator_allocate_cost::<std::alloc::System>() == 1,
        #[trigger] allocator_clone_cost::<std::alloc::System>() == 0,
;

pub broadcast group group_rust_1_100_std_axioms {
    axiom_system_allocator_cost,
}

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

pub broadcast axiom fn axiom_global_allocator_allocate_cost()
    ensures
        #[trigger] allocator_allocate_cost::<alloc::alloc::Global>() == 1,
;

pub broadcast axiom fn axiom_global_allocator_clone_cost()
    ensures
        #[trigger] allocator_clone_cost::<alloc::alloc::Global>() == 0,
;

pub broadcast group group_rust_1_100_axioms {
    axiom_vec_from_fn_cost,
    axiom_vec_from_fn_cost_fn,
    axiom_global_allocator_allocate_cost,
    axiom_global_allocator_clone_cost,
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

/// `Box::new_in` allocates with the given allocator (once, or not at all for a zero-sized `T`)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::new_in ](x: T, alloc: A) -> (b: Box<T, A>)
    ensures
        *b == x,
    allocates
        allocator_allocate_cost::<A>(),
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
