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
//! the allocator that obtain memory, see `vir/src/alloc_check.rs`. A call of an allocator's
//! `allocate`, `grow`, ... costs `allocator_allocate_cost(a, layout)`, `allocator_grow_cost(a, ptr,
//! old_layout, new_layout)`, ..., which may depend on the allocator's value and on the arguments,
//! and is at most `allocator_max_cost::<A>()`: 1 for the global and the system allocator, what a
//! custom allocator's `vstd::alloc_check::BoundedAllocator` impl says for it (counted at the
//! leaves). `Vec<T, A>` and `Box<T, A>` charge the cost of the very call they make (`Vec` with its
//! allocator, its buffer pointer, and the layouts of its old capacity and of the capacity that
//! std 1.100's growth policy picks, `vec::vec_amortized_cap`); `VecDeque<T, A>`, `HashMap<K, V, S,
//! A>`, `Rc::map`/`Arc::map` and the containers' `clone`/`split_off` (which allocate with a clone
//! of the allocator) charge the maximum, since vstd does not name their arguments; cloning the
//! allocator costs `allocator_clone_cost::<A>()`.
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

pub assume_specification[ Layout::size ](l: &Layout) -> (r: usize)
    ensures
        r == spec_layout_size(*l),
    opens_invariants none
    no_unwind
    allocates
        0,
;

pub assume_specification[ Layout::align ](l: &Layout) -> (r: usize)
    ensures
        r == spec_layout_align(*l),
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// -V alloc-check: an upper bound on the allocations of one call of `allocate`,
/// `allocate_zeroed`, `grow`, `grow_zeroed` or `shrink` of any allocator of type `A`, with any
/// arguments. Allocations are counted at the leaves: a call to the global or the system allocator
/// is 1, and an allocator that implements `vstd::alloc_check::BoundedAllocator` costs at most what
/// its `max_cost` says. For any other type, this is an uninterpreted per-type cost (like
/// `iter_adapter_cost`: it does not constrain implementations that Verus does not check). The
/// containers charge it where they allocate with arguments (or an allocator) that their
/// specifications cannot name (a cloned allocator, a hash table, ...).
pub uninterp spec fn allocator_max_cost<A: ?Sized>() -> int;

/// -V alloc-check: the allocations of `a.allocate(layout)` and `a.allocate_zeroed(layout)`, i.e.
/// the bound of these methods on the `Allocator` declaration. It may depend on the allocator's
/// value (its configuration) and on the arguments. (For a `BoundedAllocator`, its `allocate_cost`,
/// cut down to `max_cost`.)
pub uninterp spec fn allocator_allocate_cost<A: ?Sized>(a: &A, layout: Layout) -> int;

/// -V alloc-check: the allocations of `a.grow(ptr, old_layout, new_layout)`
pub uninterp spec fn allocator_grow_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> int;

/// -V alloc-check: the allocations of `a.grow_zeroed(ptr, old_layout, new_layout)`
pub uninterp spec fn allocator_grow_zeroed_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> int;

/// -V alloc-check: the allocations of `a.shrink(ptr, old_layout, new_layout)`
pub uninterp spec fn allocator_shrink_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
) -> int;

/// -V alloc-check: the allocations of cloning an allocator of type `A` (which the containers'
/// `clone` and `split_off` do): 0 for the global allocator and for references; for any other
/// allocator, an uninterpreted per-type cost.
pub uninterp spec fn allocator_clone_cost<A: ?Sized>() -> int;

pub broadcast axiom fn axiom_allocator_max_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_max_cost::<A>() >= 0,
;

// (each cost of one call is at most the maximum, which is defined as an upper bound of all of
// them)
pub broadcast axiom fn axiom_allocator_allocate_cost<A: ?Sized>(a: &A, layout: Layout)
    ensures
        0 <= #[trigger] allocator_allocate_cost::<A>(a, layout) <= allocator_max_cost::<A>(),
;

pub broadcast axiom fn axiom_allocator_grow_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
)
    ensures
        0 <= #[trigger] allocator_grow_cost::<A>(a, ptr, old_layout, new_layout)
            <= allocator_max_cost::<A>(),
;

pub broadcast axiom fn axiom_allocator_grow_zeroed_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
)
    ensures
        0 <= #[trigger] allocator_grow_zeroed_cost::<A>(a, ptr, old_layout, new_layout)
            <= allocator_max_cost::<A>(),
;

pub broadcast axiom fn axiom_allocator_shrink_cost<A: ?Sized>(
    a: &A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
)
    ensures
        0 <= #[trigger] allocator_shrink_cost::<A>(a, ptr, old_layout, new_layout)
            <= allocator_max_cost::<A>(),
;

pub open spec fn clamp_cost(c: int, max: int) -> int {
    if c <= 0 {
        0
    } else if c <= max {
        c
    } else if max >= 0 {
        max
    } else {
        0
    }
}

/// A `BoundedAllocator`'s costs (clamped at 0, and cut down to its `max_cost`)
#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_max_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>()
    ensures
        #[trigger] allocator_max_cost::<A>() == clamp_cost(A::max_cost(), A::max_cost()),
;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_allocate_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>(a: &A, layout: Layout)
    ensures
        #[trigger] allocator_allocate_cost::<A>(a, layout) == clamp_cost(
            a.allocate_cost(layout),
            A::max_cost(),
        ),
;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_grow_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>(a: &A, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout)
    ensures
        #[trigger] allocator_grow_cost::<A>(a, ptr, old_layout, new_layout) == clamp_cost(
            a.grow_cost(ptr, old_layout, new_layout),
            A::max_cost(),
        ),
;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_grow_zeroed_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>(a: &A, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout)
    ensures
        #[trigger] allocator_grow_zeroed_cost::<A>(a, ptr, old_layout, new_layout) == clamp_cost(
            a.grow_zeroed_cost(ptr, old_layout, new_layout),
            A::max_cost(),
        ),
;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn axiom_bounded_allocator_shrink_cost<
    A: crate::alloc_check::BoundedAllocator + ?Sized,
>(a: &A, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout)
    ensures
        #[trigger] allocator_shrink_cost::<A>(a, ptr, old_layout, new_layout) == clamp_cost(
            a.shrink_cost(ptr, old_layout, new_layout),
            A::max_cost(),
        ),
;

// `&A` and `&mut A` forward every method to `A` (std 1.100 `core/src/alloc/mod.rs`). (For `&mut A`
// only the maximum is stated: a specification cannot dereference a `&&mut A` argument.)
pub broadcast axiom fn axiom_ref_allocator_max_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_max_cost::<&A>() == allocator_max_cost::<A>(),
;

pub broadcast axiom fn axiom_mut_ref_allocator_max_cost<A: ?Sized>()
    ensures
        #[trigger] allocator_max_cost::<&mut A>() == allocator_max_cost::<A>(),
;

pub broadcast axiom fn axiom_ref_allocator_allocate_cost<A: ?Sized>(a: &&A, layout: Layout)
    ensures
        #[trigger] allocator_allocate_cost::<&A>(a, layout) == allocator_allocate_cost::<A>(
            *a,
            layout,
        ),
;

pub broadcast axiom fn axiom_ref_allocator_grow_cost<A: ?Sized>(
    a: &&A,
    ptr: NonNull<u8>,
    old_layout: Layout,
    new_layout: Layout,
)
    ensures
        #[trigger] allocator_grow_cost::<&A>(a, ptr, old_layout, new_layout)
            == allocator_grow_cost::<A>(*a, ptr, old_layout, new_layout),
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
    axiom_spec_layout_size,
    axiom_spec_layout_align,
    axiom_allocator_max_cost,
    axiom_allocator_allocate_cost,
    axiom_allocator_grow_cost,
    axiom_allocator_grow_zeroed_cost,
    axiom_allocator_shrink_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_max_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_allocate_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_grow_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_grow_zeroed_cost,
    #[cfg(not(verus_verify_core))]
    axiom_bounded_allocator_shrink_cost,
    axiom_ref_allocator_max_cost,
    axiom_mut_ref_allocator_max_cost,
    axiom_ref_allocator_allocate_cost,
    axiom_ref_allocator_grow_cost,
    axiom_allocator_clone_cost,
    axiom_ref_allocator_clone_cost,
}

/// The allocator trait. -V alloc-check: `deallocate` allocates nothing (the drop rule relies on
/// this: dropping a container calls it), and the others cost what `allocator_allocate_cost`,
/// `allocator_grow_cost`, `allocator_grow_zeroed_cost` and `allocator_shrink_cost` say for the
/// allocator and the arguments. These bounds hold for the std allocators and for every
/// implementation that Verus checks, which `vstd::alloc_check::BoundedAllocator` requires. std's
/// default bodies of `allocate_zeroed`, `grow`, `grow_zeroed` and `shrink` call `allocate` or
/// `allocate_zeroed` once (with the new layout) and `deallocate` at most once, so they stay within
/// `allocate_cost` of the new layout, which is what `BoundedAllocator`'s defaults say.
#[verifier::external_trait_specification]
pub unsafe trait ExAllocator {
    type ExternalTraitSpecificationFor: core::alloc::Allocator;

    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_allocate_cost::<Self>(self, layout),
    ;

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_allocate_cost::<Self>(self, layout),
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
            allocator_grow_cost::<Self>(self, ptr, old_layout, new_layout),
    ;

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
        allocates
            allocator_grow_zeroed_cost::<Self>(self, ptr, old_layout, new_layout),
    ;

    unsafe fn shrink(&self, ptr: NonNull<u8>, old_layout: Layout, new_layout: Layout) -> Result<
        NonNull<[u8]>,
        AllocError,
    >
        allocates
            allocator_shrink_cost::<Self>(self, ptr, old_layout, new_layout),
    ;
}

} // verus!
// The std allocators: each method is one call to the allocator (`deallocate` frees memory and is
// not counted), i.e. their `max_cost` is 1 (`vstd::alloc_check::BoundedAllocator`); the
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
        #[trigger] allocator_max_cost::<std::alloc::System>() == 1,
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
        #[trigger] allocator_max_cost::<alloc::alloc::Global>() == 1,
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

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::allocator ](v: &Vec<T, A>) -> (r: &A)
    ensures
        *r == super::vec::spec_vec_allocator(v),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
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
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    opens_invariants none
    no_unwind
    allocates
        0,
;

/// `Box::new_in` allocates `Layout::new::<T>()` with the given allocator (or nothing for a
/// zero-sized `T`)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::new_in ](x: T, alloc: A) -> (b: Box<T, A>)
    ensures
        *b == x,
        spec_box_allocator(&b) == alloc,
        exists|r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>|
            crate::alloc_heap::allocator_heap()
                == #[trigger] crate::alloc_heap::allocator_allocate_heap_in::<A>(
                crate::alloc_heap::old_allocator_heap(),
                &alloc,
                spec_array_layout::<T>(1),
                r,
            ),
    allocates
        crate::alloc_heap::allocator_allocate_cost_in::<A>(
            crate::alloc_heap::old_allocator_heap(),
            &alloc,
            spec_array_layout::<T>(1),
        ),
;

/// `Box::take` moves the value out and keeps the allocation (with uninitialized contents)
pub assume_specification<T, A: Allocator>[ Box::<T, A>::take ](boxed: Box<T, A>) -> (r: (
    T,
    Box<core::mem::MaybeUninit<T>, A>,
))
    ensures
        r.0 == *boxed,
        spec_box_allocator(&r.1) == spec_box_allocator(&boxed),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
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
            0
        } else {
            allocator_allocate_cost::<A>(&spec_box_allocator(&this), spec_array_layout::<U>(1))
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
        allocator_max_cost::<A>() + call_allocates(f, (&*this,)),
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
        allocator_max_cost::<A>() + call_allocates(f, (&*this,)),
;

} // verus!
