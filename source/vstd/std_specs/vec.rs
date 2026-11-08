use super::super::prelude::*;
use super::iter::{FromIteratorSpecImpl, IteratorSpec};
use verus_builtin::*;

use super::super::slice::SliceIndexSpec;
use super::clone::{lemma_seq_clone_allocates_zero, seq_clone_allocates};
use super::core::IndexSpec;
use super::rust_1_100::{
    allocator_allocate_cost, allocator_clone_cost, allocator_grow_cost, allocator_max_cost,
    spec_array_layout,
};
use alloc::collections::TryReserveError;
use alloc::vec::{IntoIter, Vec};
use core::alloc::Allocator;
use core::clone::Clone;
use core::marker::PhantomData;
use core::ops::Index;
use core::option::Option;
use core::option::Option::None;
use core::slice::SliceIndex;

use super::iter::{iter_next_back_cost, iter_next_cost};
use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVec<T, A: Allocator>(Vec<T, A>);

pub trait VecAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T, A: Allocator> VecAdditionalSpecFns<T> for Vec<T, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryReserveError(alloc::collections::TryReserveError);

// We still have a special case for Vec::index on usize.
// The general Vec::index case now goes through the Index trait,
// but this special case is still here because it's more direct and efficient in its SMT encoding,
// and Vec::index on usize is very common.
//
// So this is a bit of a hack, but we just manually redirect
// `vec[i]` to this function here from rust_to_vir_expr.
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index")]
pub fn vec_index<T, A: Allocator>(vec: &Vec<T, A>, i: usize) -> (element: &T)
    requires
        i < vec.view().len(),
    ensures
        *element == vec.view().index(i as int),
    no_unwind
    allocates 0
{
    &vec[i]
}

/// This is a specification for the indexing operator `vec[i]` when it expands to the `IndexMut` trait
#[doc(hidden)]
#[verifier::external_body]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::std_specs::vec::vec_index_mut")]
pub fn vec_index_mut<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: &mut T)
    requires
        i < vec.view().len(),
    ensures
        *element == old(vec)@.index(i as int),
        final(vec)@ == old(vec)@.update(i as int, *final(element)),

        *final(element) == final(vec).view().index(i as int),
    no_unwind
    allocates 0
{
    &mut vec[i]
}

////// Len (with autospec)
pub uninterp spec fn spec_vec_len<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &Vec<T, A>)
    ensures
        #[trigger] spec_vec_len(v) == v@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_vec_len)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::len ](vec: &Vec<T, A>) -> (len: usize)
    ensures
        len == spec_vec_len(vec),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    no_unwind
    allocates deallocates_when(0int, false)
;

////// Capacity (for allocation checking, -V alloc-check)
// Only what std documents as guaranteed (alloc/src/vec/mod.rs, "Guarantees" and the method docs)
// is stated here; `allocates` bounds are upper bounds on allocator calls (allocate or grow).
pub uninterp spec fn spec_vec_capacity<T, A: Allocator>(v: &Vec<T, A>) -> usize;

// A Vec's capacity is at least its length, and is usize::MAX for zero-sized elements.
pub broadcast proof fn axiom_spec_capacity<T, A: Allocator>(v: &Vec<T, A>)
    ensures
        #[trigger] spec_vec_capacity(v) >= v@.len(),
        crate::layout::size_of::<T>() == 0 ==> spec_vec_capacity(v) == usize::MAX,
{
    admit();
}

/// -V alloc-check: the allocator of a vector and the pointer to its buffer: with its capacity,
/// these are the arguments of the allocator call that growing it makes
pub uninterp spec fn spec_vec_allocator<T, A: Allocator>(v: &Vec<T, A>) -> A;

pub uninterp spec fn spec_vec_ptr<T, A: Allocator>(v: &Vec<T, A>) -> core::ptr::NonNull<u8>;

/// std 1.100 `alloc/src/raw_vec/mod.rs`, `min_non_zero_cap`: the smallest capacity a vector
/// with elements of `elem_size` bytes grows to
pub open spec fn vec_min_non_zero_cap(elem_size: nat) -> int {
    if elem_size == 1 {
        8
    } else if elem_size <= 1024 {
        4
    } else {
        1
    }
}

/// std 1.100 `RawVecInner::grow_amortized`: the capacity that a vector with capacity `cap` and
/// length `len` grows to when it needs room for `additional` more elements (`reserve`, `push`,
/// `insert`, `append`, `extend_from_slice`, `resize`)
pub open spec fn vec_amortized_cap<T>(cap: int, len: int, additional: int) -> int {
    let c = if 2 * cap >= len + additional {
        2 * cap
    } else {
        len + additional
    };
    let m = vec_min_non_zero_cap(crate::layout::size_of::<T>());
    if m >= c {
        m
    } else {
        c
    }
}

/// The allocations of growing `v` to capacity `new_cap`: std 1.100 `RawVecInner::finish_grow`
/// calls `allocate` with the new layout if the vector has no buffer yet, and otherwise `grow`
/// with its pointer, its old layout and the new one
pub open spec fn vec_grow_cost<T, A: Allocator>(v: &Vec<T, A>, new_cap: int) -> int {
    if spec_vec_capacity(v) == 0 {
        allocator_allocate_cost::<A>(&spec_vec_allocator(v), spec_array_layout::<T>(new_cap as nat))
    } else {
        allocator_grow_cost::<A>(
            &spec_vec_allocator(v),
            spec_vec_ptr(v),
            spec_array_layout::<T>(spec_vec_capacity(v) as nat),
            spec_array_layout::<T>(new_cap as nat),
        )
    }
}

/// `vec_grow_cost` in the allocator heap `h` (for an allocator with a state, the cost at its state)
pub open spec fn vec_grow_cost_in<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    new_cap: int,
) -> int {
    if spec_vec_capacity(v) == 0 {
        crate::alloc_heap::allocator_allocate_cost_in::<A>(
            h,
            &spec_vec_allocator(v),
            spec_array_layout::<T>(new_cap as nat),
        )
    } else {
        crate::alloc_heap::allocator_grow_cost_in::<A>(
            h,
            &spec_vec_allocator(v),
            spec_vec_ptr(v),
            spec_array_layout::<T>(spec_vec_capacity(v) as nat),
            spec_array_layout::<T>(new_cap as nat),
        )
    }
}

/// The allocator heap after growing `v` to capacity `new_cap`, where the allocator returned `r`
pub open spec fn vec_grow_heap_in<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    new_cap: int,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> crate::alloc_heap::AllocHeap {
    if spec_vec_capacity(v) == 0 {
        crate::alloc_heap::allocator_allocate_heap_in::<A>(
            h,
            &spec_vec_allocator(v),
            spec_array_layout::<T>(new_cap as nat),
            r,
        )
    } else {
        crate::alloc_heap::allocator_grow_heap_in::<A>(
            h,
            &spec_vec_allocator(v),
            spec_vec_ptr(v),
            spec_array_layout::<T>(spec_vec_capacity(v) as nat),
            spec_array_layout::<T>(new_cap as nat),
            r,
        )
    }
}

/// `vec_reserve_cost` in the allocator heap `h`
pub open spec fn vec_reserve_cost_in<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    additional: int,
) -> int {
    if spec_vec_capacity(v) - v@.len() >= additional {
        0
    } else {
        vec_grow_cost_in(
            h,
            v,
            vec_amortized_cap::<T>(spec_vec_capacity(v) as int, v@.len() as int, additional),
        )
    }
}

/// The allocator heap after making room in `v` for `additional` more elements, where the
/// allocator (if it was called) returned `r`
pub open spec fn vec_reserve_heap_in<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    additional: int,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> crate::alloc_heap::AllocHeap {
    if spec_vec_capacity(v) - v@.len() >= additional {
        h
    } else {
        vec_grow_heap_in(
            h,
            v,
            vec_amortized_cap::<T>(spec_vec_capacity(v) as int, v@.len() as int, additional),
            r,
        )
    }
}

/// `h2` is the allocator heap after making room in `v` (in heap `h`) for `additional` more
/// elements, for some result of the allocator call
pub open spec fn vec_reserve_heap<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    h2: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    additional: int,
) -> bool {
    exists|r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>|
        h2 == #[trigger] vec_reserve_heap_in(h, v, additional, r)
}

/// `h2` is the allocator heap after growing `v` (in heap `h`) to capacity `new_cap`, for some
/// result of the allocator call
pub open spec fn vec_grow_heap<T, A: Allocator>(
    h: crate::alloc_heap::AllocHeap,
    h2: crate::alloc_heap::AllocHeap,
    v: &Vec<T, A>,
    new_cap: int,
) -> bool {
    exists|r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>|
        h2 == #[trigger] vec_grow_heap_in(h, v, new_cap, r)
}

/// The allocations of making room in `v` for `additional` more elements (`reserve`)
pub open spec fn vec_reserve_cost<T, A: Allocator>(v: &Vec<T, A>, additional: int) -> int {
    if spec_vec_capacity(v) - v@.len() >= additional {
        0
    } else {
        vec_grow_cost(v, vec_amortized_cap::<T>(spec_vec_capacity(v) as int, v@.len() as int, additional))
    }
}

/// -V alloc-check, `#[verifier::fip]`: making room in `v` for `additional` more elements
/// reallocates its existing buffer (`grow`, which frees the old block); growing a vector that has
/// no buffer yet only allocates
pub open spec fn vec_regrows<T, A: Allocator>(v: &Vec<T, A>, additional: int) -> bool {
    crate::layout::size_of::<T>() > 0 && spec_vec_capacity(v) > 0 && spec_vec_capacity(v)
        - v@.len() < additional
}

/// After `v` made room for `additional` more elements (if it had to grow, and grew), its capacity
/// is the one that std's growth policy picks
pub open spec fn vec_reserved<T, A: Allocator>(old_v: &Vec<T, A>, new_v: &Vec<T, A>, additional: int) -> bool {
    crate::layout::size_of::<T>() > 0 && spec_vec_capacity(old_v) - old_v@.len() < additional
        ==> spec_vec_capacity(new_v) == vec_amortized_cap::<T>(
        spec_vec_capacity(old_v) as int,
        old_v@.len() as int,
        additional,
    )
}

#[verifier::when_used_as_spec(spec_vec_capacity)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::capacity ](vec: &Vec<T, A>) -> (capacity: usize)
    ensures
        capacity == spec_vec_capacity(vec),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    no_unwind
    allocates deallocates_when(0int, false)
;

////// Other functions
pub assume_specification<T>[ Vec::<T>::new ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
        crate::layout::size_of::<T>() > 0 ==> spec_vec_capacity(&v) == 0,
    allocates deallocates_when(0int, false)
;

pub assume_specification<T>[ <Vec<T> as core::default::Default>::default ]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
        crate::layout::size_of::<T>() > 0 ==> spec_vec_capacity(&v) == 0,
    allocates 0
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::new_in ](alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
        spec_vec_allocator(&v) == alloc,
        crate::layout::size_of::<T>() > 0 ==> spec_vec_capacity(&v) == 0,
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, false)
;

pub assume_specification<T>[ Vec::<T>::with_capacity ](capacity: usize) -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty(),
        spec_vec_capacity(&v) >= capacity,
    allocates deallocates_when(if capacity == 0 { 0int } else { 1int }, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::with_capacity_in ](capacity: usize, alloc: A) -> (v: Vec<T, A>)
    ensures
        v@ == Seq::<T>::empty(),
        spec_vec_capacity(&v) >= capacity,
        spec_vec_allocator(&v) == alloc,
        capacity == 0 || crate::layout::size_of::<T>() == 0 ==> crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
        capacity > 0 && crate::layout::size_of::<T>() > 0 ==> exists|r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>|
            crate::alloc_heap::allocator_heap() == #[trigger] crate::alloc_heap::allocator_allocate_heap_in::<A>(crate::alloc_heap::old_allocator_heap(), &alloc, spec_array_layout::<T>(capacity as nat), r),
    // `RawVecInner::try_allocate_in`: one `allocate` of the array layout, unless it is empty
    allocates deallocates_when(if capacity == 0 || crate::layout::size_of::<T>() == 0 {
        0int
    } else {
        crate::alloc_heap::allocator_allocate_cost_in::<A>(crate::alloc_heap::old_allocator_heap(), &alloc, spec_array_layout::<T>(capacity as nat))
    }, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@,
        spec_vec_capacity(final(vec)) >= old(vec)@.len() + additional,
        spec_vec_capacity(old(vec)) - old(vec)@.len() >= additional
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        vec_reserved(old(vec), final(vec), additional as int),
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), additional as int),
    allocates deallocates_when(vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), additional as int), vec_regrows(old(vec), additional as int))
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::try_reserve ](
    vec: &mut Vec<T, A>,
    additional: usize,
) -> (result: Result<(), TryReserveError>)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@,
        result is Ok ==> spec_vec_capacity(final(vec)) >= old(vec)@.len() + additional,
        spec_vec_capacity(old(vec)) - old(vec)@.len() >= additional
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        result is Ok ==> vec_reserved(old(vec), final(vec), additional as int),
        // (std 1.100 `RawVecInner::grow_amortized` fails with `CapacityOverflow` before calling
        // the allocator when the new capacity overflows, leaving the heap as it was)
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), additional as int)
            || (result is Err && crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap()),
    allocates deallocates_when(vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), additional as int), vec_regrows(old(vec), additional as int))
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::try_reserve_exact ](
    vec: &mut Vec<T, A>,
    additional: usize,
) -> (result: Result<(), TryReserveError>)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@,
        result is Ok ==> spec_vec_capacity(final(vec)) >= old(vec)@.len() + additional,
        spec_vec_capacity(old(vec)) - old(vec)@.len() >= additional
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        // `RawVecInner::grow_exact`: exactly the room asked for
        result is Ok && crate::layout::size_of::<T>() > 0 && spec_vec_capacity(old(vec))
            - old(vec)@.len() < additional ==> spec_vec_capacity(final(vec)) == old(vec)@.len()
            + additional,
        spec_vec_capacity(old(vec)) - old(vec)@.len() >= additional ==> crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
        // (`RawVecInner::grow_exact` fails with `CapacityOverflow` before calling the allocator
        // when the new capacity overflows, leaving the heap as it was)
        spec_vec_capacity(old(vec)) - old(vec)@.len() < additional ==> (vec_grow_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), old(vec)@.len() + additional)
            || (result is Err && crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap())),
    allocates deallocates_when(if spec_vec_capacity(old(vec)) - old(vec)@.len() >= additional {
        0int
    } else {
        vec_grow_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), old(vec)@.len() + additional)
    }, vec_regrows(old(vec), additional as int))
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::push ](vec: &mut Vec<T, A>, value: T)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@.push(value),
        old(vec)@.len() < spec_vec_capacity(old(vec))
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        vec_reserved(old(vec), final(vec), 1),
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), 1),
    // `RawVec::grow_one`, i.e. `grow_amortized(len, 1)` with `len == capacity`
    allocates deallocates_when(vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), 1), vec_regrows(old(vec), 1))
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::pop ](vec: &mut Vec<T, A>) -> (value:
    Option<T>)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        old(vec)@.len() > 0 ==> value == Some(old(vec)@[old(vec)@.len() - 1])
            && final(vec)@ == old(vec)@[..old(vec)@.len() - 1],
        old(vec)@.len() == 0 ==> value == None::<T> && final(vec)@ == old(vec)@,
        spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::append ](
    vec: &mut Vec<T, A>,
    other: &mut Vec<T, A>,
)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@ + old(other)@,
        final(other)@ == Seq::<T>::empty(),
        spec_vec_capacity(old(vec)) - old(vec)@.len() >= old(other)@.len()
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        vec_reserved(old(vec), final(vec), old(other)@.len() as int),
        spec_vec_allocator(final(other)) == spec_vec_allocator(old(other)),
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), old(other)@.len() as int),
    // `reserve(other.len())`
    allocates deallocates_when(vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), old(other)@.len() as int), vec_regrows(old(vec), old(other)@.len() as int))
;

pub assume_specification<T: core::clone::Clone, A: Allocator>[ Vec::<T, A>::extend_from_slice ](
    vec: &mut Vec<T, A>,
    other: &[T],
)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@.len() == old(vec)@.len() + other@.len(),
        forall|i: int|
            #![trigger final(vec)@[i]]
            0 <= i < final(vec)@.len() ==> if i < old(vec)@.len() {
                final(vec)@[i] == old(vec)@[i]
            } else {
                cloned::<T>(other@[i - old(vec)@.len()], final(vec)@[i])
            },
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), other@.len() as int),
    // `reserve(other.len())` (at most one growth), then one `T::clone` per element
    allocates vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), other@.len() as int) + seq_clone_allocates(other@, other@.len())
;

impl<T: Sized, I: SliceIndex<[T]>, A: Allocator> super::core::IndexSpecImpl<I> for Vec<T, A> {
    open spec fn index_req(&self, index: &I) -> bool {
        forall|s: &[T]| #[trigger] s@ == self@ ==> index.in_bounds(s)
    }
}

pub assume_specification<T, I: SliceIndex<[T]>, A: Allocator>[Vec::<T, A>::index](
    vec: &Vec<T, A>,
    i: I,
) -> (r: &<Vec<T, A> as Index<I>>::Output)
    ensures
        exists|s: &[T]| #[trigger] s@ == vec@ && call_ensures(<I as SliceIndex<[T]>>::index, (i, s), r),
    // SliceIndex is sealed: only std's (non-allocating) impls exist
    allocates 0
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::swap_remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.update(i as int, old(vec)@.last()).drop_last(),
        spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::insert ](
    vec: &mut Vec<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(vec).len(),
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@.insert(i as int, element),
        old(vec)@.len() < spec_vec_capacity(old(vec))
            ==> spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        vec_reserved(old(vec), final(vec), 1),
        vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), 1),
    // `RawVec::grow_one`, i.e. `grow_amortized(len, 1)` with `len == capacity`
    allocates deallocates_when(vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), 1), vec_regrows(old(vec), 1))
;

pub assume_specification<T, A: Allocator> [ <Vec<T, A>>::is_empty ](
    v: &Vec<T, A>,
) -> (res: bool)
    ensures res <==> v@.len() == 0,
    opens_invariants none
    no_unwind
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::remove ](
    vec: &mut Vec<T, A>,
    i: usize,
) -> (element: T)
    requires
        i < old(vec).len(),
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        element == old(vec)[i as int],
        final(vec)@ == old(vec)@.remove(i as int),
        spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::clear ](vec: &mut Vec<T, A>)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec).view() == Seq::<T>::empty(),
        spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, old(vec)@.len() > 0 && crate::alloc_check::drop_may_deallocate::<T>())
;

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_slice ](vec: &Vec<T, A>) -> (slice: &[T])
    ensures
        slice@ == vec@,
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    opens_invariants none
    no_unwind
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::convert::AsRef<[T]>>::as_ref ](
    vec: &Vec<T, A>,
) -> (slice: &[T])
    ensures
        slice@ == vec@,
    opens_invariants none
    no_unwind
    allocates 0
;

#[doc(hidden)]
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::as_mut_slice ](vec: &mut Vec<T, A>) -> (slice: &mut [T])
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    opens_invariants none
    no_unwind
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::Deref>::deref ](
    vec: &Vec<T, A>,
) -> (slice: &[T])
    ensures
        slice@ == vec@,
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator>[ <Vec<T, A> as core::ops::DerefMut>::deref_mut ](
    vec: &mut Vec<T, A>,
) -> (slice: &mut [T])
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        slice@ == old(vec)@,
        final(slice)@ == final(vec)@,
    allocates deallocates_when(0int, false)
;

pub assume_specification<T, A: Allocator + core::clone::Clone>[ Vec::<T, A>::split_off ](
    vec: &mut Vec<T, A>,
    at: usize,
) -> (return_value: Vec<T, A>)
    requires
        at <= old(vec)@.len(),
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        final(vec)@ == old(vec)@[..at],
        return_value@ == old(vec)@[at..],
    // the returned vector's buffer, and a clone of the allocator
    allocates allocator_max_cost::<A>() + allocator_clone_cost::<A>()
;

pub open spec fn vec_clone_trigger<T, A: Allocator>(v1: Vec<T, A>, v2: Vec<T, A>) -> bool {
    true
}

// rustc 1.99.1: `<[T]>::to_vec_in`, i.e. `with_capacity_in(len)` and one `T::clone` per element
// and a clone of the allocator
pub assume_specification<T: Clone, A: Allocator + Clone>[ <Vec<T, A> as Clone>::clone ](
    vec: &Vec<T, A>,
) -> (res: Vec<T, A>)
    ensures
        res.len() == vec.len(),
        forall|i| #![all_triggers] 0 <= i < vec.len() ==> cloned::<T>(vec[i], res[i]),
        vec_clone_trigger(*vec, res),
        vec@ =~= res@ ==> vec@ == res@,
    allocates (if vec@.len() == 0 { 0int } else { allocator_max_cost::<A>() }) + seq_clone_allocates(vec@, vec@.len()) + allocator_clone_cost::<A>()
;

pub broadcast proof fn vec_clone_deep_view_proof<T: DeepView, A: Allocator>(
    v1: Vec<T, A>,
    v2: Vec<T, A>,
)
    requires
        #[trigger] vec_clone_trigger(v1, v2),
        v1.deep_view() =~= v2.deep_view(),
    ensures
        v1.deep_view() == v2.deep_view(),
{
}

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::truncate ](vec: &mut Vec<T, A>, len: usize)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        len <= old(vec).len() ==> final(vec)@ == old(vec)@[..len],
        len > old(vec).len() ==> final(vec)@ == old(vec)@,
        spec_vec_capacity(final(vec)) == spec_vec_capacity(old(vec)),
        crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
    allocates deallocates_when(0int, len < old(vec)@.len() && crate::alloc_check::drop_may_deallocate::<T>())
;

pub assume_specification<T: Clone, A: Allocator>[ Vec::<T, A>::resize ](
    vec: &mut Vec<T, A>,
    len: usize,
    value: T,
)
    ensures
        spec_vec_allocator(final(vec)) == spec_vec_allocator(old(vec)),
        len <= old(vec).len() ==> final(vec)@ == old(vec)@[..len],
        len > old(vec).len() ==> {
            &&& final(vec)@.len() == len
            &&& final(vec)@[..old(vec).len()] == old(vec)@
            &&& forall|i| #![all_triggers] old(vec).len() <= i < len ==> cloned::<T>(value, final(vec)@[i])
        },
        len <= old(vec).len() ==> crate::alloc_heap::allocator_heap() == crate::alloc_heap::old_allocator_heap(),
        len > old(vec).len() ==> vec_reserve_heap(crate::alloc_heap::old_allocator_heap(), crate::alloc_heap::allocator_heap(), old(vec), len - old(vec)@.len()),
    // `extend_with(len - old_len, value)`: at most one growth, at most one `T::clone` per new element
    allocates if len <= old(vec)@.len() {
        0int
    } else {
        vec_reserve_cost_in(crate::alloc_heap::old_allocator_heap(), old(vec), len - old(vec)@.len())
            + (len - old(vec)@.len()) * call_allocates(T::clone, (&value,))
    }
;

pub broadcast proof fn axiom_vec_index_decreases<A>(v: Vec<A>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] (decreases_to!(v => v[i])),
{
    admit();
}

pub assume_specification<T: PartialEq<U>, U, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialEq<Vec<U, A2>>>::eq ](
    x: &Vec<T, A1>,
    y: &Vec<U, A2>,
) -> bool
    allocates super::slice::seq_eq_allocates(x@, y@)
;

impl<T: super::cmp::PartialEqSpec<U>, U, A1: Allocator, A2: Allocator> super::cmp::PartialEqSpecImpl<Vec<U, A2>> for Vec<T, A1> {
    open spec fn obeys_eq_spec() -> bool {
        T::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &Vec<U, A2>) -> bool {
        &&& self.len() == other.len()
        &&& forall|i: int| #![auto] 0 <= i < self.len() ==> self[i].eq_spec(&other[i])
    }
}

// The `into_iter` method of a `Vec` returns an iterator of type `IntoIter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExIntoIter<T, A: Allocator>(IntoIter<T, A>);

// To allow reasoning about the "contents" of the Vec iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original vec.
pub uninterp spec fn into_iter_elts<T, A: Allocator>(i: IntoIter<T, A>) -> Seq<T>;

pub broadcast axiom fn axiom_next_cost_vec_into_iter<T, A: Allocator>(i: &IntoIter<T, A>)
    ensures
        #[trigger] iter_next_cost(i) == 0,
;

/// std's other `Iterator` methods for this type (`nth`, `find`, `try_fold`, ...) allocate nothing
pub broadcast axiom fn axiom_aux_alloc_free_vec_into_iter<T, A: Allocator>()
    ensures
        #[trigger] super::iter::iter_aux_alloc_free::<IntoIter<T, A>>(),
;

pub broadcast axiom fn axiom_next_back_cost_vec_into_iter<T, A: Allocator>(i: &IntoIter<T, A>)
    ensures
        #[trigger] iter_next_back_cost(i) == 0,
;

impl <T, A: Allocator> super::iter::IteratorSpecImpl for IntoIter<T, A> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;
    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        Seq::new(IteratorSpec::remaining(self).len(), |i: int| true)
    }
    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

impl <T, A: Allocator> super::iter::DoubleEndedIteratorSpecImpl for IntoIter<T, A> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = into_iter_elts(*self).len();
        if 0 <= index < len {
            Some(into_iter_elts(*self)[len - index - 1])
        } else {
            None
        }
    }
}

// This is used by `vec![x; n]`
pub assume_specification<T: Clone>[ alloc::vec::from_elem ](elem: T, n: usize) -> (v: Vec<T>)
    ensures
        v.len() == n,
        forall |i| 0 <= i < n ==> cloned(elem, #[trigger] v@[i])
    // `with_capacity(n)` (one buffer), then at most one `T::clone` per element
    allocates (if n == 0 { 0int } else { 1int }) + n * call_allocates(T::clone, (&elem,));

pub assume_specification<T, A: Allocator>[ Vec::<T, A>::into_iter ](vec: Vec<T, A>) -> (iter: <Vec<
    T,
    A,
> as core::iter::IntoIterator>::IntoIter)
    ensures
        IteratorSpec::remaining(&iter) == vec@,
        into_iter_elts(iter) == IteratorSpec::remaining(&iter),
        IteratorSpec::decrease(&iter) is Some,
    allocates 0
;

pub assume_specification<'a, T, A: Allocator> [<&'a Vec<T, A> as core::iter::IntoIterator>::into_iter] (vec: &'a Vec<T, A>) ->
    (iter: <&'a Vec<T, A> as core::iter::IntoIterator>::IntoIter)
    ensures
        IteratorSpec::remaining(&iter) == vec@.as_ref(),
        super::slice::into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,    allocates 0
;

impl<T>  FromIteratorSpecImpl<T> for Vec<T> {
    open spec fn from_iter_ensures(remaining: Seq<T>, produces: Seq<bool>, s: Self) -> bool {
        &&& produces.len() == remaining.len()
        &&& produces.all(|p: bool| p)
        &&& remaining == s@
    }
}

pub broadcast proof fn lemma_vec_obeys_eq_spec<T: PartialEq>()
    requires
        super::super::laws_eq::obeys_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_eq::<Vec<T>>(),
{
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_vec_obeys_view_eq<T: PartialEq + View>()
    requires
        super::super::laws_eq::obeys_concrete_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_view_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_concrete_eq);
    reveal(super::super::laws_eq::obeys_view_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x@ == y@);
}

pub broadcast proof fn lemma_vec_obeys_deep_eq<T: PartialEq + DeepView>()
    requires
        super::super::laws_eq::obeys_deep_eq::<T>(),
    ensures
        #[trigger] super::super::laws_eq::obeys_deep_eq::<Vec<T>>(),
{
    use super::cmp::PartialEqSpec;
    broadcast use {axiom_spec_len, super::super::seq::group_seq_lemmas};
    reveal(super::super::laws_eq::obeys_eq_spec_properties);
    reveal(super::super::laws_eq::obeys_deep_eq);
    assert(forall|x: Vec<T>, y: Vec<T>| x.eq_spec(&y) ==> x.deep_view() == y.deep_view());
    assert forall|x: Vec<T>, y: Vec<T>| x.deep_view() == y.deep_view() implies x.eq_spec(&y) by {
        assert(x.deep_view().len() == y.deep_view().len());
        assert forall|i: int| #![auto] 0 <= i < x.len() implies x[i].eq_spec(&y[i]) by {
            assert(x.deep_view()[i] == y.deep_view()[i]);
        }
    }
}

pub broadcast axiom fn axiom_vec_has_resolved<T>(vec: Vec<T>, i: int)
    ensures
        0 <= i < vec.len() ==> #[trigger] has_resolved::<Vec<T>>(vec) ==> has_resolved(
            #[trigger] vec@[i],
        ),
;

pub broadcast axiom fn axiom_vec_decreases_to_view<T>(v: Vec<T>)
    ensures
        #[trigger] (decreases_to!(v => v@));

pub broadcast group group_vec_axioms {
    axiom_next_cost_vec_into_iter,
    axiom_aux_alloc_free_vec_into_iter,
    axiom_next_back_cost_vec_into_iter,
    axiom_spec_len,
    axiom_spec_capacity,
    lemma_seq_clone_allocates_zero,
    axiom_vec_index_decreases,
    vec_clone_deep_view_proof,
    axiom_vec_has_resolved,
    axiom_vec_decreases_to_view,
}

pub axiom fn tracked_borrow_slice<T, A: Allocator>(tracked vec: &Vec<T, A>) -> (tracked t: &[T])
    ensures t@ == vec@;

pub axiom fn tracked_borrow_mut_slice<T, A: Allocator>(tracked vec: &mut Vec<T, A>) -> (tracked t: &mut [T])
    ensures
        (*t)@ == old(vec)@,
        (*t).len() == final(t).len(),
        final(vec)@ == final(t)@;

} // verus!
