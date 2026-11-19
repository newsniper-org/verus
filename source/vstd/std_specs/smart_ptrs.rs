use super::super::prelude::*;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

// TODO
// (std 1.100 `alloc/src/slice.rs`: `Vec::from_raw_parts_in` on the box's buffer and allocator:
// it allocates, frees and drops nothing)
#[verifier::alloc_check_skip_drops]
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
    allocates
        0int,
    deallocates
        0,
;

// std 1.100 `alloc/src/boxed/convert.rs`: `Box::clone_from_ref`, which allocates once (nothing
// for a zero-sized layout) and clones each element into place (`CloneToUninit` for `[T]`, bitwise
// for `TrivialClone` types). On a normal return it drops no `T` (its guards act only on
// unwinding), and it deallocates only if a `clone` does. (std's `fn from(slice: &[T])` takes a
// slice of any lifetime, not only the impl's `'a`.)
#[verifier::alloc_check_skip_drops]
pub assume_specification<'a, T: Clone>[ <Box<[T]> as core::convert::From<&'a [T]>>::from ](
    slice: &[T],
) -> (res: Box<[T]>)
    ensures
        res@.len() == slice@.len(),
        forall|i| #![all_triggers] 0 <= i < slice@.len() ==> cloned::<T>(slice@[i], res@[i]),
        slice@ =~= res@ ==> slice@ == res@,
    allocates
        (if slice@.len() == 0 {
            0int
        } else {
            1int
        }) + super::clone::seq_clone_allocates(slice@, slice@.len()),
    deallocates
        deallocates_when(
            super::clone::seq_clone_deallocations(slice@, slice@.len()),
            !super::super::alloc_check::clone_is_fip::<T>(),
        ),
;

pub assume_specification<T>[ Box::<T>::new ](t: T) -> (v: Box<T>)
    ensures
        *v == t,
    allocates
        1int,
    deallocates
        0,
;

pub assume_specification<T: core::default::Default>[ <Box<
    T,
> as core::default::Default>::default ]() -> (res: Box<T>)
    ensures
        T::default.ensures((), *res),
    allocates
        1 + call_allocations(T::default, ()),
;

pub assume_specification<T>[ Rc::<T>::new ](t: T) -> (v: Rc<T>)
    ensures
        *v == t,
    allocates
        1,
;

pub assume_specification<T: core::default::Default>[ <Rc<
    T,
> as core::default::Default>::default ]() -> (res: Rc<T>)
    ensures
        T::default.ensures((), *res),
    allocates
        1 + call_allocations(T::default, ()),
;

pub assume_specification<T>[ Arc::<T>::new ](t: T) -> (v: Arc<T>)
    ensures
        *v == t,
    allocates
        1,
;

pub assume_specification<T: core::default::Default>[ <Arc<
    T,
> as core::default::Default>::default ]() -> (res: Arc<T>)
    ensures
        T::default.ensures((), *res),
    allocates
        1 + call_allocations(T::default, ()),
;

pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
    allocates
        1 + call_allocations(T::clone, (&**b,)),
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::try_unwrap ](v: Rc<T, A>) -> (result: Result<
    T,
    Rc<T, A>,
>)
    ensures
        match result {
            Ok(t) => t == *v,
            Err(e) => e == v,
        },
    allocates
        0,
;

pub assume_specification<T, A: Allocator>[ Rc::<T, A>::into_inner ](v: Rc<T, A>) -> (result: Option<
    T,
>)
    ensures
        result matches Some(t) ==> t == *v,
    allocates
        0,
;

// Cloning an `Rc`/`Arc` increments its reference count and clones its allocator (the runtime's)
#[cfg(not(verus_verify_core))]
pub assume_specification<T: ?Sized, A: core::alloc::AllocatorClone>[ <Rc<T, A> as Clone>::clone ](
    r: &Rc<T, A>,
) -> (res: Rc<T, A>)
    ensures
        res == *r,
    allocates
        0,
;

#[cfg(not(verus_verify_core))]
pub assume_specification<T: ?Sized, A: core::alloc::AllocatorClone>[ <Arc<T, A> as Clone>::clone ](
    r: &Arc<T, A>,
) -> (res: Arc<T, A>)
    ensures
        res == *r,
    allocates
        0,
;

} // verus!
