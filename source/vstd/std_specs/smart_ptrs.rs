use super::super::prelude::*;

use super::rust_1_100::{allocator_allocate_cost, allocator_clone_cost};
use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::alloc::Allocator;

verus! {

// TODO
pub assume_specification<T, A: Allocator>[ <[T]>::into_vec ](b: Box<[T], A>) -> (v: Vec<T, A>)
    ensures
        v@ == b@,
    allocates
        0,
;

pub assume_specification<T>[ Box::<T>::new ](t: T) -> (v: Box<T>)
    ensures
        *v == t,
    allocates
        1,
;

pub assume_specification<T: core::default::Default>[ <Box<
    T,
> as core::default::Default>::default ]() -> (res: Box<T>)
    ensures
        T::default.ensures((), *res),
    allocates
        1 + call_allocates(T::default, ()),
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
        1 + call_allocates(T::default, ()),
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
        1 + call_allocates(T::default, ()),
;

pub assume_specification<T: Clone, A: Allocator + Clone>[ <Box<T, A> as Clone>::clone ](
    b: &Box<T, A>,
) -> (res: Box<T, A>)
    ensures
        cloned::<T>(**b, *res),
    allocates
        allocator_allocate_cost::<A>() + call_allocates(T::clone, (&**b,)) + allocator_clone_cost::<
            A,
        >(),
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

// Cloning an `Rc`/`Arc` increments its reference count and clones its allocator
#[cfg(not(verus_verify_core))]
pub assume_specification<T: ?Sized, A: core::alloc::AllocatorClone>[ <Rc<T, A> as Clone>::clone ](
    r: &Rc<T, A>,
) -> (res: Rc<T, A>)
    ensures
        res == *r,
    allocates
        allocator_clone_cost::<A>(),
;

#[cfg(not(verus_verify_core))]
pub assume_specification<T: ?Sized, A: core::alloc::AllocatorClone>[ <Arc<T, A> as Clone>::clone ](
    r: &Arc<T, A>,
) -> (res: Arc<T, A>)
    ensures
        res == *r,
    allocates
        allocator_clone_cost::<A>(),
;

} // verus!
