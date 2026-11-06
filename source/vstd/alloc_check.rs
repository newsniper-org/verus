//! Support for checking `allocates` bounds of exec functions (`-V alloc-check`).
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// Types whose drop glue performs no allocation.
///
/// With `-V alloc-check`, every `Drop::drop` that a checked function may run must be bounded by
/// `allocates 0`. A generic function that may drop a value of a type parameter `T` therefore needs
/// the bound `T: AllocFreeDrop` (or `T: Copy`). An `unsafe impl AllocFreeDrop for X` is only
/// accepted under `-V alloc-check` when dropping an `X` cannot allocate, and every impl in the
/// program must be one that Verus checks.
///
/// The trait is `unsafe` because code that Verus does not see (for example, an unverified client
/// of a library verified with `-V check-api-safety`) could otherwise implement it for a type whose
/// drop allocates, and so break the bounds of the generic functions that rely on it.
pub unsafe trait AllocFreeDrop {

}

unsafe impl AllocFreeDrop for () {

}

unsafe impl AllocFreeDrop for bool {

}

unsafe impl AllocFreeDrop for char {

}

unsafe impl AllocFreeDrop for u8 {

}

unsafe impl AllocFreeDrop for u16 {

}

unsafe impl AllocFreeDrop for u32 {

}

unsafe impl AllocFreeDrop for u64 {

}

unsafe impl AllocFreeDrop for u128 {

}

unsafe impl AllocFreeDrop for usize {

}

unsafe impl AllocFreeDrop for i8 {

}

unsafe impl AllocFreeDrop for i16 {

}

unsafe impl AllocFreeDrop for i32 {

}

unsafe impl AllocFreeDrop for i64 {

}

unsafe impl AllocFreeDrop for i128 {

}

unsafe impl AllocFreeDrop for isize {

}

unsafe impl<'a, T: ?Sized> AllocFreeDrop for &'a T {

}

unsafe impl<'a, T: ?Sized> AllocFreeDrop for &'a mut T {

}

unsafe impl<T: AllocFreeDrop> AllocFreeDrop for Option<T> {

}

unsafe impl<T: AllocFreeDrop, E: AllocFreeDrop> AllocFreeDrop for Result<T, E> {

}

unsafe impl<A: AllocFreeDrop, B: AllocFreeDrop> AllocFreeDrop for (A, B) {

}

unsafe impl<A: AllocFreeDrop, B: AllocFreeDrop, C: AllocFreeDrop> AllocFreeDrop for (A, B, C) {

}

#[cfg(feature = "alloc")]
unsafe impl<T: AllocFreeDrop> AllocFreeDrop for alloc::boxed::Box<T> {

}

#[cfg(feature = "alloc")]
unsafe impl<T: AllocFreeDrop> AllocFreeDrop for alloc::vec::Vec<T> {

}

#[cfg(feature = "alloc")]
unsafe impl AllocFreeDrop for alloc::alloc::Global {

}

#[cfg(feature = "std")]
unsafe impl AllocFreeDrop for std::alloc::System {

}

#[cfg(feature = "alloc")]
unsafe impl AllocFreeDrop for alloc::string::String {

}

#[cfg(feature = "std")]
unsafe impl AllocFreeDrop for std::hash::RandomState {

}

/// Allocators (`core::alloc::Allocator`) whose allocations `-V alloc-check` counts, also when a
/// container uses them (`Vec<T, A>`, `Box<T, A>`, `Rc<T, A>`, ...).
///
/// The `Allocator` declaration bounds `deallocate` by `allocates 0` and each of `allocate`,
/// `allocate_zeroed`, `grow`, `grow_zeroed` and `shrink` by
/// `vstd::std_specs::rust_1_100::allocator_allocate_cost::<Self>()`. For an allocator `X`,
/// `unsafe impl BoundedAllocator for X { open spec fn allocate_cost() -> int { n } }` makes that
/// cost `n` (clamped at 0). `X`'s `Allocator` impl, which Verus verifies against the declaration,
/// must then make at most `n` allocations per call of those methods, counted at the leaves: a call
/// to the global or the system allocator is 1, a call to another `BoundedAllocator` costs what its
/// `allocate_cost` says. The containers' specifications charge `allocator_allocate_cost::<A>()`
/// per allocation (`Vec::push` that grows, `Box::new_in`, ...), so for `n == 0` (an arena that
/// hands out memory it already has) using the container allocates nothing.
///
/// Under `-V alloc-check` the impl is accepted only if `X`'s `Allocator` impl is one that Verus
/// checks (inside `verus!`), and every impl must be one that Verus checks. A value of a container
/// whose allocator is not the global or the system allocator may be dropped (which calls the
/// allocator's `deallocate`) only if its allocator is a `BoundedAllocator` (a reference to one is
/// one too). `AllocFreeDrop` is a supertrait: dropping the allocator itself must not allocate.
///
/// The trait is `unsafe` for the same reason as `AllocFreeDrop`.
pub unsafe trait BoundedAllocator: AllocFreeDrop {
    /// The allocations of one call of `allocate`, `allocate_zeroed`, `grow`, `grow_zeroed` or
    /// `shrink`
    spec fn allocate_cost() -> int;
}

#[cfg(feature = "alloc")]
unsafe impl BoundedAllocator for alloc::alloc::Global {
    open spec fn allocate_cost() -> int {
        1
    }
}

#[cfg(feature = "std")]
unsafe impl BoundedAllocator for std::alloc::System {
    open spec fn allocate_cost() -> int {
        1
    }
}

// `&A` and `&mut A` forward every method to `A`
unsafe impl<'a, A: BoundedAllocator + ?Sized> BoundedAllocator for &'a A {
    open spec fn allocate_cost() -> int {
        A::allocate_cost()
    }
}

unsafe impl<'a, A: BoundedAllocator + ?Sized> BoundedAllocator for &'a mut A {
    open spec fn allocate_cost() -> int {
        A::allocate_cost()
    }
}

} // verus!
