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

// (`Global` is behind the unstable `allocator_api`, which vstd only enables when verifying)
#[cfg(all(feature = "alloc", verus_keep_ghost))]
unsafe impl AllocFreeDrop for alloc::alloc::Global {

}

#[cfg(feature = "alloc")]
unsafe impl AllocFreeDrop for alloc::string::String {

}

#[cfg(feature = "std")]
unsafe impl AllocFreeDrop for std::hash::RandomState {

}

} // verus!
