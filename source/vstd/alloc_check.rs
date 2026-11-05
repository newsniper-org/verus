//! Support for checking `allocates` bounds of exec functions (`-V alloc-check`).
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// Types whose drop glue performs no allocation.
///
/// With `-V alloc-check`, every `Drop::drop` that a checked function may run must be bounded by
/// `allocates 0`. A generic function that may drop a value of a type parameter `T` therefore needs
/// the bound `T: AllocFreeDrop` (or `T: Copy`). An `impl AllocFreeDrop for X` is only accepted
/// under `-V alloc-check` when dropping an `X` cannot allocate.
pub trait AllocFreeDrop {

}

impl AllocFreeDrop for () {

}

impl AllocFreeDrop for bool {

}

impl AllocFreeDrop for char {

}

impl AllocFreeDrop for u8 {

}

impl AllocFreeDrop for u16 {

}

impl AllocFreeDrop for u32 {

}

impl AllocFreeDrop for u64 {

}

impl AllocFreeDrop for u128 {

}

impl AllocFreeDrop for usize {

}

impl AllocFreeDrop for i8 {

}

impl AllocFreeDrop for i16 {

}

impl AllocFreeDrop for i32 {

}

impl AllocFreeDrop for i64 {

}

impl AllocFreeDrop for i128 {

}

impl AllocFreeDrop for isize {

}

impl<'a, T: ?Sized> AllocFreeDrop for &'a T {

}

impl<'a, T: ?Sized> AllocFreeDrop for &'a mut T {

}

impl<T: AllocFreeDrop> AllocFreeDrop for Option<T> {

}

impl<T: AllocFreeDrop, E: AllocFreeDrop> AllocFreeDrop for Result<T, E> {

}

impl<A: AllocFreeDrop, B: AllocFreeDrop> AllocFreeDrop for (A, B) {

}

impl<A: AllocFreeDrop, B: AllocFreeDrop, C: AllocFreeDrop> AllocFreeDrop for (A, B, C) {

}

#[cfg(feature = "alloc")]
impl<T: AllocFreeDrop> AllocFreeDrop for alloc::boxed::Box<T> {

}

#[cfg(feature = "alloc")]
impl<T: AllocFreeDrop> AllocFreeDrop for alloc::vec::Vec<T> {

}

// (`Global` is behind the unstable `allocator_api`, which vstd only enables when verifying)
#[cfg(all(feature = "alloc", verus_keep_ghost))]
impl AllocFreeDrop for alloc::alloc::Global {

}

#[cfg(feature = "alloc")]
impl AllocFreeDrop for alloc::string::String {

}

#[cfg(feature = "std")]
impl AllocFreeDrop for std::hash::RandomState {

}

} // verus!
