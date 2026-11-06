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
/// The `Allocator` declaration bounds `deallocate` by `allocates 0` and `allocate`,
/// `allocate_zeroed`, `grow`, `grow_zeroed` and `shrink` by costs that may depend on the
/// allocator's value and on the arguments (`vstd::std_specs::rust_1_100::allocator_allocate_cost`
/// and the like). An `unsafe impl BoundedAllocator for X` defines them for `X`:
///
/// - `max_cost()`: an upper bound for every call, of any allocator of type `X`, with any
///   arguments (charged where a container allocates with arguments, or a cloned allocator, that
///   its specification cannot name);
/// - `allocate_cost(&self, layout)` (also for `allocate_zeroed`), `grow_cost`, `grow_zeroed_cost`
///   and `shrink_cost`: the cost of one call. By default, `allocate_cost` is `max_cost()` and the
///   others are `allocate_cost` of the new layout (what std's default bodies of `grow`,
///   `grow_zeroed` and `shrink` do: one `allocate` or `allocate_zeroed`). A cost above
///   `max_cost()` is cut down to it, and a negative one is 0.
///
/// `X`'s `Allocator` impl, which Verus verifies against these bounds, must then stay within them,
/// counted at the leaves: a call to the global or the system allocator is 1, a call to another
/// `BoundedAllocator` costs what it says. The containers charge these costs (`Vec::push` that
/// grows is `grow_cost` with the vector's pointer, its old layout and the layout of the capacity
/// that std's growth policy picks), so for an arena whose costs are 0 using the container
/// allocates nothing.
///
/// Under `-V alloc-check` the impl is accepted only if `X`'s `Allocator` impl is one that Verus
/// checks (inside `verus!`), and every impl must be one that Verus checks. It may define
/// `grow_cost`, `grow_zeroed_cost` or `shrink_cost` only if the `Allocator` impl defines `grow`,
/// `grow_zeroed` or `shrink` (std's default bodies are not verified, so their costs are the
/// defaults). A value of a container whose allocator is not the global or the system allocator
/// may be dropped (which calls the allocator's `deallocate`) only if its allocator is a
/// `BoundedAllocator` (a reference to one is one too). `AllocFreeDrop` is a supertrait: dropping
/// the allocator itself must not allocate.
///
/// The trait is `unsafe` for the same reason as `AllocFreeDrop`.
pub unsafe trait BoundedAllocator: AllocFreeDrop {
    /// An upper bound on the allocations of one call of any of the methods, for any value and
    /// arguments
    spec fn max_cost() -> int;

    /// The allocations of `self.allocate(layout)` and `self.allocate_zeroed(layout)`
    open spec fn allocate_cost(&self, layout: core::alloc::Layout) -> int {
        Self::max_cost()
    }

    /// The allocations of `self.grow(ptr, old_layout, new_layout)`
    open spec fn grow_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        self.allocate_cost(new_layout)
    }

    /// The allocations of `self.grow_zeroed(ptr, old_layout, new_layout)`
    open spec fn grow_zeroed_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        self.allocate_cost(new_layout)
    }

    /// The allocations of `self.shrink(ptr, old_layout, new_layout)`
    open spec fn shrink_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        self.allocate_cost(new_layout)
    }
}

#[cfg(feature = "alloc")]
unsafe impl BoundedAllocator for alloc::alloc::Global {
    open spec fn max_cost() -> int {
        1
    }
}

#[cfg(feature = "std")]
unsafe impl BoundedAllocator for std::alloc::System {
    open spec fn max_cost() -> int {
        1
    }
}

// `&A` and `&mut A` forward every method to `A`
unsafe impl<'a, A: BoundedAllocator + ?Sized> BoundedAllocator for &'a A {
    open spec fn max_cost() -> int {
        A::max_cost()
    }

    open spec fn allocate_cost(&self, layout: core::alloc::Layout) -> int {
        (**self).allocate_cost(layout)
    }

    open spec fn grow_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).grow_cost(ptr, old_layout, new_layout)
    }

    open spec fn grow_zeroed_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).grow_zeroed_cost(ptr, old_layout, new_layout)
    }

    open spec fn shrink_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).shrink_cost(ptr, old_layout, new_layout)
    }
}

unsafe impl<'a, A: BoundedAllocator + ?Sized> BoundedAllocator for &'a mut A {
    open spec fn max_cost() -> int {
        A::max_cost()
    }

    open spec fn allocate_cost(&self, layout: core::alloc::Layout) -> int {
        (**self).allocate_cost(layout)
    }

    open spec fn grow_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).grow_cost(ptr, old_layout, new_layout)
    }

    open spec fn grow_zeroed_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).grow_zeroed_cost(ptr, old_layout, new_layout)
    }

    open spec fn shrink_cost(
        &self,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        (**self).shrink_cost(ptr, old_layout, new_layout)
    }
}

} // verus!
