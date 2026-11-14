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

/// `T: Tr with { fn drop allocates 0; }` on a function's type parameter stands for the
/// precondition `bound_drop_alloc_free::<T>()`: inside the function, dropping a `T` allocates
/// nothing; at a call, Verus checks it for the type `T` is instantiated with (its drop glue) and
/// then assumes it. (No other code can show it.)
pub uninterp spec fn bound_drop_alloc_free<T: ?Sized>() -> bool;

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

/// Types whose drop glue does not deallocate memory: a `#[verifier::fip]` function (fully
/// in-place, FP²) may drop values of them on paths that return normally.
///
/// A `#[verifier::fip]` function must not deallocate. Its drops are checked on the MIR of the
/// compiled program, after drop elaboration: a value that is dropped there (rather than moved,
/// returned or reused) must have no drop glue at all, or be of a type that implements this trait
/// (a generic one needs the bound `T: NoDeallocDrop`). An `unsafe impl NoDeallocDrop for X` is
/// only accepted when dropping an `X` cannot deallocate: `X` is not a `Box`, its own `Drop`
/// (if any) is `#[verifier::fip]`, and each of its fields has no drop glue or is
/// `NoDeallocDrop`. Every impl in the program is checked, whichever crate it is in.
/// `AllocFreeDrop` is a supertrait: such a drop does not allocate either.
pub unsafe trait NoDeallocDrop: AllocFreeDrop {

}

/// Dropping a value of type `T` may deallocate (false for a `NoDeallocDrop` type)
pub uninterp spec fn drop_may_deallocate<T: ?Sized>() -> bool;

pub broadcast axiom fn axiom_no_dealloc_drop<T: NoDeallocDrop + ?Sized>()
    ensures
        !#[trigger] drop_may_deallocate::<T>(),
;

pub broadcast group group_alloc_check_axioms {
    axiom_no_dealloc_drop,
}

unsafe impl NoDeallocDrop for () {

}

unsafe impl NoDeallocDrop for bool {

}

unsafe impl NoDeallocDrop for char {

}

unsafe impl NoDeallocDrop for u8 {

}

unsafe impl NoDeallocDrop for u16 {

}

unsafe impl NoDeallocDrop for u32 {

}

unsafe impl NoDeallocDrop for u64 {

}

unsafe impl NoDeallocDrop for u128 {

}

unsafe impl NoDeallocDrop for usize {

}

unsafe impl NoDeallocDrop for i8 {

}

unsafe impl NoDeallocDrop for i16 {

}

unsafe impl NoDeallocDrop for i32 {

}

unsafe impl NoDeallocDrop for i64 {

}

unsafe impl NoDeallocDrop for i128 {

}

unsafe impl NoDeallocDrop for isize {

}

unsafe impl<'a, T: ?Sized> NoDeallocDrop for &'a T {

}

unsafe impl<'a, T: ?Sized> NoDeallocDrop for &'a mut T {

}

unsafe impl<T: NoDeallocDrop> NoDeallocDrop for Option<T> {

}

unsafe impl<T: NoDeallocDrop, E: NoDeallocDrop> NoDeallocDrop for Result<T, E> {

}

unsafe impl<A: NoDeallocDrop, B: NoDeallocDrop> NoDeallocDrop for (A, B) {

}

unsafe impl<A: NoDeallocDrop, B: NoDeallocDrop, C: NoDeallocDrop> NoDeallocDrop for (A, B, C) {

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

/// Allocators that a `#[verifier::fip]` function (fully in-place, FP²) may use through std's
/// containers.
///
/// A container that grows without a buffer to reallocate (`Vec::push` on an empty vector) only
/// calls its allocator's `allocate`, which for a user allocator is user code: a fip function may
/// instantiate std (or vstd) code with an allocator other than the global or the system allocator
/// only if the allocator implements this trait (a generic one needs the bound
/// `A: FipAllocator`). An `unsafe impl FipAllocator for X` is accepted only if `X`'s `allocate`
/// (and `allocate_zeroed`, if the `Allocator` impl defines it) and `X`'s `Clone::clone` (if any)
/// are `#[verifier::fip]` functions of the same crate. `NoDeallocDrop` is a supertrait: dropping
/// the allocator does not deallocate.
pub unsafe trait FipAllocator: core::alloc::Allocator + BoundedAllocator + NoDeallocDrop {

}

/// Allocators that a `#[verifier::fip(strict)]` function may use through std's containers: as
/// `FipAllocator`, with `#[verifier::fip(strict)]` methods (constant stack space), none of which
/// can reach (through calls that are not tail calls or through other allocators) a function that
/// uses a user allocator itself.
pub unsafe trait FipStrictAllocator: FipAllocator {

}

#[cfg(feature = "alloc")]
unsafe impl NoDeallocDrop for alloc::alloc::Global {

}

#[cfg(feature = "alloc")]
unsafe impl FipAllocator for alloc::alloc::Global {

}

#[cfg(feature = "alloc")]
unsafe impl FipStrictAllocator for alloc::alloc::Global {

}

#[cfg(feature = "std")]
unsafe impl NoDeallocDrop for std::alloc::System {

}

#[cfg(feature = "std")]
unsafe impl FipAllocator for std::alloc::System {

}

#[cfg(feature = "std")]
unsafe impl FipStrictAllocator for std::alloc::System {

}

unsafe impl<'a, A: FipAllocator + ?Sized> FipAllocator for &'a A {

}

unsafe impl<'a, A: FipStrictAllocator + ?Sized> FipStrictAllocator for &'a A {

}

unsafe impl<'a, A: FipAllocator + ?Sized> FipAllocator for &'a mut A {

}

unsafe impl<'a, A: FipStrictAllocator + ?Sized> FipStrictAllocator for &'a mut A {

}

/// The address of a block `NonNull<[u8]>` (as an allocator returns it)
pub open spec fn block_addr(block: core::ptr::NonNull<[u8]>) -> usize {
    super::std_specs::ptr::spec_nonnull_as_ptr(block)@.addr
}

/// The length of a block `NonNull<[u8]>`
pub open spec fn block_len(block: core::ptr::NonNull<[u8]>) -> usize {
    super::std_specs::ptr::spec_nonnull_as_ptr(block)@.metadata
}

/// The provenance of a block `NonNull<[u8]>`
pub open spec fn block_provenance(block: core::ptr::NonNull<[u8]>) -> super::raw_ptr::Provenance {
    super::std_specs::ptr::spec_nonnull_as_ptr(block)@.provenance
}

/// The receipt for a block that an `Allocator` impl handed out ([`hand_out`]): it gives no access
/// to the block, and [`reclaim`] turns it back into the block's permission when the block is
/// returned to `deallocate` (or `grow`, `shrink`).
#[verifier::external_body]
pub tracked struct Handout {
    _no_copy: NoCopy,
}

impl Handout {
    pub uninterp spec fn addr(self) -> usize;

    pub uninterp spec fn len(self) -> usize;

    pub uninterp spec fn provenance(self) -> super::raw_ptr::Provenance;
}

/// Gives up the permission of `block` (as std's containers own the memory that an allocator
/// returns): in the body of a user's `Allocator::allocate` (or `allocate_zeroed`, `grow`,
/// `grow_zeroed`, `shrink`), the block returned in `Ok` must be the last one this call handed out
/// (or got from another allocator), and Verus allows `hand_out` only there. The receipt can be
/// kept, to [`reclaim`] the block later.
pub axiom fn hand_out(
    tracked pt: super::raw_ptr::PointsToRaw,
    block: core::ptr::NonNull<[u8]>,
) -> (tracked h: Handout)
    requires
        pt.is_range(block_addr(block) as int, block_len(block) as int),
        pt.provenance() == block_provenance(block),
    ensures
        h.addr() == block_addr(block),
        h.len() == block_len(block),
        h.provenance() == pt.provenance(),
;

/// Takes back the permission of the block that the caller of `deallocate` (or `grow`, `shrink`)
/// returns: std's `Allocator` contract says that `ptr` is a block this allocator (or an equivalent
/// one) handed out and that the caller no longer uses it. Verus allows `reclaim` only in the body
/// of a user's `Allocator::deallocate` (or `grow`, `grow_zeroed`, `shrink`), with that method's
/// `ptr`, at most once (and, in `grow` or `shrink`, not if it returns `Err`: the old block is then
/// still the caller's). The receipt says what the block was.
pub axiom fn reclaim(
    ptr: core::ptr::NonNull<u8>,
    layout: core::alloc::Layout,
    tracked h: Handout,
) -> (tracked pt: super::raw_ptr::PointsToRaw)
    requires
        h.addr() == super::std_specs::ptr::spec_nonnull_as_ptr(ptr)@.addr,
        super::std_specs::rust_1_100::spec_layout_size(layout) <= h.len(),
    ensures
        pt.is_range(h.addr() as int, h.len() as int),
        pt.provenance() == h.provenance(),
;

} // verus!
// Marker traits for the operator traits of `core` (FP²'s `fip` and `fbip` for one trait's
// methods). For an operator trait `Op` (`Add`, `PartialEq`, `Index`, ...), there are three
// levels, each a supertrait of the next:
//
// - `FbipOp`: every method of `X`'s `Op` impl that the impl defines is bounded by `allocates 0`
//   (FP²'s `fbip`: no allocation). A generic call of an `Op` method through `T: FbipOp` is
//   charged 0 by `-V alloc-check`.
// - `FipOp`: also, each of those methods is `#[verifier::fip]` (FP²'s `fip`: no allocation, no
//   deallocation). A `#[verifier::fip]` function may call an `Op` method through `T: FipOp`.
// - `FipStrictOp`: also, each of those methods is `#[verifier::fip(strict)]` (constant stack
//   space). A `#[verifier::fip(strict)]` function may call an `Op` method through
//   `T: FipStrictOp` (except `Ord::{max, min, clamp}`, which drop a `T`).
//
// The methods an impl does not define run `core`'s provided bodies, which call only the trait's
// own methods (`ne` calls `eq`, `lt` calls `partial_cmp`). `Ord`'s provided `max`, `min` and
// `clamp` also drop a value of `Self`: so `FbipOrd` needs `AllocFreeDrop` and `FipOrd` needs
// `NoDeallocDrop`. The markers follow the supertraits of the operator traits (`FipOrd` implies
// `FipPartialOrd` and `FipPartialEq`, `FipIndexMut` implies `FipIndex`).
//
// The traits are `unsafe`, and every impl outside vstd is checked by `-V alloc-check` (an impl
// in a crate that was not verified with it is rejected where it is used). vstd's impls for the
// primitive types are trusted.
macro_rules! def_op_markers {
    ($($op:path => $fbip:ident, $fip:ident, $strict:ident [$($g:tt)*] [$($a:tt)*] [$($sup_fbip:tt)*] [$($sup_fip:tt)*] [$($sup_strict:tt)*];)*) => {
        verus! {
            $(
                pub unsafe trait $fbip<$($g)*>: $op<$($a)*> $($sup_fbip)* {}
                pub unsafe trait $fip<$($g)*>: $fbip<$($a)*> $($sup_fip)* {}
                pub unsafe trait $strict<$($g)*>: $fip<$($a)*> $($sup_strict)* {}
            )*
        }
    };
}

def_op_markers! {
    core::ops::Neg => FbipNeg, FipNeg, FipStrictNeg [] [] [] [] [];
    core::ops::Not => FbipNot, FipNot, FipStrictNot [] [] [] [] [];
    core::ops::Add => FbipAdd, FipAdd, FipStrictAdd [Rhs = Self] [Rhs] [] [] [];
    core::ops::Sub => FbipSub, FipSub, FipStrictSub [Rhs = Self] [Rhs] [] [] [];
    core::ops::Mul => FbipMul, FipMul, FipStrictMul [Rhs = Self] [Rhs] [] [] [];
    core::ops::Div => FbipDiv, FipDiv, FipStrictDiv [Rhs = Self] [Rhs] [] [] [];
    core::ops::Rem => FbipRem, FipRem, FipStrictRem [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitAnd => FbipBitAnd, FipBitAnd, FipStrictBitAnd [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitOr => FbipBitOr, FipBitOr, FipStrictBitOr [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitXor => FbipBitXor, FipBitXor, FipStrictBitXor [Rhs = Self] [Rhs] [] [] [];
    core::ops::Shl => FbipShl, FipShl, FipStrictShl [Rhs = Self] [Rhs] [] [] [];
    core::ops::Shr => FbipShr, FipShr, FipStrictShr [Rhs = Self] [Rhs] [] [] [];
    core::ops::AddAssign => FbipAddAssign, FipAddAssign, FipStrictAddAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::SubAssign => FbipSubAssign, FipSubAssign, FipStrictSubAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::MulAssign => FbipMulAssign, FipMulAssign, FipStrictMulAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::DivAssign => FbipDivAssign, FipDivAssign, FipStrictDivAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::RemAssign => FbipRemAssign, FipRemAssign, FipStrictRemAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitAndAssign => FbipBitAndAssign, FipBitAndAssign, FipStrictBitAndAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitOrAssign => FbipBitOrAssign, FipBitOrAssign, FipStrictBitOrAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::BitXorAssign => FbipBitXorAssign, FipBitXorAssign, FipStrictBitXorAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::ShlAssign => FbipShlAssign, FipShlAssign, FipStrictShlAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::ShrAssign => FbipShrAssign, FipShrAssign, FipStrictShrAssign [Rhs = Self] [Rhs] [] [] [];
    core::ops::Index => FbipIndex, FipIndex, FipStrictIndex [Idx: ?Sized] [Idx] [] [] [];
    core::ops::IndexMut => FbipIndexMut, FipIndexMut, FipStrictIndexMut [Idx: ?Sized] [Idx] [+ FbipIndex<Idx>] [+ FipIndex<Idx>] [+ FipStrictIndex<Idx>];
    core::ops::Deref => FbipDeref, FipDeref, FipStrictDeref [] [] [] [] [];
    core::ops::DerefMut => FbipDerefMut, FipDerefMut, FipStrictDerefMut [] [] [+ FbipDeref] [+ FipDeref] [+ FipStrictDeref];
    core::cmp::PartialEq => FbipPartialEq, FipPartialEq, FipStrictPartialEq [Rhs: ?Sized = Self] [Rhs] [] [] [];
    core::cmp::PartialOrd => FbipPartialOrd, FipPartialOrd, FipStrictPartialOrd [Rhs: ?Sized = Self] [Rhs] [+ FbipPartialEq<Rhs>] [+ FipPartialEq<Rhs>] [+ FipStrictPartialEq<Rhs>];
    core::cmp::Ord => FbipOrd, FipOrd, FipStrictOrd [] [] [+ FbipPartialOrd + AllocFreeDrop] [+ FipPartialOrd + NoDeallocDrop] [+ FipStrictPartialOrd];
}

// vstd's impls for the primitive types (trusted: std's arithmetic, bit operations and comparisons
// of primitives neither allocate nor deallocate, and use bounded stack space)
macro_rules! op_marker_impls {
    ($markers:tt [$($t:ty)*]) => {
        $(op_marker_impls!(@one $t $markers);)*
    };
    (@one $t:ty [$($fbip:ident, $fip:ident, $strict:ident);*]) => {
        verus! {
            $(
                unsafe impl $fbip for $t {}
                unsafe impl $fip for $t {}
                unsafe impl $strict for $t {}
            )*
        }
    };
}

op_marker_impls!([
    FbipAdd, FipAdd, FipStrictAdd; FbipSub, FipSub, FipStrictSub; FbipMul, FipMul, FipStrictMul;
    FbipDiv, FipDiv, FipStrictDiv; FbipRem, FipRem, FipStrictRem;
    FbipBitAnd, FipBitAnd, FipStrictBitAnd; FbipBitOr, FipBitOr, FipStrictBitOr;
    FbipBitXor, FipBitXor, FipStrictBitXor; FbipShl, FipShl, FipStrictShl;
    FbipShr, FipShr, FipStrictShr; FbipNot, FipNot, FipStrictNot;
    FbipAddAssign, FipAddAssign, FipStrictAddAssign; FbipSubAssign, FipSubAssign, FipStrictSubAssign;
    FbipMulAssign, FipMulAssign, FipStrictMulAssign; FbipDivAssign, FipDivAssign, FipStrictDivAssign;
    FbipRemAssign, FipRemAssign, FipStrictRemAssign;
    FbipBitAndAssign, FipBitAndAssign, FipStrictBitAndAssign;
    FbipBitOrAssign, FipBitOrAssign, FipStrictBitOrAssign;
    FbipBitXorAssign, FipBitXorAssign, FipStrictBitXorAssign;
    FbipShlAssign, FipShlAssign, FipStrictShlAssign; FbipShrAssign, FipShrAssign, FipStrictShrAssign;
    FbipPartialEq, FipPartialEq, FipStrictPartialEq; FbipPartialOrd, FipPartialOrd, FipStrictPartialOrd;
    FbipOrd, FipOrd, FipStrictOrd
] [u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize]);

op_marker_impls!([FbipNeg, FipNeg, FipStrictNeg] [i8 i16 i32 i64 i128 isize]);

op_marker_impls!([
    FbipNot, FipNot, FipStrictNot; FbipBitAnd, FipBitAnd, FipStrictBitAnd;
    FbipBitOr, FipBitOr, FipStrictBitOr; FbipBitXor, FipBitXor, FipStrictBitXor;
    FbipBitAndAssign, FipBitAndAssign, FipStrictBitAndAssign;
    FbipBitOrAssign, FipBitOrAssign, FipStrictBitOrAssign;
    FbipBitXorAssign, FipBitXorAssign, FipStrictBitXorAssign;
    FbipPartialEq, FipPartialEq, FipStrictPartialEq; FbipPartialOrd, FipPartialOrd, FipStrictPartialOrd;
    FbipOrd, FipOrd, FipStrictOrd
] [bool]);

op_marker_impls!([
    FbipPartialEq, FipPartialEq, FipStrictPartialEq; FbipPartialOrd, FipPartialOrd, FipStrictPartialOrd;
    FbipOrd, FipOrd, FipStrictOrd
] [char]);
