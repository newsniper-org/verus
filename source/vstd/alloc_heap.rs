//! The allocator heap of `-V alloc-check`: the states of allocators whose costs depend on a
//! mutable state (an arena's remaining capacity, a pool's free list).
//!
//! Each thread has one ghost heap `H`, which Verus threads through every exec and proof function
//! (like the allocation counter). `H` maps the location of each registered allocator to a lower
//! bound of its state (in the allocator's preorder `S::le`: "at least as good as"). The
//! allocator's implementation keeps the authoritative state (an [`AllocAuth<S>`], in its own
//! invariant), and the lower bound in `H` is the one fragment of it:
//!
//! - deallocating (also when a drop that Verus does not see calls `deallocate`) only raises the
//!   authoritative state ([`AllocAuth::raise`]), so the lower bound stays valid;
//! - allocating moves both together ([`AllocAuth::step`]), which needs `H`.
//!
//! Specifications name the heap with [`allocator_state`] (in `ensures`: the state after the call;
//! in `requires` and in the body: the current state) and [`old_allocator_state`] (the state when
//! the function was called; the only form allowed in `allocates`). Verus replaces these, and
//! [`allocator_heap`] and [`old_allocator_heap`], by the heap of the context.
#[allow(unused_imports)]
use super::prelude::*;
use super::resource::Loc;
use super::resource::preorder_auth::{Preorder, PreorderAuth, PreorderFrag};

verus! {

/// The values of the ghost allocator heap
#[verifier::external_body]
pub struct AllocHeap {
    _p: (),
}

/// Is a lower bound of the state of the allocator at `l` (with states `S`) in `h`?
pub uninterp spec fn heap_has<S>(h: AllocHeap, l: Loc) -> bool;

/// The lower bound of the state of the allocator at `l` in `h`
pub uninterp spec fn heap_state<S>(h: AllocHeap, l: Loc) -> S;

/// `h` with the lower bound at `l` changed to `s`
pub uninterp spec fn heap_set<S>(h: AllocHeap, l: Loc, s: S) -> AllocHeap;

/// `h` with a newly registered allocator at `l` in state `s`
pub uninterp spec fn heap_register<S>(h: AllocHeap, l: Loc, s: S) -> AllocHeap;

pub broadcast axiom fn axiom_heap_set_same<S>(h: AllocHeap, l: Loc, s: S)
    ensures
        #[trigger] heap_state::<S>(heap_set::<S>(h, l, s), l) == s,
;

pub broadcast axiom fn axiom_heap_set_other<S, B>(h: AllocHeap, l: Loc, s: S, q: Loc)
    requires
        q != l,
    ensures
        #[trigger] heap_state::<B>(heap_set::<S>(h, l, s), q) == heap_state::<B>(h, q),
;

pub broadcast axiom fn axiom_heap_set_has<S, B>(h: AllocHeap, l: Loc, s: S, q: Loc)
    ensures
        #[trigger] heap_has::<B>(heap_set::<S>(h, l, s), q) == heap_has::<B>(h, q),
;

pub broadcast axiom fn axiom_heap_register_same<S>(h: AllocHeap, l: Loc, s: S)
    ensures
        #[trigger] heap_state::<S>(heap_register::<S>(h, l, s), l) == s,
        heap_has::<S>(heap_register::<S>(h, l, s), l),
;

// (A newly registered allocator's location is fresh, so registering keeps every lower bound that
// was in the heap. Freshness is not visible to the solver: `Resource::alloc` does not say where
// the new resource is.)
pub broadcast axiom fn axiom_heap_register_other<S, B>(h: AllocHeap, l: Loc, s: S, q: Loc)
    requires
        heap_has::<B>(h, q),
    ensures
        #[trigger] heap_state::<B>(heap_register::<S>(h, l, s), q) == heap_state::<B>(h, q),
;

pub broadcast axiom fn axiom_heap_register_has<S, B>(h: AllocHeap, l: Loc, s: S, q: Loc)
    requires
        heap_has::<B>(h, q),
    ensures
        #[trigger] heap_has::<B>(heap_register::<S>(h, l, s), q),
;

pub broadcast axiom fn axiom_heap_set_unchanged<S>(h: AllocHeap, l: Loc)
    requires
        heap_has::<S>(h, l),
    ensures
        #[trigger] heap_set::<S>(h, l, heap_state::<S>(h, l)) == h,
;

pub broadcast group group_alloc_heap_axioms {
    axiom_heap_set_unchanged,
    axiom_heap_set_same,
    axiom_heap_set_other,
    axiom_heap_set_has,
    axiom_heap_register_same,
    axiom_heap_register_other,
    axiom_heap_register_has,
}

/// The heap of the context. Verus replaces this: in `ensures`, the heap after the call; in
/// `requires` and in a body, the current heap.
pub uninterp spec fn allocator_heap() -> AllocHeap;

/// The heap when the enclosing function was called. Verus replaces this.
pub uninterp spec fn old_allocator_heap() -> AllocHeap;

/// The lower bound of `a`'s state in the heap of the context (see [`allocator_heap`])
pub uninterp spec fn allocator_state<A: StatefulAllocator + ?Sized>(a: &A) -> A::State;

/// The lower bound of `a`'s state when the enclosing function was called (see
/// [`old_allocator_heap`])
pub uninterp spec fn old_allocator_state<A: StatefulAllocator + ?Sized>(a: &A) -> A::State;

/// Is `a` registered in the heap of the context?
pub uninterp spec fn allocator_tracked<A: StatefulAllocator + ?Sized>(a: &A) -> bool;

/// What Verus replaces [`allocator_state`] and [`old_allocator_state`] by
pub open spec fn allocator_state_in<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
) -> A::State {
    heap_state::<A::State>(h, a.loc())
}

/// What Verus replaces [`allocator_tracked`] by
pub open spec fn allocator_tracked_in<A: StatefulAllocator + ?Sized>(h: AllocHeap, a: &A) -> bool {
    heap_has::<A::State>(h, a.loc())
}

/// A witness that an allocator at `self.loc()` with states `S` is registered in the heap of this
/// thread. It is neither `Send` nor `Sync`, and neither is an allocator that keeps one (as
/// [`StatefulAllocator`] requires), so the allocator and its lower bound stay in one thread.
pub tracked struct Registered<S> {
    _not_send: core::marker::PhantomData<*const ()>,
    _s: core::marker::PhantomData<S>,
    ghost l: Loc,
}

impl<S> Registered<S> {
    pub closed spec fn loc(self) -> Loc {
        self.l
    }
}

// A witness's allocator is in the heap: its fragment went into the heap of this thread when it
// was registered and never leaves it, and the witness stays in this thread (it is not `Send`)
pub axiom fn lemma_registered<S>(tracked reg: &Registered<S>)
    ensures
        heap_has::<S>(allocator_heap(), reg.loc()),
        allocator_heap() == old_allocator_heap(),
;

/// -V alloc-check: what Verus charges for `a.allocate(layout)` (and `allocate_zeroed`) on an
/// allocator with a state, in heap `h`
pub open spec fn stateful_allocate_cost<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
) -> int {
    crate::std_specs::rust_1_100::clamp_cost(
        a.allocate_cost_at(heap_state::<A::State>(h, a.loc()), layout),
        A::max_cost(),
    )
}

/// The heap after `a.allocate(layout)` returned `r`, in heap `h`
pub open spec fn stateful_allocate_heap<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> AllocHeap {
    heap_set::<A::State>(h, a.loc(), a.allocate_next(heap_state::<A::State>(h, a.loc()), layout, r))
}

/// What Verus charges for `a.grow(ptr, old_layout, new_layout)` (and `grow_zeroed`)
pub open spec fn stateful_grow_cost<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
) -> int {
    crate::std_specs::rust_1_100::clamp_cost(
        a.grow_cost_at(heap_state::<A::State>(h, a.loc()), ptr, old_layout, new_layout),
        A::max_cost(),
    )
}

/// The heap after `a.grow(ptr, old_layout, new_layout)` (or `grow_zeroed`) returned `r`
pub open spec fn stateful_grow_heap<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> AllocHeap {
    heap_set::<A::State>(
        h,
        a.loc(),
        a.grow_next(heap_state::<A::State>(h, a.loc()), ptr, old_layout, new_layout, r),
    )
}

/// What Verus charges for `a.shrink(ptr, old_layout, new_layout)`
pub open spec fn stateful_shrink_cost<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
) -> int {
    crate::std_specs::rust_1_100::clamp_cost(
        a.shrink_cost_at(heap_state::<A::State>(h, a.loc()), ptr, old_layout, new_layout),
        A::max_cost(),
    )
}

/// The heap after `a.shrink(ptr, old_layout, new_layout)` returned `r`
pub open spec fn stateful_shrink_heap<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> AllocHeap {
    heap_set::<A::State>(
        h,
        a.loc(),
        a.shrink_next(heap_state::<A::State>(h, a.loc()), ptr, old_layout, new_layout, r),
    )
}

/// Is `a` in heap `h`? (Always, for a live allocator: see `lemma_registered`.)
pub open spec fn stateful_tracked<A: StatefulAllocator + ?Sized>(h: AllocHeap, a: &A) -> bool {
    heap_has::<A::State>(h, a.loc())
}

/// The authoritative state of an allocator registered in the heap (see the module documentation)
pub tracked struct AllocAuth<S: Preorder> {
    inner: PreorderAuth<S>,
}

// Moves the fragment into the heap. (The heap is not a value: it holds the fragments, which no
// code outside this module can name.)
axiom fn deposit<S: Preorder>(tracked f: PreorderFrag<S>)
    ensures
        allocator_heap() == heap_register::<S>(old_allocator_heap(), f.id(), f@),
;

// Replace the fragment at `l` (which is in the heap) by `f`
axiom fn replace_frag<S: Preorder>(tracked f: PreorderFrag<S>)
    requires
        heap_has::<S>(old_allocator_heap(), f.id()),
    ensures
        allocator_heap() == heap_set::<S>(old_allocator_heap(), f.id(), f@),
;

// Take the fragment at `l` out of the heap; `replace_frag` must put one back before the
// enclosing proof function returns
axiom fn take_frag<S: Preorder>(l: Loc) -> (tracked f: PreorderFrag<S>)
    requires
        heap_has::<S>(old_allocator_heap(), l),
    ensures
        f.id() == l,
        f@ == heap_state::<S>(old_allocator_heap(), l),
        allocator_heap() == old_allocator_heap(),
;

impl<S: Preorder> AllocAuth<S> {
    pub closed spec fn id(self) -> Loc {
        self.inner.id()
    }

    pub closed spec fn view(self) -> S {
        self.inner@
    }

    /// Register a new allocator with state `s`
    pub proof fn register(s: S) -> (tracked out: (AllocAuth<S>, Registered<S>))
        ensures
            out.0.id() == out.1.loc(),
            out.0@ == s,
            allocator_heap() == heap_register::<S>(old_allocator_heap(), out.0.id(), s),
    {
        let tracked (a, f) = PreorderAuth::new(s);
        let l = a.id();
        deposit(f);
        let tracked reg = Registered {
            _not_send: core::marker::PhantomData,
            _s: core::marker::PhantomData,
            l,
        };
        (AllocAuth { inner: a }, reg)
    }

    /// The lower bound in the heap is a lower bound of the authoritative state
    pub proof fn lower_bound(tracked &mut self, tracked reg: &Registered<S>)
        requires
            old(self).id() == reg.loc(),
            heap_has::<S>(old_allocator_heap(), reg.loc()),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == old(self)@,
            allocator_heap() == old_allocator_heap(),
            heap_state::<S>(old_allocator_heap(), reg.loc()).le(old(self)@),
    {
        broadcast use axiom_heap_set_unchanged;

        let tracked f = take_frag::<S>(reg.loc());
        self.inner.lower_bound(&f);
        replace_frag(f);
    }

    /// Raise the authoritative state alone (deallocation)
    pub proof fn raise(tracked &mut self, new_state: S)
        requires
            old(self)@.le(new_state),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == new_state,
    {
        self.inner.raise(new_state);
    }

    /// Move the authoritative state and its lower bound in the heap together (allocation)
    pub proof fn step(tracked &mut self, tracked reg: &Registered<S>, new_auth: S, new_lower: S)
        requires
            old(self).id() == reg.loc(),
            heap_has::<S>(old_allocator_heap(), reg.loc()),
            new_lower.le(new_auth),
        ensures
            final(self).id() == old(self).id(),
            final(self)@ == new_auth,
            allocator_heap() == heap_set::<S>(old_allocator_heap(), reg.loc(), new_lower),
    {
        let tracked mut f = take_frag::<S>(reg.loc());
        self.inner.step(&mut f, new_auth, new_lower);
        replace_frag(f);
    }
}

/// An allocator whose costs depend on its state, which the heap keeps track of (see the module
/// documentation). It must keep its [`Registered`] witness (`witness`), which makes it neither
/// `Send` nor `Sync`.
///
/// Verus charges a call `a.allocate(layout)` (and the other `Allocator` methods)
/// `clamp_cost(a.allocate_cost_at(s, layout), max_cost())` where `s = allocator_state(a)`, and
/// sets `allocator_state(a)` to `a.allocate_next(s, layout, r)` after it; the impl's `allocate` is
/// verified against the same two facts. Unknown states cost at most `max_cost()`.
pub unsafe trait StatefulAllocator: crate::alloc_check::BoundedAllocator {
    type State: Preorder;

    /// The location of the allocator's state
    spec fn loc(&self) -> Loc;

    proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Self::State>)
        ensures
            w.loc() == self.loc(),
    ;

    /// The allocations of `self.allocate(layout)` and `self.allocate_zeroed(layout)` when the
    /// state is at least `s`
    spec fn allocate_cost_at(&self, s: Self::State, layout: core::alloc::Layout) -> int;

    /// The state after `self.allocate(layout)` (or `allocate_zeroed`) returned `r`
    spec fn allocate_next(
        &self,
        s: Self::State,
        layout: core::alloc::Layout,
        r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
    ) -> Self::State;

    /// The allocations of `self.grow(ptr, old_layout, new_layout)` (and `grow_zeroed`) when the
    /// state is at least `s`. By default, what std's default bodies do: one `allocate` with the
    /// new layout. Only an allocator whose `Allocator` impl defines `grow` and `grow_zeroed` may
    /// change it (or `grow_next`).
    open spec fn grow_cost_at(
        &self,
        s: Self::State,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        self.allocate_cost_at(s, new_layout)
    }

    /// The state after `self.grow(ptr, old_layout, new_layout)` (or `grow_zeroed`) returned `r`
    open spec fn grow_next(
        &self,
        s: Self::State,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
        r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
    ) -> Self::State {
        self.allocate_next(s, new_layout, r)
    }

    /// The allocations of `self.shrink(ptr, old_layout, new_layout)` (see `grow_cost_at`; only an
    /// allocator whose `Allocator` impl defines `shrink` may change it, or `shrink_next`)
    open spec fn shrink_cost_at(
        &self,
        s: Self::State,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
    ) -> int {
        self.allocate_cost_at(s, new_layout)
    }

    /// The state after `self.shrink(ptr, old_layout, new_layout)` returned `r`
    open spec fn shrink_next(
        &self,
        s: Self::State,
        ptr: core::ptr::NonNull<u8>,
        old_layout: core::alloc::Layout,
        new_layout: core::alloc::Layout,
        r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
    ) -> Self::State {
        self.allocate_next(s, new_layout, r)
    }
}

// ---- The cost and the heap after an allocator call, for any allocator type (the containers'
// specifications use these; see `std_specs::vec`)
use super::std_specs::rust_1_100::{allocator_allocate_cost, allocator_grow_cost};

/// The allocations of `a.allocate(layout)` in heap `h`: at most the stateless cost, and at most
/// the cost at the state for an allocator with a state
pub uninterp spec fn allocator_allocate_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
) -> int;

/// The allocations of `a.grow(ptr, old_layout, new_layout)` in heap `h` (see
/// `allocator_allocate_cost_in`)
pub uninterp spec fn allocator_grow_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
) -> int;

/// The heap after `a.allocate(layout)` returned `r`, in heap `h`: the same for the global and the
/// system allocator, moved by `allocate_next` for an allocator with a state, and unknown otherwise
pub uninterp spec fn allocator_allocate_heap_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> AllocHeap;

/// The heap after `a.grow(ptr, old_layout, new_layout)` returned `r` (see
/// `allocator_allocate_heap_in`)
pub uninterp spec fn allocator_grow_heap_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
) -> AllocHeap;

pub broadcast axiom fn axiom_allocator_allocate_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
)
    ensures
        0 <= #[trigger] allocator_allocate_cost_in::<A>(h, a, layout) <= allocator_allocate_cost::<
            A,
        >(a, layout),
;

pub broadcast axiom fn axiom_allocator_grow_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
)
    ensures
        0 <= #[trigger] allocator_grow_cost_in::<A>(h, a, ptr, old_layout, new_layout)
            <= allocator_grow_cost::<A>(a, ptr, old_layout, new_layout),
;

pub broadcast axiom fn axiom_stateful_allocate_cost_in<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_allocate_cost_in::<A>(h, a, layout) <= stateful_allocate_cost::<A>(
            h,
            a,
            layout,
        ),
;

pub broadcast axiom fn axiom_stateful_allocate_heap_in<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_allocate_heap_in::<A>(h, a, layout, r) == stateful_allocate_heap::<A>(
            h,
            a,
            layout,
            r,
        ),
;

pub broadcast axiom fn axiom_stateful_grow_in<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_grow_cost_in::<A>(h, a, ptr, old_layout, new_layout)
            <= stateful_grow_cost::<A>(h, a, ptr, old_layout, new_layout),
;

pub broadcast axiom fn axiom_stateful_grow_heap_in<A: StatefulAllocator + ?Sized>(
    h: AllocHeap,
    a: &A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_grow_heap_in::<A>(h, a, ptr, old_layout, new_layout, r)
            == stateful_grow_heap::<A>(h, a, ptr, old_layout, new_layout, r),
;

// (the global and the system allocator have no state in the heap, and cost what they always do)
#[cfg(feature = "alloc")]
pub broadcast axiom fn axiom_global_allocate_in(
    h: AllocHeap,
    a: &alloc::alloc::Global,
    layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_allocate_heap_in::<alloc::alloc::Global>(h, a, layout, r) == h,
;

#[cfg(feature = "alloc")]
pub broadcast axiom fn axiom_global_allocate_cost_in(
    h: AllocHeap,
    a: &alloc::alloc::Global,
    layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_allocate_cost_in::<alloc::alloc::Global>(h, a, layout)
            == allocator_allocate_cost::<alloc::alloc::Global>(a, layout),
;

#[cfg(feature = "alloc")]
pub broadcast axiom fn axiom_global_grow_in(
    h: AllocHeap,
    a: &alloc::alloc::Global,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_grow_heap_in::<alloc::alloc::Global>(
            h,
            a,
            ptr,
            old_layout,
            new_layout,
            r,
        ) == h,
;

#[cfg(feature = "alloc")]
pub broadcast axiom fn axiom_global_grow_cost_in(
    h: AllocHeap,
    a: &alloc::alloc::Global,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_grow_cost_in::<alloc::alloc::Global>(h, a, ptr, old_layout, new_layout)
            == allocator_grow_cost::<alloc::alloc::Global>(a, ptr, old_layout, new_layout),
;

// (`&A` forwards every method to `A`)
pub broadcast axiom fn axiom_ref_allocate_in<A: ?Sized>(
    h: AllocHeap,
    a: &&A,
    layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_allocate_heap_in::<&A>(h, a, layout, r)
            == allocator_allocate_heap_in::<A>(h, *a, layout, r),
;

pub broadcast axiom fn axiom_ref_allocate_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &&A,
    layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_allocate_cost_in::<&A>(h, a, layout) == allocator_allocate_cost_in::<
            A,
        >(h, *a, layout),
;

pub broadcast axiom fn axiom_ref_grow_in<A: ?Sized>(
    h: AllocHeap,
    a: &&A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
    r: Result<core::ptr::NonNull<[u8]>, core::alloc::AllocError>,
)
    ensures
        #[trigger] allocator_grow_heap_in::<&A>(h, a, ptr, old_layout, new_layout, r)
            == allocator_grow_heap_in::<A>(h, *a, ptr, old_layout, new_layout, r),
;

pub broadcast axiom fn axiom_ref_grow_cost_in<A: ?Sized>(
    h: AllocHeap,
    a: &&A,
    ptr: core::ptr::NonNull<u8>,
    old_layout: core::alloc::Layout,
    new_layout: core::alloc::Layout,
)
    ensures
        #[trigger] allocator_grow_cost_in::<&A>(h, a, ptr, old_layout, new_layout)
            == allocator_grow_cost_in::<A>(h, *a, ptr, old_layout, new_layout),
;

pub broadcast group group_allocator_in_axioms {
    axiom_allocator_allocate_cost_in,
    axiom_allocator_grow_cost_in,
    axiom_stateful_allocate_cost_in,
    axiom_stateful_allocate_heap_in,
    axiom_stateful_grow_in,
    axiom_stateful_grow_heap_in,
    #[cfg(feature = "alloc")]
    axiom_global_allocate_in,
    #[cfg(feature = "alloc")]
    axiom_global_allocate_cost_in,
    #[cfg(feature = "alloc")]
    axiom_global_grow_in,
    #[cfg(feature = "alloc")]
    axiom_global_grow_cost_in,
    axiom_ref_allocate_in,
    axiom_ref_allocate_cost_in,
    axiom_ref_grow_in,
    axiom_ref_grow_cost_in,
}

} // verus!
