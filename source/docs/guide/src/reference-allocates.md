# Allocation bounds (`allocates`)

> **Fork extension, experimental.** The `allocates` clause and the `-V alloc-check` /
> `-V alloc-check-strict` options exist in this fork of Verus only. A Korean version of this
> page is [here](./reference-allocates.ko.md).
>
> For an introduction to fully in-place functions (FP²'s `fip` and `fbip`) with examples, see
> [FIP and FBIP](./fip-fbip.md).

An `exec` function can state an upper bound on the number of allocator calls it makes:

```rust
fn make_pair(x: u64) -> (r: (Box<u64>, Box<u64>))
    allocates 2
{
    (Box::new(x), Box::new(x))
}
```

The bound is a single spec expression of type `int` over the function's parameters. It is
evaluated when the function is entered, so a `&mut` parameter refers to its value at entry
(`old(v)`):

```rust
fn push_one(v: &mut Vec<u64>, x: u64)
    allocates if old(v)@.len() == vstd::std_specs::vec::spec_vec_capacity(&*old(v)) { 1int } else { 0int }
{
    v.push(x);
}
```

The clause goes with the other signature clauses (`requires`, `ensures`, `opens_invariants`,
`no_unwind`, ...). It is only allowed on `exec` functions and on `exec` closures.

## Checking bounds: `-V alloc-check`

Without a flag, `allocates` is parsed and kept, but nothing is checked and no bound is assumed.

With `-V alloc-check`, Verus checks every function that has an `allocates` bound:

* A ghost counter, `allocated()`, starts at 0 when the function is entered.
* Every exec call adds the callee's own `allocates` bound (applied to the call's arguments) to
  the counter. A call to a function without an `allocates` bound is rejected inside a checked
  function, because its allocations are unknown.
* At every normal return, the counter must be at most the function's bound.

`allocated()` can be used in loop invariants and assertions:

```rust
fn boxes(n: usize) -> (r: Vec<Box<usize>>)
    allocates 1 + n
{
    broadcast use vstd::std_specs::vec::group_vec_axioms;
    let mut v: Vec<Box<usize>> = Vec::with_capacity(n);
    for i in 0..n
        invariant
            v@.len() == i,
            n <= vstd::std_specs::vec::spec_vec_capacity(&v),
            allocated() <= 1 + i,
    {
        v.push(Box::new(i));
    }
    v
}
```

The leaves of this accounting are the bounds that vstd gives to std functions (`Box::new`
allocates 1, `Vec::push` allocates 1 only when the vector is full, `Vec::with_capacity(0)`
allocates nothing, ...), and the bounds of `external_body` functions, which are trusted like
their other specifications.

## What a bound means

`allocates e` bounds, for one call that **returns normally**, the number of calls to the
allocator that obtain memory (allocate, allocate-zeroed and reallocate, i.e. grow or shrink;
deallocation is not counted) that the Rust *abstract machine* makes, that is, the source program.

It does not bound bytes, peak memory, or calls on paths that unwind.

The compiled program may make fewer calls. The compiler is documented to be free to remove
allocations and to merge them:
* LLVM LangRef (main @932a5ca) allows allocation elision, and allows splitting `realloc` into
  an allocation and a free, one of which may be elided.
* The `core::alloc::GlobalAlloc` docs at rustc 1.100 (`core/src/alloc/global.rs`,
  rust-lang/rust#159720) also allow merging allocations.

No current document either allows or forbids the compiler to *introduce* an allocator call that
the source does not make. A bound is not a claim about such a compiler. The test
`rust_verify_test/tests/alloc_check_runtime.rs` runs verified programs with a counting
`#[global_allocator]` at several optimization levels and compares the calls they actually make
with their verified bounds.

## Drops

Implicit drops (end of scope, temporaries, reassignment, the drop glue of containers) do not
appear as calls, so they cannot be charged where they happen. Instead, `-V alloc-check` requires
that every `Drop::drop` that a checked function may run allocates nothing. The function's
parameter types and the types of every expression in its body over-approximate what it may
drop. For each of these types:

* A user type with a `Drop` impl needs `allocates 0` on its `drop`, and that `drop` must be
  verified with `-V alloc-check`:

  ```rust
  pub struct Handle { pub id: u64 }

  impl Drop for Handle {
      fn drop(&mut self)
          opens_invariants none
          no_unwind
          allocates 0
      {
      }
  }
  ```

  An `external_body` (or `assume_specification`) `drop` is not trusted, even with `allocates 0`.
  Verus accepts the body of such a `drop` without verifying it, and a `drop` is never called
  explicitly, so the claim would silently cover every implicit drop. Only vstd's own are trusted.
* The fields of a type are checked recursively.
* A type whose fields are hidden (`external_body`, or private fields that are not visible from
  here) is accepted only if it is `Copy`, or if it is a std or vstd type whose drop is trusted.
  For std, only a list of types is trusted (for example `Vec`, `Box`, `String`, `HashMap`, their
  iterators, and the iterator adapters). It does not include types such as `BufWriter`, whose
  `drop` flushes and may allocate, or `vec::Splice`, whose `drop` is where `Vec::splice`
  reserves memory. A Copy impl `impl<A: Copy> Copy for W<A>` makes `W<args>` `Copy` only when
  the arguments are `Copy`.
* A type parameter `T` needs the bound `T: Copy` or `T: vstd::alloc_check::AllocFreeDrop`:

  ```rust
  fn consume<T: AllocFreeDrop>(t: T)
      allocates 0
  {
  }

  unsafe impl AllocFreeDrop for Handle {}
  ```

  `AllocFreeDrop` is an `unsafe trait`. An impl is accepted only if dropping the type cannot
  allocate (it passes the drop rule), and every impl of it in the program must be one that
  Verus checks: an impl outside `verus!`, or in a dependency whose `.vir` is not imported, is
  rejected. vstd implements it for the primitive types, references, `Option`, `Result`, tuples,
  `Box`, `Vec`, `String` and others.
* A closure drops its captures. A bounded closure is checked like a function: its captures,
  including other closures it may drop, must pass the drop rule.

### Custom allocators

A container with an allocator other than the global one (`Vec<T, A>`, `Box<T, A>`, `Rc<T, A>`,
...) charges each allocation the cost of the allocator call it makes. Allocations are counted at
the leaves: a call to the global or the system allocator is 1. A custom allocator gets its costs
from the unsafe marker trait `vstd::alloc_check::BoundedAllocator`:

```rust
use std::alloc::{Allocator, AllocError, Global, Layout};
use std::ptr::NonNull;
use vstd::alloc_check::BoundedAllocator;

pub struct Fwd;

unsafe impl Allocator for Fwd {
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        allocates 1
    {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates 0
    {
        #[verifier::trusted_call] {
            unsafe { Global.deallocate(ptr, layout) }
        }
    }
}

unsafe impl AllocFreeDrop for Fwd {}

unsafe impl BoundedAllocator for Fwd {
    open spec fn max_cost() -> int { 1 }
}

fn push_one(v: &mut Vec<u64, Fwd>, x: u64)
    allocates 1
{
    v.push(x);
}
```

`deallocate`, `grow`, `grow_zeroed` and `shrink` are `#[verifier::trusted_only]`. std requires
that the pointer is a live block of this allocator with a fitting layout, and a precondition cannot
say that. So verified code may call them (for any allocator, also through a generic
`A: Allocator`) only inside a
[`#[verifier::trusted_call]`](./reference-attributes.md#verifiertrusted_only-and-verifiertrusted_call)
block, like the forwarding call above. That call is trusted; the rest of the function is still
verified, and a closure made in the block is not trusted. `--no-cheating` rejects the block, so
under it an allocator cannot forward `deallocate` to another allocator.

Verified code frees memory through `vstd::raw_ptr::deallocate` and its `Dealloc` permission
instead (`raw_ptr::allocate` is one allocation, `raw_ptr::deallocate` none). An allocator can do
the same, also under `--no-cheating`. The memory it returns belongs to the caller (std's
containers), so Verus checks that the allocator does not keep the block's permission:

* In the body of a user's `allocate` (or `allocate_zeroed`, `grow`, `grow_zeroed`, `shrink`), a
  block returned in `Ok` must be one whose permission the body gave up with
  `vstd::alloc_check::hand_out(pt, block)` (which consumes the `PointsToRaw` covering exactly the
  block, and returns a receipt `Handout`), or one it got from another allocator (whose memory
  Verus never had a permission for), or from an `external_body` function (trusted, like any
  `external_body`). It must be the last such block of the call. `hand_out` may be called only in
  those bodies, not in a function they call or a closure.
* In the body of `deallocate` (or `grow`, `grow_zeroed`, `shrink`),
  `vstd::alloc_check::reclaim(ptr, layout, receipt)` takes back the permission of the block being
  freed: `ptr` must be that method's `ptr`, it may be called once, and a `grow` or `shrink` that
  returns `Err` must not have called it (the old block is still the caller's). The receipt says
  which block it was (address, length and provenance). `reclaim` rests on std's `Allocator`
  contract: `deallocate` (which verified code cannot call: it is `trusted_only`) receives only a
  live block that this allocator, or an equivalent one, handed out, which the caller no longer
  uses.

* The block must also be big and aligned enough: the `Allocator` declaration's postcondition
  `allocator_block_fits(r, layout)` (`new_layout` for `grow` and `shrink`) says that a block
  returned in `Ok` is at least `layout.size()` long and aligned to `layout.align()`, as std's
  contract says, so a user's impl must show it.
* A user's `grow`, `grow_zeroed` or `shrink` must move the old block's contents into the new one,
  which Verus cannot check (the permissions of raw memory do not say what it holds). So it is
  accepted only as `#[verifier::external_body]` (trusted; `--no-cheating` rejects it); leaving it
  out uses std's default body (`allocate`, copy, `deallocate`), which is safe.

So an allocator that frees:

* `allocate` gets a block from `raw_ptr::allocate(layout.size(), layout.align())`
  (`Layout::size` and `Layout::align` say that the pair is a `valid_layout`), makes the
  `NonNull<[u8]>` it returns with `core::ptr::slice_from_raw_parts_mut` and `NonNull::new`, hands
  it out, and keeps the receipt and the `Dealloc`, with the block's pointer and layout, in state
  it can reach from `&self` (a `LocalInvariant`, or an `AtomicInvariant` for a `Sync` allocator,
  over a `PCell` that records them);
* `deallocate` frees a block only if it finds the address and the layout among them: it reclaims
  the permission with the receipt and calls `raw_ptr::deallocate`; it leaves anything else alone
  (std never passes anything else). A type invariant ties the invariant to the cell, since
  `deallocate` cannot have a precondition.

The test `one_slot_allocator_frees_no_cheating` (`rust_verify_test/tests/alloc_check_custom_allocator.rs`)
is such an allocator, for one block at a time.

The `Allocator` declaration bounds `deallocate` by `allocates 0`, and `allocate`,
`allocate_zeroed`, `grow`, `grow_zeroed` and `shrink` by costs that the marker defines.
`max_cost()` is an upper bound for every call. The per-call costs `allocate_cost(&self, layout)`
(also for `allocate_zeroed`), `grow_cost(&self, ptr, old_layout, new_layout)`,
`grow_zeroed_cost` and `shrink_cost` may depend on the allocator's value and on the arguments.
By default `allocate_cost` is `max_cost()`, and the others are `allocate_cost` of the new layout.
A per-call cost above `max_cost()` is cut down to it. Verus verifies the impl against these
bounds. The methods that the impl does not define run std's default bodies, and each of those
calls `allocate` or `allocate_zeroed` once with the new layout. So the marker may define
`grow_cost`, `grow_zeroed_cost` or `shrink_cost` only if the impl defines `grow`, `grow_zeroed` or
`shrink`.

`Vec<T, A>` and `Box<T, A>` charge the cost of the very call they make. A vector without a buffer
(capacity 0) that grows calls `allocate` instead, and is charged `allocate_cost` of the new
layout; a zero-sized `T` (and `Box::new_in` of one) calls nothing. A `Vec::push` that grows an
existing buffer is charged `grow_cost` with the vector's allocator (`spec_vec_allocator`), its buffer pointer, the
layout of its old capacity, and the layout of the capacity that std's growth policy picks
(`vec_amortized_cap`, the policy of std 1.100). After the growth the vector has exactly that
capacity, and its allocator does not change. An allocator whose cost depends on its
configuration or on the request size can therefore give exact bounds:

```rust
pub struct Chunked { pub limit: usize }

unsafe impl BoundedAllocator for Chunked {
    open spec fn max_cost() -> int { 1 }

    open spec fn allocate_cost(&self, layout: Layout) -> int {
        if spec_layout_size(layout) <= self.limit { 0 } else { 1 }
    }
}

fn push_fits(v: &mut Vec<u64, Chunked>)
    requires
        spec_vec_allocator(&*old(v)).limit == 256,
        old(v)@.len() == 8,
        spec_vec_capacity(&*old(v)) == 8,
    allocates 0
{
    v.push(1); // grows to 16 elements, 128 bytes
}
```

`VecDeque<T, A>`, `HashMap<K, V, S, A>`, `Rc::map` and `Arc::map` charge `allocator_max_cost::<A>()`
instead, because vstd does not name the arguments of their allocator calls. An arena that hands
out memory it already holds can have cost 0, and then using a container with it allocates
nothing.

* The marker impl is accepted only if the allocator's `Allocator` impl is one that Verus checks
  (inside `verus!`). Every marker impl must also be one that Verus checks.
* Dropping a container calls its allocator's `deallocate`. So a container may be dropped only if
  its allocator is the global or the system allocator, or a `BoundedAllocator`. A reference to
  one counts too. A generic allocator needs the bound `A: Allocator + BoundedAllocator`.
  `AllocFreeDrop` is a supertrait of `BoundedAllocator`, so dropping the allocator itself must
  not allocate.
* Cloning a container (and `split_off`) also clones its allocator, at the cost
  `allocator_clone_cost::<A>()`. std's containers also clone their allocator where Verus does
  not see it: dropping a `BTreeMap` (or its `IntoIter`) clones it once for every node it frees.
  So the `Clone` impls of a `BoundedAllocator` must be ones that Verus checks, bounded by
  `allocates 0`, and must not change the allocator heap (next section). (So `#[derive(Clone)]` on
  an allocator is rejected: the derived impl is not checked by Verus; write the impl in `verus!`.)
  `Allocator`'s contract
  already requires a clone to behave like the same allocator. The cost is therefore 0 for a
  `BoundedAllocator`, as for the global allocator and for references. For other allocators it is
  uninterpreted.
* With `BoundedAllocator` alone, a cost depends only on the allocator's value and the arguments,
  not on its mutable state (behind `&self`, which the methods take). The next section lifts this.

### Allocators with a state

A pool that first hands out blocks it already holds, or an arena that runs out, costs
different amounts depending on its state. `vstd::alloc_heap::StatefulAllocator` (on top of
`BoundedAllocator`) gives the state's type, a preorder on it ("at least as good as"), the cost
of `allocate` in a state (`allocate_cost_at`) and the state after it (`allocate_next`):

```rust
pub struct Free(pub nat);          // blocks left; more is better

impl Preorder for Free {
    open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
    proof fn le_refl(a: Self) {}
    proof fn le_trans(a: Self, b: Self, c: Self) {}
}

unsafe impl StatefulAllocator for Pool {
    type State = Free;
    open spec fn loc(&self) -> Loc { self.reg@.loc() }
    proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) { self.reg.borrow() }
    open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
        if s.0 > 0 { 0 } else { 1 }
    }
    open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
        if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
    }
}

fn two(p: &Pool, l: Layout)
    requires allocator_state(p).0 >= 2,
    ensures allocator_state(p).0 == old_allocator_state(p).0 - 2,
    allocates 0
{
    let _ = p.allocate(l);
    let _ = p.allocate(l);
}
```

Verus keeps, per thread, a ghost heap of lower bounds of these states. Specifications read it
with `allocator_state(a)` (in `ensures`, after the call; in `requires` and in a body, the
current state) and `old_allocator_state(a)` (when the function was called, which is the only
form an `allocates` bound may use). A call `a.allocate(layout)` is charged
`allocate_cost_at(allocator_state(a), layout)` (cut down to `max_cost()`) and moves the state to
`allocate_next`. The impl's `allocate` is verified against the same two facts.

* The implementation keeps the actual state in an `AllocAuth<S>` (in its own invariant), made by
  `AllocAuth::register(s)`, which also returns the `Registered<S>` witness the allocator must keep
  (`witness`). `AllocAuth::step` moves the actual state and the heap's lower bound together
  (allocation); `AllocAuth::raise` moves the actual state up alone (deallocation).
* The heap holds lower bounds, not the states: `deallocate` runs where Verus does not see it
  (when a container is dropped), so it may only raise the state. A `deallocate` or `Drop::drop`
  that may change the heap is rejected.
* `Registered` is neither `Send` nor `Sync`, so neither is an allocator that keeps it: the state
  and its lower bound stay in one thread. This rests on the allocator not implementing `Send` or
  `Sync` itself: an `unsafe impl Send`/`Sync` written outside `verus!` is not checked by Verus (as
  with any `unsafe impl` of an auto trait), and would let the state move to another thread.
* A function whose specification mentions the heap passes it on to its callers. After a call to
  any other function that may change the heap (it allocates from an allocator with a state, or
  calls code that Verus cannot see the effect of: a closure, a function of a crate verified
  without Verus's heap analysis), the states are unknown, and then cost `max_cost()`. The
  analysis is per instantiation: a generic function that may reach an allocator only through its
  type parameter `A` (`v.push(1)` on a `Vec<u8, A>`) keeps the states when called with
  `A = Global`. A proof
  function that changes the heap must say how in its `ensures`.
* An `external_body` function or an `assume_specification` is trusted, like its `allocates`
  bound: it may change the heap only through its type arguments (a type parameter, a closure,
  a type of the user's crate). So a std call instantiated with a user type (`Vec<MyStruct>::push`)
  also makes the states unknown.
* `grow` (and `grow_zeroed`) and `shrink` move the state too, by `grow_cost_at`/`grow_next` and
  `shrink_cost_at`/`shrink_next`. By default these are what std's default bodies do (one
  `allocate` with the new layout); an allocator may change them only for methods its `Allocator`
  impl defines. A call through `&A` is a call of `A`'s method.
* The containers' specifications say what they do to the heap:
  * `Vec`: every operation that allocates (`with_capacity_in`, `reserve`, `try_reserve`,
    `try_reserve_exact`, `push`, `insert`, `append`, `extend_from_slice`, `resize`) costs the
    allocator call's cost at its state, and moves the state as the allocator says (not at all for
    the global allocator, or when the vector has room); the other operations keep the heap.
    `Box::new_in` likewise.
  * `VecDeque` (with `new_in` and `with_capacity_in`), `HashMap` and `HashSet`: their allocating
    operations make at most one allocator call (`allocator_some_call_heap_in`), with the
    stateless cost; the others keep the heap. `BTreeMap`/`BTreeSet` reads and removals keep it.
  * The heap is unknown after: operations that clone the allocator (`clone`, `split_off`) or call
    a closure (`Box`/`Rc`/`Arc::map`), the trait methods (`Deref`, `Index`, `IntoIterator`), and
    `BTreeMap`/`BTreeSet` inserts (which have no `allocates` bound).
  * A container instantiated with an element type through which user code may reach an
    allocator with a state (`Vec<Vec<u8, &Pool>>`: `T::clone`, drops) does not describe the heap:
    it is unknown after the call.
* A closure's own specification may mention the heap: in its `requires` and body,
  `allocator_state(a)` is the heap at that point of the call, in its `ensures` the heap when it
  returns, and `old_allocator_state(a)` the heap when it was called. Calling the closure value
  (`f(x)`) uses its specification at the caller's heap. Its `allocates` bound, like a function's,
  is evaluated when it is called, so it may use only the `old_` forms:

  ```rust
  let f = |u: u8| -> (r: Result<NonNull<[u8]>, AllocError>)
      allocates if old_allocator_state(p).0 > 0 { 0int } else { 1int }
  {
      p.allocate(l)
  };
  ```

  Such a closure (one whose `requires`, `ensures` or `allocates` mentions the heap) cannot be
  passed where only `call_requires(f, args)` is known (generic code): that means "at every
  heap". The same holds for a function whose `allocates` bound mentions the heap, used as a
  value (`let g = take; g(p, l)` works, passing `take` to generic code does not).

## Callbacks, closures and traits

A call through a generic function value is charged `call_allocates(f, args)`, the bound of
whatever `f` turns out to be. A caller's bound can mention it:

```rust
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64
    requires f.requires((x,)),
    allocates call_allocates(*f, (x,))
{
    f(x)
}

fn use_apply() -> u64
    allocates 0
{
    let half = |y: u64| -> (r: u64) allocates 0 { y / 2 };
    apply(&half, 7)
}
```

For a closure with an `allocates` bound, or a function, `call_allocates` is that bound. The
vstd specifications of std functions that call user code charge those calls the same way (for
example `Vec::clone` charges `T::clone` once per element, and `HashMap::insert` charges the
`Hash`/`Eq` callbacks through `hash_ops_cost(m, k)`).

A bound on a trait method declaration bounds every implementation:

```rust
pub trait Shape {
    fn area(&self) -> u64 allocates 0;
}

fn total<S: Shape>(a: &S, b: &S) -> u64
    allocates 0
{
    let x = a.area();
    let y = b.area();
    if x < 1000 && y < 1000 { x + y } else { 0 }
}
```

Each impl is checked against the declaration's bound. Consequently:

* Every impl of such a method must be checked by Verus. An impl in a crate that was not verified
  with `-V alloc-check`, an impl outside `verus!`, or one in a dependency whose `.vir` is not
  imported is rejected. This applies even if this crate never uses that impl.
* The methods of a user `external_trait_specification` cannot have bounds, because the trait's
  implementations and provided methods are not checked by Verus. vstd's bounds on std traits are
  the exception: each is a per-implementation term (`iter_next_cost`, `iter_adapter_cost`, ...)
  that is constrained only for std's own types. For example, `Iterator::rev` costs
  `iter_adapter_cost::<Self>()`, which is 0 for std's iterators. For a generic iterator `I`, it
  is 0 only under `iter_aux_alloc_free::<I>()`.
* With `-V check-api-safety`, a bound on a method of a public, safe trait is rejected:
  unverified safe code could implement the trait without staying within the bound. (This is the
  same rule as for `requires`, `no_unwind` and `opens_invariants`.)

### Bound specifications: `T: Tr with { .. }`

A function's type parameter can specify the methods of its bound, instead of a marker trait:

```rust
fn dup<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }>(x: &T) -> (r: (T, T))
    allocates 0
{
    (x.clone(), x.clone())
}
```

Inside the function, a call of the method gets the bound's specification; a caller must show
that the type it instantiates `T` with meets it. A method's specification may have `requires`
(which the impl must accept), `ensures` (which the impl must give) and `allocates`.
`fn drop allocates 0;` says that dropping a `T` allocates nothing; Verus checks it against the
instantiation's drop glue, so the type that instantiates `T` needs no `AllocFreeDrop` impl. The block stands for
`requires` clauses (`call_requires`, `call_ensures`, `call_allocates`). Besides a function's
type parameters, it may appear in a `where` clause (`where T: Clone with { .. }`, also for a type
that is not a parameter), on an inherent impl block (every exec and proof method gets it), and
on a struct's type parameter (every inherent impl block of the struct in the same `verus!`
block gets it, for the type it instantiates the parameter with). It is rejected on a trait impl,
whose methods cannot have `requires`.

## Fully in-place functions: `#[verifier::fip]`

The FP² paper (Lorenzen, Leijen and Swierstra, ICFP 2023) distinguishes functions that run in
place. In its terms, an `allocates n` bound is the heap part of `fbip(n)`: at most `n`
allocations, with any number of deallocations. `#[verifier::fip]` is `fip(n)`: the function also
never deallocates memory on a normal return. Without an `allocates` bound it is `fip`, which
means no allocation either (`allocates 0`). The attribute needs `-V alloc-check`, and a function
may carry only one of `#[verifier::fip]` and `#[verifier::fip(strict)]`.

```rust
pub struct Node { pub val: u64, pub next: Option<Box<Node>> }

#[verifier::fip]
fn halve(mut b: Box<Node>) -> (r: Box<Node>) {
    b.val = b.val / 2;
    b
}

#[verifier::fip]
fn push_spare(v: &mut Vec<u64>)
    requires
        old(v)@.len() < spec_vec_capacity(&*old(v)),
{
    v.push(1);
}
```

Two things are checked:

* **Calls.** A callee must be `#[verifier::fip]` itself, or have a deallocation condition, which
  the caller must show to be false. A specification without a verified body states this
  condition as `allocates deallocates_when(n, c)`: the function allocates at most `n` and may
  deallocate only when `c` holds (evaluated at entry). For example, `Vec::push` may deallocate
  when it has to grow an existing buffer. Growing reallocates, which frees the old block. A
  vector without a buffer grows by calling only its allocator's `allocate`, which does not
  deallocate for the global and the system allocator. For any other allocator, `allocate` is
  user code (see below). Calls of trait methods that do not resolve to an impl (generic calls),
  and calls of closures, are rejected.
* **Drops.** The compiler inserts drops that do not appear in the source. They are checked on
  the MIR of the compiled program, after ghost code is erased and after drop elaboration. A value
  may be dropped on a path that returns normally only if its type has no drop glue at all, or
  implements the unsafe marker trait `vstd::alloc_check::NoDeallocDrop`. A generic type needs
  the bound `T: NoDeallocDrop`. Moving the contents out of a `Box` frees the box. To stay in
  place, reuse the box instead (`*b = ..`, or field updates).

`core::mem::forget` does not deallocate, so a fip function may forget a value it owns. That leaks
the value's memory: unlike FP²'s linear discipline, `#[verifier::fip]` only says that nothing is
freed, not that every owned cell is reused.

An `unsafe impl NoDeallocDrop for X` is accepted only if `X` is not a `Box`, its own `Drop` (if
any) is `#[verifier::fip]`, and each of its fields has no drop glue or is `NoDeallocDrop`. The
impls of this crate are checked when it is compiled; an impl of another crate is accepted only if
that crate was verified and compiled with `-V alloc-check` and imported with its library file
(so its compilation checked it), and rejected otherwise.

A container calls its allocator's methods inside std's code, so a fip function may use std or
vstd code with an allocator other than the global or the system allocator (`Vec<u8, A>::push`,
`Vec::with_capacity_in(n, a)`) only if the allocator implements the unsafe marker trait
`vstd::alloc_check::FipAllocator`. A generic allocator needs the bound `A: FipAllocator`. An
`unsafe impl FipAllocator for X` is accepted only if `X`'s `allocate`, its `allocate_zeroed` (if
its `Allocator` impl defines one) and its `Clone::clone` (if any) are `#[verifier::fip]`
functions of the same crate. `Allocator`, `BoundedAllocator` and `NoDeallocDrop` are supertraits.
A `#[verifier::fip(strict)]` function needs `FipStrictAllocator` instead, whose methods must be
`#[verifier::fip(strict)]`.

Paths that unwind are not covered, as for `allocates`. The drop check runs in the compilation
step of Verus, so `--no-lifetime` and `--no-erasure-check` reject `#[verifier::fip]` functions.

### Constant stack space: `#[verifier::fip(strict)]`

FP²'s `fip` also requires constant stack space. `#[verifier::fip(strict)]` adds this to
`#[verifier::fip]`. Rust does not guarantee that a call in tail position replaces the caller's
frame. It is not done at `opt-level=0`, and not when a drop is pending after the call. A strict
function therefore recurses only through `become` (`#![feature(explicit_tail_calls)]`). rustc
guarantees that a `become` call replaces the frame, or rejects the program.

```rust
#[verifier::fip(strict)]
fn sum(n: u64, acc: u64) -> (r: u64)
    decreases n
{
    if n == 0 { acc } else { become sum(n - 1, acc.wrapping_add(n)) }
}
```

The calls of a strict function are checked on the MIR of the compiled program, after drop
elaboration. This includes the destructors that its drops run.

* A call may go to another strict function, or to std or vstd. Their functions do not call back
  into the caller's code, because the calls that could do so (through callbacks) are rejected by
  the checks above. A function of another crate may be called (also as the target of `become`)
  only if it is strict and its crate was verified and compiled with `-V alloc-check` and
  imported with its library file (see "Libraries and other crates"): that compilation checked it
  and everything it reaches. It can call back into this crate only through a user allocator it is
  instantiated with (`A: FipStrictAllocator`, whose strict methods are this crate's): such a call
  counts as using a user allocator, so the allocator's methods may not reach it (below). Calls of
  other functions of other crates, and calls whose callee is not known (generic calls, function
  values), are rejected.
* Destructors count as calls: those that the function's drops run, and those of the types that
  a std or vstd call is instantiated with (std may drop such values inside the call, as
  `Vec::<T>::clear` does). The destructor of another crate's type is accepted on the same terms
  as its functions (a strict `Drop::drop` of a crate verified and compiled with `-V alloc-check`),
  and rejected otherwise. A drop (or such a call) whose destructors are not known here, because
  it involves a type parameter, an associated or opaque type, or `dyn`, is rejected; a `Copy`
  bound rules out a destructor.
* The std functions whose vstd specification is marked `#[verifier::alloc_check_skip_drops]`
  drop no value of their type arguments, so a call of one runs no destructor of them, and may be
  instantiated with a type parameter whatever its bounds. These are `mem::swap`, `mem::replace`,
  the slice views (`len`, `first`, `last`, `get`, `get_unchecked`, indexing, `swap`, `split_at`,
  `split_first`, `split_last` and their `_mut`, `_checked` and `_unchecked` variants), and
  `Vec`'s `new`, `new_in`, `len`, `capacity`, `is_empty`, `pop`, `remove`, `swap_remove`,
  `as_slice`, `as_mut_slice`, `deref`, `deref_mut` and indexing. (`mem::take` is not among
  them: it runs `T::default`.) The mark is trusted, like `external_body`, and is accepted only in
  vstd.
* A cycle of calls between strict functions must consist of `become` calls only. A non-tail call
  adds a frame, so a cycle through one grows the stack.

`-V fip-lint` (which does not need `-V alloc-check`) warns about recursion that grows the stack
and suggests how to avoid it:

* A recursive call in tail position that is not a tail call. The warning says whether a drop is
  pending after the call, and whether the signatures allow `become`.
* Recursion modulo a constructor (TRMC), such as `List::Cons(n, Box::new(range(n - 1)))`. The
  call is not a tail call, because its result becomes a field of the value that is returned. A
  loop can build the same value in constant stack space. It keeps a `&mut` hole (the field that
  is still to be filled), stores each new value into it, and then moves the hole into the new
  value's field. This is destination-passing style, as in Leijen and Lorenzen's "Tail Recursion
  Modulo Context".

For recursion modulo a constructor, the warning comes with the rewrite into a loop as a
suggestion, which an editor (verus-analyzer) offers as a quick fix. `-V fip-lint=fix` writes the
rewrite to the source files instead. A rewrite is kept only if the crate still verifies: after a
successful verification, Verus writes each rewrite, verifies the crate again, and restores the
file if that fails. So nothing about the rewrite is trusted. For that reason `=fix` cannot be
combined with options that verify only part of the crate or skip checks (`--no-verify`,
`--verify-root`, `--verify-module`, `--verify-only-module`, `--verify-function`, `--no-lifetime`,
`--no-erasure-check`, `--no-trait-conflicts`, `-V allow-inline-air`, `-V ignore-unexpected-smt`).
Each trial only verifies (without `--export`, `--compile`, `-o`, `--out-dir` and `--emit`); if a
rewrite is kept, the run is repeated with all the options, so the outputs describe the rewritten
files. A file is rewritten in place: through a symbolic link, keeping hard links and the file's
mode. A file that cannot be written, or that has a byte-order mark or CRLF line endings, is left
alone. While it runs, the originals are kept in `<file>.fip-lint-orig` (next to the file a link
points to), listed in a journal `.fip-lint-journal` next to the crate root; SIGINT, SIGTERM or
SIGHUP restore them. If the process is killed outright, the backups and the journal stay, and the
next `=fix` run refuses to start (and lists the backups, also those of files outside the crate
root's directory) until they are restored or deleted. The journal also keeps two `=fix` runs on
one crate apart; other tools (an editor, `cargo build`) can still see a trial while it runs.

The rewrite works on a strongly connected component of the call graph, so mutual recursion is
rewritten too. Every recursive call in the component must be either a tail call or the only
recursive call inside a constructor in tail position (possibly through `Box::new` and nested
constructors).

* A single function becomes a loop in its own body.
* Several functions share one loop in a new helper function. Its state is an enum with one
  variant per function, which holds that function's arguments and its hole, so the functions can
  return different types. Each function starts the loop in its own state.

The rewritten code evaluates the constructor's fields and the call's arguments in the same order
as the original. A field after the recursive call is evaluated after the call returns in the
original, but before the next iteration in the loop, so the rewrite is offered only when such
fields are literals or names. Likewise, a value whose drop runs user code (a `Drop` impl outside
std, or a type parameter) is dropped at a different time in the loop, so a function with a
binding or an expression (a temporary: a `match` scrutinee, an argument) of such a type is not
rewritten. The loop invariant states two things:

* If the hole's final value (`*final(hole)`) satisfies the `ensures` for the current arguments,
  then the result satisfies the `ensures` for the original arguments.
* With `allocates`, the allocations so far plus the bound for the current arguments stay within
  the original bound.

Each value is written into the hole with `core::mem::forget(core::mem::replace(hole, value))`.
The replaced value is a placeholder (a variant without fields), so forgetting it leaks nothing,
and a `#[verifier::fip]` function stays `#[verifier::fip]`. After the rewrite, the functions can be
marked `#[verifier::fip(strict)]`. The test `fip_trmc_fix_*` rewrites recursion that overflows the
stack 10^6 levels deep, and runs the result at `opt-level=0` and `3`.

The rewrite is not offered, and the warning says why, when:

* a function is not a free function (for example, it is a method);
* a parameter is `&mut`, ghost or tracked, or is a pattern rather than a name;
* the body binds a parameter's name again (`let mut k = k + 1;`): the loop assigns the
  parameters by name. This is decided by name, so it also covers bindings that would be harmless:
  a `match` arm binding the same name, or a local of the same name inside a macro;
* the function's source mentions a name starting with `__trmc`, which the rewrite uses for its own
  names;
* the function comes from a macro expansion;
* a constructor field after the recursive call is not a literal or a name, or the drop of a
  binding or a temporary runs user code (see above). A value of a type parameter counts, even if
  nothing of that type is pending when the recursive call returns (`fn f<T>(l: G<T>)`);
* a function has no `decreases` (it becomes the loop's), uses `returns`, or returns early with `?`;
* the return type is not an enum with a variant without fields;
* several functions have different generic parameters, have more than one `decreases` expression
  each, or do not all have `allocates`.

## Libraries and other crates

A bound in an imported crate is trusted only if that crate was verified with `-V alloc-check`,
completely (not with `--no-verify` or a `--verify-*` filter), and successfully:

* The exported `.vir` file is first written with its bounds marked as unchecked. It is written
  again with them marked as checked only after both verification and compilation succeed. So a
  library must be built with `--compile` (as `cargo verus` and the vstd build do) for its bounds
  to be usable by other crates.
* The `.vir` file records the SVH of the compiled crate. An importer rejects a `.vir` whose
  crate is linked in a different build, for example an older version of the source.
* Dependencies named `std`, `core` or `alloc` must come from the toolchain's sysroot, and there
  must be only one of each. An imported crate named `vstd` must be one that was verified as
  vstd, built together with the linked vstd.
* A crate being verified with `-V alloc-check` cannot itself be named `std`, `core` or
  `alloc`, or `vstd` unless it is vstd.

## `-V alloc-check-strict`

`-V alloc-check-strict` does what `-V alloc-check` does. In addition, every function with an
`allocates` bound must be `no_unwind`, so that no panic path exists, and closures cannot have
bounds. vstd's specifications of allocating std functions (`Box::new`, `Vec::push`, ...) are not
`no_unwind`: capacity overflow is a `panic!` that can unwind. So in practice, a function that
allocates cannot pass the strict mode yet.

## Trust and limitations

What `-V alloc-check` trusts:
* the bounds in vstd's specifications of std functions, and the design of vstd's bounds on std
  trait methods described above;
* the `deallocates_when` conditions in vstd's specifications (for `#[verifier::fip]`), and, for
  `#[verifier::fip(strict)]`, that std's and vstd's functions use bounded stack space and that
  rustc implements `become` as specified (an incomplete feature of the pinned toolchain; the test
  `fip_strict_tail_calls_*` runs a `become` recursion 10^8 levels deep at `opt-level=0` and `3`);
* std's `Allocator` contract, for `vstd::alloc_check::reclaim`: the block that `deallocate` (or
  `grow`, `shrink`) receives is a live block that this allocator handed out (see "Custom
  allocators");
* calls inside `#[verifier::trusted_call]` blocks (such as an allocator's forwarding
  `deallocate`). `--no-cheating` applies only to the crate being verified: the blocks (and the
  `external_body` functions) of a dependency verified without it are trusted all the same, and a
  `.vir` does not record whether it was;
* `external_body` functions other than `drop`, and `external_body` types (their hidden fields'
  drops are trusted only for std types that vstd declares);
* the crates `std`, `core`, `alloc`, `vstd` and `verus_builtin`: their functions reach user code
  only through their type arguments, and use bounded stack space. They are recognized by name,
  and a crate of one of these names is accepted only if it is the real one: `std`, `core` and
  `alloc` from the toolchain's sysroot, each the only crate of its name; `vstd` and
  `verus_builtin` from the files that Verus itself gives with `--extern vstd=..` and
  `--extern verus_builtin=..` (with `--no-vstd` no dependency may be named `vstd`), and an
  imported `vstd` must also have been verified as vstd. Verus gives these files from its own
  installation; with `--is-core`, `--import-via-core` or in its internal test mode it does not,
  and the ones on the command line are then trusted. A crate being verified with -V alloc-check
  cannot take one of these names, except that a crate verified with `--is-vstd` is `vstd` (it
  then trusts its own `external_body` drops and opaque types; `--no-cheating` rejects
  `--is-vstd`);
* the toolchain's std (its trusted drops and opaque types).

Known limitations, all of which make Verus reject programs or give weaker bounds (they are not
unsound):
* cloning a container whose allocator is neither the global allocator, a reference nor a
  `BoundedAllocator`, and allocators that forward to an allocator they hold (`Box`, `Rc`, `Arc`
  and `Pin` used as allocators): their cost is an uninterpreted term
  (`allocator_clone_cost::<A>()`, `allocator_max_cost::<A>()`), so only a bound that names it
  verifies;
* `dyn` values and opaque `impl Trait` values being dropped;
* projected types in drop glue (for example `Cow`);
* a closure that captures one field of a struct is checked as if it captured the whole struct;
* unchecked implementations of bounded trait methods anywhere in the program.

`catch_unwind` is rejected inside checked functions. A caught panic lets execution continue
after allocations on the unwinding path, and `allocates` does not count those.
