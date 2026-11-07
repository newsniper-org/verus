# Allocation bounds (`allocates`)

> **Fork extension, experimental.** The `allocates` clause and the `-V alloc-check` /
> `-V alloc-check-strict` options exist in this fork of Verus only. A Korean version of this
> page is [here](./reference-allocates.ko.md).

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
* The `core::alloc::GlobalAlloc` docs at rustc 1.99.1 (`core/src/alloc/global.rs`,
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
        unsafe { Global.deallocate(ptr, layout) }
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

`Vec<T, A>` and `Box<T, A>` charge the cost of the very call they make. A `Vec::push` that grows
is charged `grow_cost` with the vector's allocator (`spec_vec_allocator`), its buffer pointer, the
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
  `allocator_clone_cost::<A>()`. That cost is 0 for the global allocator and for references.
  For other allocators it is uninterpreted.
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
  and its lower bound stay in one thread.
* A function whose specification mentions the heap passes it on to its callers. After a call to
  any other function that may change the heap (it allocates from an allocator with a state, or
  calls code that Verus cannot see the effect of: a trait method on a type parameter, a closure,
  a function of another crate), the states are unknown, and then cost `max_cost()`. A proof
  function that changes the heap must say how in its `ensures`.
* An `external_body` function or an `assume_specification` is trusted, like its `allocates`
  bound: it may change the heap only through its type arguments (a type parameter, a closure,
  a type of the user's crate). So a std call instantiated with a user type (`Vec<MyStruct>::push`)
  also makes the states unknown.
* Not yet: `grow` and `shrink` of an allocator with a state are charged their stateless costs
  and leave the states unknown; the containers' specifications do not name the states.

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

## Fully in-place functions: `#[verifier::fip]`

The FP² paper (Lorenzen, Leijen and Swierstra, ICFP 2023) distinguishes functions that run in
place. In its terms, an `allocates n` bound is the heap part of `fbip(n)`: at most `n`
allocations, with any number of deallocations. `#[verifier::fip]` is `fip(n)`: the function also
never deallocates memory on a normal return. Without an `allocates` bound it is `fip`, which
means no allocation either (`allocates 0`).

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
  vector without a buffer can grow without deallocating. Calls of trait methods that do not
  resolve to an impl (generic calls), and calls of closures, are rejected.
* **Drops.** The compiler inserts drops that do not appear in the source. They are checked on
  the MIR of the compiled program, after ghost code is erased and after drop elaboration. A value
  may be dropped on a path that returns normally only if its type has no drop glue at all, or
  implements the unsafe marker trait `vstd::alloc_check::NoDeallocDrop`. A generic type needs
  the bound `T: NoDeallocDrop`. Moving the contents out of a `Box` frees the box. To stay in
  place, reuse the box instead (`*b = ..`, or field updates).

An `unsafe impl NoDeallocDrop for X` is accepted only if `X` is not a `Box`, its own `Drop` (if
any) is `#[verifier::fip]`, and each of its fields has no drop glue or is `NoDeallocDrop`. Every
impl in the program is checked, whichever crate it is in.

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
  the checks above. Calls of functions of other crates, and calls whose callee is not known
  (generic calls, function values), are rejected.
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
file if that fails. So nothing about the rewrite is trusted.

The rewrite works on a strongly connected component of the call graph, so mutual recursion is
rewritten too. Every recursive call in the component must be either a tail call or the only
recursive call inside a constructor in tail position (possibly through `Box::new` and nested
constructors).

* A single function becomes a loop in its own body.
* Several functions share one loop in a new helper function. Its state is an enum with one
  variant per function, which holds that function's arguments and its hole, so the functions can
  return different types. Each function starts the loop in its own state.

The rewritten code evaluates the constructor's fields and the call's arguments in the same order
as the original. The loop invariant states two things:

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
* `external_body` functions other than `drop`;
* the toolchain's std (its trusted drops and opaque types).

Known limitations, all of which make Verus reject programs (they are not unsound):
* cloning a container whose allocator is neither the global allocator nor a reference, and
  allocators that forward to an allocator they hold (`Box`, `Rc`, `Arc` and `Pin` used as
  allocators);
* `dyn` values and opaque `impl Trait` values being dropped;
* projected types in drop glue (for example `Cow`);
* a closure that captures one field of a struct is checked as if it captured the whole struct;
* unchecked implementations of bounded trait methods anywhere in the program.

`catch_unwind` is rejected inside checked functions. A caught panic lets execution continue
after allocations on the unwinding path, and `allocates` does not count those.
