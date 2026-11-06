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
* A cost cannot depend on the allocator's mutable state (behind `&self`, which the methods take),
  only on its value and the arguments.

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
