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
appear as calls. For allocations they are not charged where they happen (their deallocations
are: see "Deallocation bounds"). Instead, `-V alloc-check` requires
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
* A `dyn` value's destructors are not known, so a function may not drop one (a `Box<dyn Tr>`,
  or a value that holds one). Which values it drops is checked on the compiled program: a
  `Box<dyn Tr>` that is only moved (returned, or passed on) is fine. A std call instantiated
  with such a type is rejected unless std drops no value of its type arguments there (see
  "Callbacks from other crates"). With `--no-lifetime` or `--no-erasure-check`, which skip the
  compiled program, the parameter and expression types are checked instead (any `dyn` is
  rejected). A closure with an `allocates` bound may not mention a `dyn` value at all yet.

### Custom allocators

An allocator (`core::alloc::Allocator`) is the runtime, as the memory manager is in FP²:
`-V alloc-check` counts the program's calls to an allocator, not what the allocator does.
Whatever the allocator:

* `allocate` and `allocate_zeroed` are one allocation each, and free nothing;
* `grow`, `grow_zeroed` and `shrink` are one allocation each and may free (they may move the
  block);
* `deallocate` allocates nothing and frees.

So a `Vec::push` that grows is 1 for any allocator (a vector without a buffer calls `allocate`,
one with a buffer `grow`), `Box::new_in` is 1 (0 for a zero-sized type, which calls nothing), and
an arena that hands out memory it already holds is still 1 per call: the call is the program's.

The allocator's own code (its `Allocator`, `Clone` and `Drop` impls) is not checked against
`allocates`, `#[verifier::fip]` or the drop rule: what it allocates (from the global allocator or
another one), frees, or uses of the stack is not counted. So:

* An allocator need not be inside `verus!`, nor its crate be verified with `-V alloc-check`. (If
  it is inside `verus!`, Verus still verifies the rest of it: its `ensures`, below.)
* Dropping a container calls its allocator's `deallocate` and drops the allocator, so a bounded
  function may drop a container with any allocator. (A fip function still may not: freeing its
  buffer is the program's deallocation.)
* Cloning a container (and `split_off`) clones its allocator, which is not counted; neither are
  the clones that std's containers make where Verus does not see them (dropping a `BTreeMap`
  clones its allocator for every node it frees). A call `a.clone()` of an allocator is 0.
* A fip or strict function may use any allocator, also a generic `A: Allocator`.

```rust
use std::alloc::{Allocator, AllocError, Global, Layout};
use std::ptr::NonNull;

pub struct Twice;

unsafe impl Allocator for Twice {
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
        let _ = Global.allocate(layout); // the allocator's own: not counted
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) { }
}

fn push_one(v: &mut Vec<u64, Twice>, x: u64)
    allocates if old(v)@.len() == spec_vec_capacity(&*old(v)) { 1int } else { 0int }
{
    v.push(x);
}
```

A bound on a function that uses a custom allocator therefore says nothing about how often that
allocator calls the global allocator: it counts calls into allocators (see "Trust and
limitations").

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

### Allocators of their own API: `encapsulates alloc(a, d)`

An allocator that does not implement `core::alloc::Allocator` (a pool or a slab with its own
`alloc` and `free`) is code that Verus checks like any other: `allocates 0` holds for a body that
only bumps a counter, although the program counts the call as an allocation. Such a function is
marked with `encapsulates alloc(a, d)`: each call counts as `a` allocations and `d`
deallocations (`a` and `d` are `nat`; they may depend on the arguments):

```rust
pub struct Pool { /* .. */ }

impl Pool {
    fn alloc(&mut self) -> (r: Slot) encapsulates alloc(1, 0) { /* .. */ }
    fn free(&mut self, s: Slot) encapsulates alloc(0, 1) { /* .. */ }
    fn release_many(&mut self, k: u64) encapsulates alloc(0, if k > 0 { 1 } else { 0 }) { /* .. */ }
}

fn two(p: &mut Pool) -> (Slot, Slot)
    allocates 2
{
    (p.alloc(), p.alloc())
}
```

* A caller is charged `a` allocations and `d` deallocations (the function's `allocates` is `a`
  and its `deallocates` is `d`), and the call may free memory where `d > 0` (so a fip function may
  make the call only where it shows `d == 0`). `call_allocations`/`f.allocations(..)` and
  `call_deallocations`/`f.deallocations(..)` are `a` and `d`; `call_allocates`/`f.allocates(..)`
  and `call_deallocates`/`f.deallocates(..)` are `a > 0` and `d > 0`.
* The body is the runtime's, as an `Allocator`'s is: what it allocates, frees or uses of the stack
  is not checked, so it may refill the pool from the global allocator. Its `ensures` are verified
  as usual. A strict function may call it as a leaf.
* It cannot be combined with `allocates` or `#[verifier::fip]`, and it is not allowed on spec and
  proof functions or on a trait method declaration. On an implementation of a trait method with a
  bound or a condition, `a` must stay within the bound and `d > 0` within the condition (checked
  on entry, for every input satisfying the `requires`; `d` must be 0 for a `#[verifier::fip]`
  declaration, whose implementations must be fip).
* It also works on `assume_specification`, for an allocator in another language:
  `pub assume_specification[ ffi_alloc ](n: usize) -> *mut u8 encapsulates alloc(1, 0);`.
* It is trusted like an `Allocator` impl: a function that claims `alloc(0, 0)` but allocates
  hides those allocations (see "Trust and limitations").

## Callbacks, closures and traits

A call through a generic function value is charged `call_allocations(f, args)`, the bound of
whatever `f` turns out to be. A caller's bound can mention it:

```rust
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64
    requires f.requires((x,)),
    allocates call_allocations(*f, (x,))
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

For a closure with an `allocates` bound, or a function, `call_allocations` is that bound, and
`call_allocates(f, args)` (a `bool`: may the call allocate) is whether it is positive (`c` for
`allocates allocates_when(a, c)`, below); a positive count implies it, so a generic caller that
requires `!f.allocates(x)` is charged 0 for the call. The
vstd specifications of std functions that call user code charge those calls the same way (for
example `Vec::clone` charges `T::clone` once per element, and `HashMap::insert` charges the
`Hash`/`Eq` callbacks through `hash_ops_cost(m, k)`).

`call_deallocations(f, args)` (the count) and `call_deallocates(f, args)` (may the call
deallocate) are the same for deallocations (see "Deallocation bounds" below): 0 and `false` for a
`#[verifier::fip]` function, the `deallocates` bound and whether it is positive (or the condition
`c` of `deallocates_when(d, c)`) otherwise, and, for a trait method whose declaration has a bound,
at most that (for every implementation). In ghost code inside `verus!` (specifications,
`assert`, ...), `f.allocations(args)`, `f.allocates(args)`, `f.deallocations(args)` and
`f.deallocates(args)` are `call_allocations(f, (args,))` and so on (exec code keeps methods of
those names). So a specification that forwards to another function can pass on all of them, also
a condition that holds only for some arguments:

```rust
#[verifier::external_body]
fn shrink_if_big(x: u64) -> (r: u64)
    allocates 0
    deallocates deallocates_when(1int, x > 5)
{ x }

#[verifier::external_body]
fn outer(x: u64) -> (r: u64)
    allocates shrink_if_big.allocations(x)
    deallocates deallocates_when(shrink_if_big.deallocations(x), shrink_if_big.deallocates(x))
{ shrink_if_big(x) }

#[verifier::fip]
fn small() -> (r: u64) {
    outer(3) // fine: `shrink_if_big.deallocates(3)` is false
}
```

vstd's specifications of std's blanket `Into` (and `TryInto`, `TryFrom` through `Into`) forward
this way to the `From` impl they call.

A call of a function value has the condition `f.deallocates(x)` in the same way, so a fip function
can call a closure marked `#[verifier::fip]` (whose `call_deallocates` is `false`), or a generic
`f` whose caller shows the condition false:

```rust
#[verifier::fip]
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> (r: u64)
    requires
        f.requires((x,)),
        !(*f).deallocates(x),
    allocates
        (*f).allocations(x),
{
    f(x)
}

#[verifier::fip]
fn halve_seven() -> (r: u64) {
    let half = #[verifier::fip] |y: u64| -> (r: u64) { y / 2 };
    apply(&half, 7)
}
```

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
`requires` clauses (`call_requires`, `call_ensures`, `call_allocations`). Besides a function's
type parameters, it may appear in a `where` clause (`where T: Clone with { .. }`, also for a type
that is not a parameter), on an inherent impl block (every exec and proof method gets it), and
on a struct's type parameter (every inherent impl block of the struct in the same `verus!`
block gets it, for the type it instantiates the parameter with). It is rejected on a trait impl,
whose methods cannot have `requires`.

## Deallocation bounds: `deallocates`

`deallocates d` bounds the number of deallocations of an exec function on a normal return, as
`allocates` bounds its allocations. It comes after `allocates`:

```rust
fn drop_two(v: &mut Pool, a: Slot, b: Slot)
    allocates 0
    deallocates 2
{
    v.free(a);
    v.free(b);
}
```

* A deallocation is the program's release of one block: `Allocator::deallocate` is 1, `grow`,
  `grow_zeroed` and `shrink` at most 1 (they may move the block), `vstd::raw_ptr::deallocate` 1,
  and a function with `encapsulates alloc(a, d)` `d`. A `#[verifier::fip]` function is
  `deallocates 0` (it cannot state `deallocates`). Any other callee needs a `deallocates` bound:
  a function with one cannot call a function without one.
* The body is checked as for `allocates`: a ghost counter, compared with the bound (evaluated at
  entry) at every normal return. `deallocated()` is that counter, for loop invariants.
* `deallocates deallocates_when(d, c)` is the bound `if c { d } else { 0 }`, and
  `call_deallocates` of the function is `c`; `allocates allocates_when(a, c)` is the same for
  allocations. A plain bound `d` makes `call_deallocates` `d > 0`.
* A trait method declaration's bound is a contract of every implementation: an implementation's
  body is counted against it, and one with a bound of its own must stay within it (checked on
  entry).
* `call_deallocations(f, args)` / `f.deallocations(x)` is the bound of a function value (see
  "Callbacks, closures and traits").
* The implicit drops are counted too. Where the compiler drops a value (a local at the end of
  its scope, on every path that leaves it: the end of the block, `return`, `break`, `continue`,
  `?`; a temporary at the end of its statement; the old value of a place an assignment
  overwrites), the count is `vstd::alloc_check::drop_deallocations(v)` of the parts of the value
  that are still there (not moved out). A value moved on some paths only is counted on the
  others (a ghost drop flag), so `match o { Some(b) => consume(b), None => {} }` counts nothing
  for `o`. So is the scrutinee of a `match` or `if let` (`if let Some(x) = v.pop() { .. }`,
  `while let Some(x) = it.next() { .. }`). A loop whose body drops values needs `deallocated()`
  in its invariant.
* `drop_deallocations` is exact for `Box` (its contents, then 1 for its block, 0 for a
  zero-sized `T`), `Vec` (its elements, then 1 if it has a buffer: `vec_has_buffer`), arrays,
  `Option`, `Result` and tuples; at most 1 for `String`; at most the elements' plus 1 for
  `VecDeque`; at most 1 plus the contents' for `Rc` and `Arc` (the last reference frees);
  at most 1 for a `HashMap` or `HashSet` whose keys, values and hasher cannot deallocate; 0 for
  `Copy` types and the `NoDeallocDrop` types (`Global` and `System` among them). The container
  facts hold for an allocator whose drop cannot deallocate: `Box<A>`, `Rc<A>` and `Arc<A>`
  implement `Allocator` too, but dropping them frees a block. For other types (a type
  parameter, a user struct) it is not defined: state what you need, e.g. `deallocates
  drop_deallocations(x)`, or bound the type parameter by `NoDeallocDrop`.
* `drop(x)` (`core::mem::drop`) is counted `drop_deallocations(x)`, like the end of a scope.
* Verus checks on the compiled program that each drop that may deallocate is one it counted,
  and rejects any other: for now, a temporary in an operand of `&&` or `||`; a temporary that a
  `let` keeps alive for the rest of its block because its initializer borrows it (`let r =
  &f();`, also through a block's tail `{ &f() }`, a branch of an `if` or `match`, or a field of a
  literal `(&f(), 1)`, `Some(&f())`); a `Box` whose contents were moved out of it; and a
  `move` closure that captures a value it only reads. Bind the value to a local, or move it.
  An or-pattern whose alternatives move different parts of a value (e.g.
  `(true, x, _) | (false, _, x)`) is rejected too (alternatives that are different variants of
  an enum are fine), and so is an async function with a `deallocates` bound. Assigning to an
  element through indexing (`v[i] = x`) is rejected too: write `let r = &mut v[i]; *r = x;`, or
  `v.set(i, x)`.
  (Like rustc, Verus drops a temporary at the end of its statement, or of the condition or branch
  of an `if`, the condition or body of a loop (every iteration), or a match arm or guard. As in
  Rust 2024 (by the edition of the code, as rustc decides), the temporaries of a block's tail
  expression are dropped at its end, before the block's locals, and the scrutinee of an `if let`
  at the end of the then-branch or before the else-branch. The edition matters: give Verus the
  crate's (`--edition 2024`; without one, Verus compiles as Rust 2021 and warns under
  `-V alloc-check`).)
* A closure can have a `deallocates` bound, counted the same way (its own drops included); a
  call of it counts `call_deallocations` of it. A `#[verifier::fip]` closure deallocates nothing
  (it cannot state `deallocates`).
* Dropping a closure drops what it owns. `drop_deallocations` of a closure is 0 when it has no
  drop glue (it captures nothing, or only references and `Copy` values), and of a function item
  always. A function that takes a closure by value may drop it: vstd's specifications of std
  functions that do (`Option::map`, `and_then`, `ok_or_else`, `unwrap_or_else`, `Result::map`,
  `map_err`, `bool::then`, `cmp::min_by`, `max_by`, `Box::map`, ...) count
  `drop_deallocations(f)` besides the call, and so does `f(x)` for `f: F` with `F: FnOnce(..)`
  (a closure of kind `Fn` called through `FnOnce` runs its body and then drops itself). The
  drop of a closure that owns a value whose drop may deallocate (a `move` closure that captures
  a `Box`) is not defined yet: capture by reference instead. (A call `f(x)` of a closure of kind
  `FnOnce` counts its drop too, though the body drops what it owns: an over-count.)
* The earlier form `allocates deallocates_when(n, c)` (a condition without a number) is no longer
  accepted: write `allocates n deallocates deallocates_when(d, c)`.
* vstd's specifications of std functions state their deallocations: those that may free memory
  do it with a count (`Vec::push` 1 where it grows an existing buffer, `String::push_str` 1,
  `Vec::clear` and `truncate` the drops of the removed elements, a comparison or `clone` that
  calls the user's code what those calls deallocate). A function that drops a value it was
  given counts `vstd::alloc_check::drop_deallocations(v)` (`Option::unwrap_or` drops `default`
  when the option is `Some`, `Option::insert` drops the old contents); for a sequence of values
  it is `seq_drop_deallocations(s)` (for `drop_deallocations`, see above).
* A few specifications state no bound, because they run user code whose deallocations vstd
  cannot name yet: the `HashMap` and `HashSet` operations that hash a key (`insert`, `get`,
  `remove`, `contains_key`, `entry`, `reserve`, ...), `to_string`, `format!` and
  `Formatter::write_fmt`, and `Vec::from_fn`. Such a function cannot be called from a function
  with a `deallocates` bound (nor from a fip function).
* `Iterator::next` (so a `for` loop) is bounded by `iter_next_deallocations(&*self)`, a
  per-implementation term like `iter_next_cost`. vstd states it 0 for std's iterators whose
  `next` frees nothing: ranges of std integers (`0..n`, `0..=n`), the iterators of slices
  (`iter()`, `iter_mut()`, `chunks`) and so of `&Vec`, the borrowing iterators of `VecDeque`,
  `HashMap`, `HashSet`, `BTreeMap` and `BTreeSet`, `Chars`, and `vec::IntoIter`. As for
  `allocates`, a loop must keep the counter in its invariant (`invariant deallocated() == 0`;
  in a fip function, `invariant allocated() == 0`). A loop over an owning iterator (`for x in v`
  for a `Vec` `v`) is still rejected: dropping the iterator frees its buffer, which is not
  counted yet. Under `-V alloc-check` a verified `impl Iterator` is counted against the bound
  too: its `next` must free nothing, unless an axiom states its `iter_next_deallocations`.

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
  the caller must show to be false: `d > 0` for `deallocates d`, `c` for `deallocates
  deallocates_when(d, c)` (evaluated at entry; see "Deallocation bounds"). For example,
  `Vec::push` may deallocate when it has to grow an existing buffer. Growing reallocates, which
  frees the old block. A vector without a buffer grows by calling only its allocator's
  `allocate`, which never deallocates (for any allocator: see "Custom allocators"). A trait
  method declaration without a default body may state a bound or a condition too, as a contract
  of every implementation: an implementation with a verified body is counted against it, one
  without (`external_body`, an `assume_specification`) has the declaration's and may not state
  its own, and the allocator runtime's code is exempt (`Allocator::allocate` is declared
  `deallocates 0`). An implementation
  that Verus does not check, or one in a crate not verified with `-V alloc-check`, is rejected. A
  call of a trait method that does not resolve to an impl (a generic call) is accepted only if
  the method's declaration is `#[verifier::fip]`, if the caller shows its declaration's
  condition false, or if it calls an operator trait's method through its marker (see "Operator
  traits" below). The attribute on a
  declaration is a contract: every implementation of the method must be `#[verifier::fip]` too
  (`#[verifier::fip(strict)]` for a strict declaration), so its calls and its drops are
  checked, and an implementation that Verus does not check is rejected (as for a declaration
  with an `allocates` bound). A default body is checked where it is declared. A call of a
  function value (a closure, or `f(x)` for `f: F` with `F: Fn(..)`) has the condition
  `f.deallocates(x)` (`call_deallocates`), which the caller must show false. That is so for a
  closure marked `#[verifier::fip]` (or `#[verifier::fip(strict)]`) on the closure expression,
  whose body is then checked like a fip function's (without a bound, it allocates nothing);
  a generic caller can require it (`requires !f.deallocates(x)`). (A strict function makes a
  generic call only through an operator trait's strict marker: otherwise its callee's stack use
  is not known. It may call a strict closure it knows.) A call of a function
  of std, vstd or another crate is also checked, on the MIR, for the functions of this crate it
  may call back (see "Callbacks from other crates" below). Such a call must not take by value a
  closure whose drop may deallocate (one that owns a `Box`, say): std may drop it, and a
  closure of kind `Fn` or `FnMut` (one bound to a local first) called through `FnOnce`, as
  `Option::map` does, runs a compiler shim that calls the body and then drops the closure's
  environment, which neither the closure's checks nor its bound cover. Capture by reference
  instead.
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

A container calls its allocator's methods inside std's code. Those are the runtime's (see "Custom
allocators"), so a fip or strict function may use std or vstd code with any allocator
(`Vec<u8, A>::push`, `Vec::with_capacity_in(n, a)`): the allocator's own code is a leaf, neither
checked for deallocation nor followed by the stack check.

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

* A call may go to another strict function, or to std or vstd. A function of another crate may
  be called (also as the target of `become`) only if it is strict and its crate was verified and
  compiled with `-V alloc-check` and imported with its library file (see "Libraries and other
  crates"): that compilation checked it and everything it reaches in its own crate. Such
  functions reach this crate's code only through the trait bounds of what the call instantiates
  them with. Those callbacks are followed and count as calls that are not tail calls (see
  "Callbacks from other crates" below), except calls of a user allocator's methods: a call with a
  user allocator (`A: FipStrictAllocator`, whose strict methods are this crate's) counts as using
  a user allocator, so the allocator's methods may not reach it (below). Calls of other functions
  of other crates, and calls whose callee is not known (function values, and generic calls other
  than an operator trait's methods through `FipStrictOp`), are rejected.
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
  `as_slice`, `as_mut_slice`, `deref`, `deref_mut` and indexing, and the comparisons listed under
  "Operator traits" below (`<[T]>::contains`, `sort_unstable`, `Option`'s comparisons, ...).
  (`mem::take` is not among them: it runs `T::default`.) The mark is trusted, like
  `external_body`, and is accepted only in vstd. The drop rule of `-V alloc-check` also relies on
  it: a call of such a function with `&mut` to a value does not count as dropping what the value
  contains.
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

### Operator traits: `FipAdd`, `FipOrd`, ...

A generic call of a trait method has no known impl. So `-V alloc-check` can bound it only through
the caller's own bound (`call_allocations`), and a fip function cannot make it at all. For the
operator traits of `core`, vstd has unsafe marker traits that say what every impl of the trait for
a type does. For each operator trait `Op` there are three, each a supertrait of the next:

| Marker | The methods of `X`'s `Op` impl | A generic call through `T: Marker` |
|---|---|---|
| `FbipOp` | are bounded by `allocates 0` | is charged 0 |
| `FipOp` | are also `#[verifier::fip]` | may be made in a `#[verifier::fip]` function |
| `FipStrictOp` | are also `#[verifier::fip(strict)]` | may be made in a `#[verifier::fip(strict)]` function |

`Op` is one of the traits that vstd specifies: `Neg`, `Not`, `Add`, `Sub`, `Mul`, `Div`, `Rem`,
`BitAnd`, `BitOr`, `BitXor`, `Shl`, `Shr`, their `*Assign` forms, `Index`, `IndexMut`, `Deref`,
`DerefMut`, `PartialEq`, `PartialOrd`, `Ord`, `Clone`, `From` and `Into`. A marker has the type parameters of its trait
(`FipAdd<Rhs = Self>`, `FipIndex<Idx>`) and follows its supertraits: `FipOrd` implies
`FipPartialOrd` and `FipPartialEq`, and `FipIndexMut` implies `FipIndex`.

```rust
use vstd::alloc_check::{FipOrd, FipStrictPartialEq};

#[verifier::fip]
fn lt_gen<T: FipOrd>(a: &T, b: &T) -> bool {
    a < b
}

#[verifier::fip(strict)]
fn eq_gen<T: FipStrictPartialEq>(a: &T, b: &T) -> bool {
    a == b
}
```

A comparison of references (`a == b` with `a: &T`) runs std's impl for references, which calls
`T`'s method, so the marker of `T` covers it.

vstd implements the markers for the primitive integer types, `bool` and `char` (for the traits
they implement), the `Clone` markers also for `f32` and `f64`, and the `From` markers for the
reflexive `From<T> for T` (which returns its argument); these impls are trusted. Any other `unsafe impl FbipOp for X` (or `FipOp`,
`FipStrictOp`) is accepted only if `X`'s `Op` impl, for the same type written the same way, is
checked by Verus, and each method that impl defines is bounded by `allocates 0` (a literal `0`)
and, for the higher levels, is `#[verifier::fip]` or `#[verifier::fip(strict)]`. A method that the
impl does not define runs `core`'s provided body, which calls only the trait's own methods. A
derived impl (`#[derive(PartialEq)]`) is not accepted, except a derived `clone`, which Verus
checks with `allocates 0` and the attributes of a level, so the markers up to that level accept it:

* If its body is `*self` (`#[derive(Clone, Copy)]` on a type without type parameters), it is
  `#[verifier::fip(strict)]` (and keeps `ensures r == *self`).
* If it is a struct's and clones field by field, its level is the lowest of the `Clone` markers
  of the fields' types, where the impl is (a type parameter needs the marker as a bound on the
  type itself, which `#[derive(Clone)]` copies onto the impl). It is at most `#[verifier::fip]` if
  a field's type has a type parameter: the strict stack check takes such a call (through a marker)
  to reach any strict `clone` of the crate, this one included. If a field's type has no marker,
  the `clone` has no bound, as before.

As for the other markers, an impl outside
`verus!`, or in a crate that was not verified with `-V alloc-check`, is rejected.

`Ord`'s provided `max`, `min` and `clamp` drop a value of `Self`. So `FbipOrd` needs
`AllocFreeDrop` and `FipOrd` needs `NoDeallocDrop`, and a strict function cannot call them
through a marker (the destructor of a type parameter is not known there). The same holds for
`Clone`'s provided `clone_from` (`*self = source.clone()`): `FbipClone` needs `AllocFreeDrop`,
`FipClone` needs `NoDeallocDrop`, and a strict function cannot call `clone_from` through
`FipStrictClone`.

The std functions that compare their arguments deallocate only if a comparison does, and
allocate only what their comparisons allocate. vstd states this with spec-level forms of the
markers, `partial_eq_is_fip::<T, Rhs>()`, `partial_ord_is_fip::<T, Rhs>()`, `ord_is_fip::<T>()`
and `ord_is_fbip::<T>()` (each true for a type with the marker), in their `deallocates_when`
conditions, and with axioms that a method of an `FbipOp` type allocates nothing
(`call_allocations(<T as PartialEq>::eq, ..) == 0`). So a fip function can call them for a type
with the marker:

```rust
#[verifier::fip]
fn sort_it<T: FipOrd>(v: &mut [T]) {
    v.sort_unstable();
}

#[verifier::fip]
fn has<T: FipPartialEq>(s: &[T], x: &T) -> bool {
    s.contains(x)
}
```

These are `<[T]>::contains`, `starts_with`, `ends_with`, `sort_unstable` and `binary_search`,
`Option`'s `eq`, `partial_cmp` and `cmp`, the comparisons of references, `Range::contains` and
`RangeInclusive::contains`, and `cmp::min` and `cmp::max`. (The integers', `bool`'s and `char`'s
`min`, `max` and `clamp` methods are specified directly, `allocates 0 deallocates 0`; `clamp`
requires `min <= max`, since core panics otherwise.) All but the last two drop nothing
(`#[verifier::alloc_check_skip_drops]`), so a strict function may call them too, through
`FipStrictOp`. (`sort_unstable`'s result is a permutation of its input, and
sorted by `cmp_spec` when `T`'s comparisons are a total order, `vstd::laws_cmp::obeys_cmp::<T>()`.
On a slice so sorted, `binary_search` returns `Ok(i)` for an `i` whose element compares `Equal`,
or `Err(i)` with every element before `i` `Less` and every element from `i` on `Greater`. How
many comparisons they make is not specified, so their allocations are an uninterpreted term
unless the type is `FbipOrd`.) vstd also implements the comparison markers for
`Option<T>` and for references, when `T` (the referent) has them. A type without a marker gets
no `deallocates_when` that it can show false, even if its comparisons are fip: give it the
marker.

In the same way, `<[T]>::to_vec`, `Box::<[T]>::from(&[T])` and `Vec::<T>::from(&[T])` (also from
`&mut [T]` and `&[T; N]`, which std writes as `to_vec`) allocate once (nothing for an empty
slice) and clone each element. Their results have the input's length and a clone of each element
(`cloned`), they allocate `1 + seq_clone_allocates(..)` (0 when the slice is empty), and they
deallocate only if a `clone` does: `clone_is_fip::<T>()` (true for a `FipClone` type) in their
`deallocates_when` conditions, with an axiom that `clone` of an `FbipClone` type allocates
nothing. Neither drops a `T` on a normal return, so a strict function may call them through
`FipStrictClone`:

```rust
#[verifier::fip(strict)]
fn copy<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
    requires
        forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
    ensures
        r@ == src@,
    allocates
        if src@.len() == 0 { 0int } else { 1int },
{
    src.to_vec()
}
```

(The `requires` gives `r@ == src@`: `cloned` allows a clone or the value itself. A caller with
`T = i32` or `T = f64` shows it from vstd's specification of their `clone`.)

`From` and `Into` go both ways. std's blanket `impl<T, U: From<T>> Into<U> for T` is
`U::from(x)`, so:

* A call `x.into()` that goes through it is checked as the call `<U as From<T>>::from(x)` when
  that `From` impl is known to Verus (has a specification, or is verified): its `allocates`,
  `deallocates_when`, "drops nothing" and `ensures` apply. (`src.into()` for a `Box<[T]>` or a `Vec<T>` is then
  `Box::<[T]>::from(src)` or `Vec::<T>::from(src)`.) When the impl is not known, the blanket impl's specification applies,
  which refers to `U::from`.
* `U: FipFrom<T>` gives `T: FipInto<U>` (vstd implements it, and a bound `U: FbipFrom<T>`
  covers the call `x.into()` too). An `Into` impl that a crate writes itself, without `From`,
  can have the `Into` markers, checked like the others.

```rust
#[verifier::fip(strict)]
fn conv<T: NoDeallocDrop, U: FipStrictFrom<T> + NoDeallocDrop>(t: T) -> U {
    t.into()
}
```

### Callbacks from other crates

The code of std, vstd or another crate can call this crate's functions only through the trait
bounds of what it is instantiated with: a generic function calls the methods of its type
arguments through its bounds. For every call of such a function in a fip function, Verus takes
the callee's bounds on the MIR of the compiled program, instantiates them with the call's type
arguments, adds their supertraits and the bounds of their associated types, and finds the impls
they select. For an impl of std it continues with the impl's own bounds (`Vec<L>: PartialEq`
needs `L: PartialEq`). Every function of an impl of this crate found this way, and every closure
or function item found through an `Fn` bound, may be called back:

* in a `#[verifier::fip]` function, it must be `#[verifier::fip]`;
* in a `#[verifier::fip(strict)]` function, it must be strict, and it counts as a call that is not
  a tail call;
* a function of a third crate must be a strict function of a crate that was verified and compiled
  with `-V alloc-check`;
* a bound on a type parameter, whose impl is not known, is accepted only through the operator
  marker of its trait (`FipOp`, or `FipStrictOp` in a strict function). In a strict function, such
  a callback may reach any strict method of this crate's impls of that trait and of its
  supertraits; each counts as a call that is not a tail call;
* anything else (a bound on `dyn`, a function pointer) is rejected.

The bounds of `core::alloc::Allocator` are left to the allocator rules above. The verifier's
checks already reject most calls of std functions that take callbacks, since their vstd
specifications have no `deallocates_when` condition. This check does not depend on that, and it
also covers strict functions of other crates that are instantiated with this crate's types.

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
`allocates` bound must be `no_unwind`, so that no panic path exists; so must every closure with a
bound (or `#[verifier::fip]`, which gives a closure `allocates 0`). vstd's specifications of
allocating std functions (`Box::new`, `Vec::push`, ...) are not `no_unwind`: capacity overflow
is a `panic!` that can unwind. So in practice, a function that allocates cannot pass the strict
mode yet.

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
* that an allocator's own code is the runtime: a bound counts the program's calls to allocators
  (one each), not what the allocators do (their `Allocator`, `Clone` and `Drop` impls are not
  checked for allocations, deallocations or stack; see "Custom allocators");
* the counts of `encapsulates alloc(a, d)` (the function's body is the runtime's and is not
  checked for allocations, deallocations or stack);
* calls inside `#[verifier::trusted_call]` blocks (such as an allocator's forwarding
  `deallocate`). `--no-cheating` applies only to the crate being verified: the blocks (and the
  `external_body` functions) of a dependency verified without it are trusted all the same, and a
  `.vir` does not record whether it was;
* `external_body` functions other than `drop`, and `external_body` types (their hidden fields'
  drops are trusted only for std types that vstd declares);
* the crates `std`, `core`, `alloc`, `vstd` and `verus_builtin`: their functions reach user code
  only through the trait bounds of their type arguments (which the fip checks follow, see
  "Callbacks from other crates"), and use bounded stack space. They are recognized by name,
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
* vstd's impls of the operator markers (`FipAdd`, `FipOrd`, ...) for the primitive types;
* the toolchain's std (its trusted drops and opaque types).

Known limitations, all of which make Verus reject programs or give weaker bounds (they are not
unsound):
* `dyn` values and opaque `impl Trait` values being dropped;
* the drop of a closure that owns a value whose drop may deallocate;
* projected types in drop glue (for example `Cow`);
* a closure that captures one field of a struct is checked as if it captured the whole struct;
* unchecked implementations of bounded trait methods anywhere in the program.

`catch_unwind` is rejected inside checked functions. A caught panic lets execution continue
after allocations on the unwinding path, and `allocates` does not count those.
