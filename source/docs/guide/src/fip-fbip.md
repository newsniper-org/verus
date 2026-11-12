# Fully in-place functions (FIP and FBIP)

> **Fork extension, experimental.** Everything on this page exists in this fork of Verus only and
> needs `-V alloc-check`. It is a guide to the features; the precise rules are in
> [Allocation bounds (`allocates`)](./reference-allocates.md). A Korean version of this page is
> [here](./fip-fbip.ko.md).

## The idea

Functional programs build new values instead of changing old ones, which normally costs an
allocation per new cell and a deallocation per dead one. The FP² paper (Lorenzen, Leijen and
Swierstra, "FP²: Fully in-Place Functional Programming", ICFP 2023) identifies functions that need
neither. They reuse the cells they consume for the cells they build. It names two classes:

| FP² class | allocations | deallocations | stack |
|---|---|---|---|
| `fip` | none | none | constant |
| `fip(n)` | at most `n` | none | constant |
| `fbip` | none | any | any |
| `fbip(n)` | at most `n` | any | any |

A `fip` function runs in a fixed amount of memory, so it can run where allocation is not
available or must not fail (in an interrupt handler, in an allocator, without an operating
system). `fbip` ("functional but in place") is weaker: it may free memory, and may use stack space
in proportion to its input.

## How the fork checks them

The fork splits FP²'s `fip` in two, because Rust does not guarantee that a call in tail position
reuses the caller's stack frame:

| What you write | Allocations | Deallocations | Stack | FP² class |
|---|---|---|---|---|
| `allocates n` | at most `n` | any | any | `fbip(n)` |
| `#[verifier::fip]` | none (or at most `n` with `allocates n`) | none on a normal return | any | `fip(n)` without the stack part |
| `#[verifier::fip(strict)]` | none (or at most `n` with `allocates n`) | none on a normal return | constant | `fip` / `fip(n)` |

All three are checked when Verus runs with `-V alloc-check`:

* `allocates n` is proved by the SMT solver, like `ensures`. Each call is charged its callee's
  bound.
* `#[verifier::fip]` adds two checks. Every call must be to a function that cannot deallocate
  (another fip function, or a std function whose vstd specification says when it may). Every drop
  that the compiler inserts must be of a value whose drop cannot deallocate.
* `#[verifier::fip(strict)]` also requires that the function recurse only through `become`
  (`#![feature(explicit_tail_calls)]`). It may call only other strict functions, std and vstd.

The checks of drops and of the stack run on the compiled program (MIR, after ghost code is erased
and drops are placed). So they see drops that do not appear in the source.

## Examples

The examples below share this list type:

```rust
pub enum List { Nil, Cons(u64, Box<List>) }

pub open spec fn len(l: List) -> nat
    decreases l
{
    match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
}
```

### `fbip(n)`: a bound on allocations

`Vec::push` allocates at most once. When the vector has to grow, it frees its old buffer.
That is fine for an allocation bound:

```rust
fn push_one(v: &mut Vec<u64>)
    allocates 1
{
    v.push(1);
}
```

### `fip`: reuse what you consume

A `Box` that is moved in and out again is not freed:

```rust
#[verifier::fip]
fn halve(mut b: Box<List>) -> (r: Box<List>) {
    match &mut *b {
        List::Cons(x, _) => { *x = *x / 2; }
        List::Nil => {}
    }
    b
}
```

The classic FP² example is reversing a list in place. Each cell's box is reused for the cell of
the result: the contents are swapped out with `mem::replace`, and the box is put into the new
cell.

```rust
#[verifier::fip]
fn reverse(l: List, acc: List) -> (r: List)
    ensures len(r) == len(l) + len(acc),
    decreases l
{
    match l {
        List::Nil => acc,
        List::Cons(x, mut b) => {
            let next = core::mem::replace(&mut *b, acc);
            reverse(next, List::Cons(x, b))
        }
    }
}
```

### `fip(n)`: a few new cells

With `allocates n`, a fip function may allocate, but still never free:

```rust
#[verifier::fip]
fn cons(x: u64, l: List) -> (r: List)
    allocates 1
{
    List::Cons(x, Box::new(l))
}
```

### Constant stack: `fip(strict)`

`reverse` above is recursive, and the recursive call is in tail position. Rust does not
promise that such a call reuses the stack frame (at `opt-level=0` it does not), so a long list
can overflow the stack. `become` makes the promise, and rustc rejects the program if it
cannot keep it:

```rust
#![feature(explicit_tail_calls)]

#[verifier::fip(strict)]
fn reverse(l: List, acc: List) -> (r: List)
    ensures len(r) == len(l) + len(acc),
    decreases l
{
    match l {
        List::Nil => acc,
        List::Cons(x, mut b) => {
            let next = core::mem::replace(&mut *b, acc);
            become reverse(next, List::Cons(x, b))
        }
    }
}
```

A loop also uses constant stack space. Recursion that is not a tail call (`len(t) + 1`) is
rejected.

### Generic code

A fip function that drops a value of a type parameter needs to know that the drop cannot free
memory. The unsafe marker trait `vstd::alloc_check::NoDeallocDrop` says so:

```rust
#[verifier::fip]
fn first<T: vstd::alloc_check::NoDeallocDrop>(a: T, b: T) -> (r: T) {
    a // `b` is dropped here
}
```

A strict function must also know which destructors such a drop runs, so it cannot drop a value of
a type parameter at all (a `Copy` bound rules out a destructor). It may still call the std
functions that move values without dropping them, such as `mem::swap`, `mem::replace` and the
slice and `Vec` views:

```rust
#[verifier::fip(strict)]
fn swap_ends<T: vstd::alloc_check::AllocFreeDrop>(xs: &mut [T])
    requires old(xs)@.len() >= 2,
    allocates 0
{
    let n = xs.len();
    xs.swap(0, n - 1);
}
```

## Common rejections

| Code | Why it is rejected | Instead |
|---|---|---|
| `fn unbox(b: Box<List>) -> List { *b }` | moving the contents out of a `Box` frees the box | keep the box and reuse it, or return it |
| `**tail = t;` | assignment drops the old value first | `mem::replace(&mut **tail, t)` and hand the old value back (or reuse it) |
| a parameter that is not used on some path | it is dropped at the end of the function | return it, store it, or move it into the result |
| `v.push(x)` in a fip function | `push` may free the old buffer when it grows | require `old(v)@.len() < spec_vec_capacity(&*old(v))`, or reserve beforehand outside the fip function |
| `fn f<T>(a: T, b: T)` dropping `b` | the drop of a `T` is not known | `T: NoDeallocDrop` (not available in a strict function) |
| `count(n - 1, acc)` in a strict function | a plain tail call may still grow the stack | `become count(n - 1, acc)` |
| `len(t) + 1` in a strict function | not a tail call | use an accumulator and `become`, or a loop |

A placeholder can be overwritten without a drop:

```rust
#[verifier::fip]
fn fill(hole: &mut List, v: List)
    requires *old(hole) is Nil,
{
    core::mem::forget(core::mem::replace(hole, v));
}
```

`Nil` owns nothing, so forgetting it leaks nothing.

## Tools

`-V fip-lint` (which does not need `-V alloc-check`) points out recursion that grows the stack:

* A tail call that is not `become`. With verus-analyzer, the quick fix rewrites it.
* Recursion modulo a constructor (TRMC), such as `List::Cons(n, Box::new(range(n - 1)))`. The
  linter suggests the equivalent loop, which fills a `&mut` hole in each step. `-V fip-lint=fix`
  applies the rewrite and keeps it only if the crate still verifies.

The reference describes when the rewrite applies.

## What is not covered

* **Unwinding.** The checks are about paths that return normally. A panic that unwinds may free
  memory. Use `no_unwind` to rule panics out.
* **Leaks.** FP²'s functions use each cell they own exactly once. Here `#[verifier::fip]` only
  promises that nothing is freed: `mem::forget` is allowed and leaks what it forgets.
* **Trust.** The specifications of std in vstd (when `Vec::push` may free, which std functions drop
  nothing) and the marker trait impls are trusted. The stack rule trusts rustc's guarantee for
  `become`, and the claim that std and vstd functions use bounded stack space.
* **Allocators.** A fip function may use a container with an allocator other than the global or
  the system allocator only if the allocator implements `FipAllocator` (or `FipStrictAllocator`
  for a strict function). See [Custom allocators](./reference-allocates.md#custom-allocators).

For the full rules, see [`#[verifier::fip]`](./reference-allocates.md#fully-in-place-functions-verifierfip)
and [`#[verifier::fip(strict)]`](./reference-allocates.md#constant-stack-space-verifierfipstrict)
in the reference.
