# Unwinding signature

For any `exec`-mode function, it is possible to specify whether that function may [unwind](https://doc.rust-lang.org/nomicon/unwinding.html). The allowed forms of the signature are:

 * No signature (default) - This means the function may unwind.
 * `no_unwind` - This means the function may not unwind.
 * `no_unwind when {boolean expression in the input arguments}` - _If_ the given condition holds, then the call is guaranteed to not unwind.
    * `no_unwind when true` is equivalent to `no_unwind`
    * `no_unwind when false` is equivalent to the default behavior

By default, a function is allowed to unwind. (Note, though, that Verus _does_
rule out common sources of unwinding, such as integer overflow, even when the function
signature technically allows unwinding.)

## Example

Suppose you want to write a function which takes an index, and that you want to specify:

 * The function will execute normally if the index is in-bounds
 * The function will unwind otherwise

You might write it like this:

```rust
fn get(&self, i: usize) -> (res: T)
    ensures i < self.len() && res == self[i]
    no_unwind when i < self.len()
```

This effectively says:

 * If `i < self.len()`, then the function will not unwind.
 * If the function returns normally, then `i < self.len()` (equivalently, if `i >= self.len()`, then the function must unwind).

## Closures

An `exec` closure can have the same signature, after its `opens_invariants` and before its
`allocates`:

```rust
let half = |y: u64| -> (r: u64) no_unwind { y / 2 };
let get = |i: usize| -> (r: u64) no_unwind when i < v.len() { v[i] };
```

Its body is checked like a function's (a `no_unwind when` condition is taken on entry, before the
body can change the parameters). Without a signature, a closure may unwind.

## Function values: `call_unwinds`

`call_unwinds(f, args)` says whether a call of the function value `f` with `args` may unwind. In
ghost code inside `verus!`, `f.unwinds(args)` is `call_unwinds(f, (args,))` (the arguments are
written unpacked, unlike `f.requires((args,))`). It is `false` for a `no_unwind` function or
closure, and where the condition holds for one with `no_unwind when`; for a trait method, the
declaration's signature applies to every implementation. A call `f(x)` of a function value is
`no_unwind when !f.unwinds(x)`, so a `no_unwind` function can call a function value it is given
by requiring it:

```rust
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> (r: u64)
    requires
        f.requires((x,)),
        !f.unwinds(x),
    no_unwind
{
    f(x)
}

fn use_it() -> (r: u64)
    no_unwind
{
    apply(&|y: u64| -> (r: u64) no_unwind { y / 2 }, 7)
}
```

## Restrictions with invariants

You cannot unwind when an [invariant](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_local_invariant.html) is open.
This restriction is necessary because an unwinding operation does not necessarily abort a program.
Rust allows a program to ["catch" an unwind](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html), for example, or there might be other threads to continue execution.
As a result, Verus cannot permit the program to exit an invariant-block early without restoring
the invariant, not even for unwinding.

This restriction is what enables Verus to rule out [exception safety violations](https://doc.rust-lang.org/nomicon/exception-safety.html).

## Drops

If you implement `Drop` for a type, you are required to give it a signature of `no_unwind`.
