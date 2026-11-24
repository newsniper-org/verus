# Ghost Erasure

Verus performs ghost erasure: ghost code that exists for verification purposes is removed when
building the executable artifacts, ensuring they are minimally disturbed.

One byproduct of this is that certain identifiers that exist at verification time will not exist at
compile time. This means that the code shown below would fail to _compile_:

```rust
use vstd::prelude::*;

verus! {

pub mod ghost_mod {
    pub closed spec fn ghost_fn() -> bool { true }
}

pub mod test_mod {
    use crate::ghost_mod::ghost_fn;
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//  FAILS: During compilation, ghost_fn is erased, causing rustc
//         to complain about a missing definition

    pub fn exec_fn() -> u64 {
        1
    }
}

} // verus!
```

To remedy this, Verus provides the `verus_only` flag, which is turned on during
verification, but is otherwise off. This allows us to guard `use` statements like the one above:

```rust
pub mod test_mod {
    #[cfg(verus_only)]
    use crate::ghost_mod::ghost_fn;
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//  OK: During compilation, the `use` statement is removed
}
```

Another use-case for the `verus_only` flag is setting attributes that only make sense during verification.
For instance, the code below sets the `verifier::loop_isolation` option to false for the file, only if `verus_only` is set:
```rust
#![cfg_attr(verus_only, verifier::loop_isolation(false))]
```


> [!CAUTION]
> This should only be used to guard `use` statements and setting config attributes.
> Using this `cfg` flag for conditional compilation of code can introduce **unsoundness**,
> breaking the verification guarantees.
>
> As an example, the code below will verify successfully, even though `f()` returns
> 42 when running the executable.
>
> ```rust
> fn f() -> (u: u32)
>   ensures u != 0
> {
>   #[cfg(verus_only)]
>   { return 0; }
>   #[cfg(not(verus_only))]
>   { return 42; }
> }
> ```

> [!NOTE]
> Verus is under _active development_, meaning this option may change or be removed
> (in particular if a better solution to this problem is devised). See the [GitHub discussion](https://github.com/verus-lang/verus/discussions/2101)
> for more information.

## Exec types must not depend on ghost code

Verus type-checks the crate twice: once with its ghost code, to verify it, and once with the ghost
code erased, to compile it. If ghost code is the only thing that fixes the type of exec code, the
two type-checks infer different types, and the compiled program would run code that Verus did not
verify. In the example below, the verified `f` uses `n: u64` and calls `<u64 as Mk>::mk`; without
the proof block, `n` would be an `i32`, the default type of an integer literal, and the compiled
`f` would call `<i32 as Mk>::mk`:

```rust
pub trait Mk { fn mk(self) -> (r: Option<u8>); }
impl Mk for u64 { fn mk(self) -> (r: Option<u8>) ensures r.is_none() { None } }
impl Mk for i32 { fn mk(self) -> (r: Option<u8>) { Some(1u8) } }

pub fn f() -> (r: Option<u8>)
    ensures r.is_none(),
{
    let n = 1;
//  ^ ERROR: this exec code has type `i32` in the compiled program, but `u64` in the verified program
    proof { let g: u64 = n; }
    n.mk()
}
```

Verus compares the two type-checks, and reports an error where exec code has another type, calls
another function or the same function with other type arguments, or has another literal in the
compiled program. The same goes for a `let ghost`, a `Ghost(..)` or `Tracked(..)` argument, a loop
invariant, a closure's `#[verus_spec]` return type, a float literal (`f64` by default) and a
diverging expression (`!`). The fix is to write the type in the exec code: `let n: u64 = 1;`,
`1u64`, or `f::<u64>(..)` for a type argument.

The comparison runs whenever Verus verifies the crate and then type-checks the compiled program:
always with `--compile`, and otherwise unless `--no-verify`, `--no-lifetime` or
`--no-erasure-check` is given. It is by source location. It covers the code that the user wrote (also inside a
`macro_rules!` definition) and rustc's desugarings of it. It does not cover the code that Verus's
and vstd's own macros generate, which differs between the two runs by design, nor the kind of a
closure (`Fn`, `FnMut` or `FnOnce`): ghost code can make a closure take a captured value by move in
the verified program only, which changes when the value is dropped, not what the closure computes.

## `Cargo.toml` configuration

[Since version 1.80](https://blog.rust-lang.org/2024/05/06/check-cfg/), Rust automatically checks if all `cfgs` match expected config names.
The `verus_only` `cfg` flag is passed in directly by Verus and never declared in a
`Cargo.toml`. This means that Rust will emit a warning when compiling. To prevent this, add the
following to your `Cargo.toml`:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = [
  'cfg(verus_only)',
] }
```

> [!NOTE]
> This is done automatically when initializing the repository with `cargo verus new`
