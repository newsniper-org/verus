# Changes from upstream Verus (fork)

> **This page describes a fork of Verus.** It lists what the `fip` branch of this fork changes
> relative to upstream Verus ([verus-lang/verus](https://github.com/verus-lang/verus)), and links
> to the pages that describe each change. A Korean version of this page is
> [here](./fork-changes.ko.md).

## Base and branches

The fork branches off upstream at commit `8bf68ee74` (2026-11-02, "Update no-cheating to disallow
various command-line flags that violate the spirit of not cheating", #3392). Its changes were made
in two layers, first on two branches:

| Branch | Toolchain then | Adds |
|---|---|---|
| `fip` | Rust 1.99.1 (as upstream) | allocation bounds: the `allocates` clause, `-V alloc-check`, `-V alloc-check-strict`, bounds in vstd's std specifications |
| `fip-beta` | Rust 1.100.0-beta.10 (`beta-2026-11-05`) | everything in `fip`, plus Rust 1.100, custom allocators and allocator state, fully in-place functions, `-V fip-lint`, `trusted_only`/`trusted_call` |

When Rust 1.100.0 was released, `fip-beta` moved to it, and `fip` was set to `fip-beta`. So
everything on this page is in both branches, except what the column "since" in the tables below
marks as `fip` (1.100): that was added to `fip` afterwards. Otherwise the column says which of the
two layers introduced it. One change on `fip` (1.100) also removes things: an allocator is now the
runtime, and only the program's calls to it are counted, so `BoundedAllocator`,
`FipAllocator`/`FipStrictAllocator`, the allocator state (`vstd::alloc_heap`) and
`PreorderAuth` are gone from `fip`. (`fip-beta`, frozen, keeps the earlier cost model.)

All of the new verification features are experimental.

## Toolchain: Rust 1.100

`rust-toolchain.toml` (and the CI workflows) select Rust 1.100.0, where upstream uses 1.99.1. The
parts of rustc that Verus carries in its own source tree (`rustc_hir_analysis`, `rustc_hir_typeck`,
`rustc_mir_build`) are updated to the same version. (They were updated to 1.100.0-beta.10 first.
None of the files they carry changed between that beta and 1.100.0.)

What this changes for verified code:

* **`box` patterns are gone** in Rust 1.100. Verus accepts `deref!(p)` patterns through `Box`,
  `Rc` and `Arc` instead (they mean what `box p` meant), and turns on the `deref_patterns` feature
  for the crate it verifies, as it turned on `box_patterns` before. Deref patterns through other
  types are not supported.
* **`core::convert::Infallible` is now an alias of `!`.** Verus therefore rejects a datatype with a
  field of type `Infallible` ("never-to-any coercion is not allowed in spec mode"), which it
  accepted with Rust 1.99.1. The never type `!` itself is stable and needs no specification.
* **`allocator_api` is partly stable.** The parts that are not are now the feature
  `allocator_ext`. vstd turns it on, and so must a crate that uses those parts.
* **`BTreeMap` and its iterators require `A: AllocatorClone`**, and vstd's specifications say so.
* **`[const] Destruct` bounds**, which std 1.100 puts on `Iterator for Range<A>` and others, are
  ignored outside const contexts.
* **New std items.** The module `vstd::std_specs::rust_1_100` specifies the std items that Rust
  1.100 stabilizes and that Verus can use: `bool::toggle`, `mem::DropGuard`,
  `UnsafeCell::{as_ref_unchecked, as_mut_unchecked, replace}`, the `Allocator`, `AllocError` and
  `Layout` types and the `Allocator` impls of `Global` and `System`, `Vec::from_fn`,
  `Vec::allocator`, `Box::allocator`, `Box::new_in`, `Box::take`, `Box::map`, `Rc::map`,
  `Arc::map`, and `Default for Once`. The module documentation lists what it does not cover, and
  why (for example `mem::conjure_zst`, whose precondition cannot be stated). `alloc::Global` is no
  longer `external_body`, so verified code can construct it.

## New features

| Feature | How to use it | Since | Documentation |
|---|---|---|---|
| Allocation bounds | `allocates n` on an `exec` function or closure, checked with `-V alloc-check` | `fip` | [Allocation bounds](./reference-allocates.md) |
| Allocation bounds imply no unwinding | `-V alloc-check-strict` | `fip` | [`-V alloc-check-strict`](./reference-allocates.md#-v-alloc-check-strict) |
| Custom allocators | `Vec<T, A>`, `Box<T, A>`, ... with any allocator: each call to an allocator is 1, and what the allocator does itself is not counted | `fip-beta`; calls only since `fip` (1.100) | [Custom allocators](./reference-allocates.md#custom-allocators) |
| Bound specifications | `T: Tr with { .. }` on type parameters, in `where` clauses, impls and structs | `fip-beta` | [Bound specifications](./reference-allocates.md#bound-specifications-t-tr-with---) |
| Fully in-place functions (no deallocation) | `#[verifier::fip]` | `fip-beta` | [FIP and FBIP](./fip-fbip.md), [reference](./reference-allocates.md#fully-in-place-functions-verifierfip) |
| Deallocation bounds on trait declarations | `deallocates d` on a trait method declaration (a contract of every implementation) | `fip` (1.100) | [Deallocation bounds](./reference-allocates.md#deallocation-bounds-deallocates) |
| A function value's bound and deallocation condition | `call_deallocates(f, args)`; `f.allocations(args)` and `f.deallocates(args)` in `verus!` | `fip` (1.100) | [Callbacks, closures and traits](./reference-allocates.md#callbacks-closures-and-traits) |
| Fully in-place closures | `#[verifier::fip]` on a closure expression; calls of function values in fip code with `!f.deallocates(x)` | `fip` (1.100) | [reference](./reference-allocates.md#fully-in-place-functions-verifierfip) |
| Unwinding of function values | `no_unwind [when c]` on closures; `call_unwinds(f, args)`, `f.unwinds(args)` in ghost code | `fip` (1.100) | [Unwinding signature](./reference-unwind-sig.md#function-values-call_unwinds) |
| Allocators of their own API | `encapsulates alloc(a, d)` on functions and `assume_specification` | `fip` (1.100) | [reference](./reference-allocates.md#allocators-of-their-own-api-encapsulates-allocad) |
| Deallocation bounds | `deallocates d`, `deallocates_when(d, c)`, `allocates_when(a, c)`, `deallocated()`, `call_deallocations`; `call_allocations` (count) beside `call_allocates` (now a `bool`); `vstd::alloc_check::drop_deallocations` and the deallocations of vstd's std specifications; implicit drops counted (checked against the compiled program); `deallocates` on closures | `fip` (1.100) | [Deallocation bounds](./reference-allocates.md#deallocation-bounds-deallocates) |
| Constant stack space | `#[verifier::fip(strict)]` with `become` | `fip-beta` | [reference](./reference-allocates.md#constant-stack-space-verifierfipstrict) |
| Generic operator calls in fip code | `T: FipAdd`, `T: FipOrd`, ... (`FbipOp`, `FipOp`, `FipStrictOp` for each operator trait of `core`) | `fip-beta` | [Operator traits](./reference-allocates.md#operator-traits-fipadd-fipord-) |
| Generic `clone` and slice copies in fip code | `T: FipClone`, ... (the same three levels for `Clone`); `<[T]>::to_vec`, `Box::<[T]>::from(&[T])`, `Vec::<T>::from(&[T])`; derived `clone`s are `allocates 0` and fip/strict as their fields allow | `fip` (1.100) | [Operator traits](./reference-allocates.md#operator-traits-fipadd-fipord-) |
| Conversions in fip code | `U: FipFrom<T>`, `T: FipInto<U>`, ...; `x.into()` is checked as `U::from(x)` | `fip` (1.100) | [Operator traits](./reference-allocates.md#operator-traits-fipadd-fipord-) |
| Stack-growth linter | `-V fip-lint`, `-V fip-lint=fix` | `fip-beta` | [FIP and FBIP: Tools](./fip-fbip.md#tools) |
| Calls whose safety cannot be specified | `#[verifier::trusted_only]`, `#[verifier::trusted_call]` | `fip-beta` | [Attributes](./reference-attributes.md#verifiertrusted_only-and-verifiertrusted_call) |
| Which proof obligation the solver is stuck on | `-V triage` | `fip` (1.100) | [`-V triage`](./reference-assert-by-tactic.md#finding-the-obligation-the-solver-is-stuck-on--v-triage) |
| Tactic scripts, expanded into checked proof code | `assert(P) by(tactic) { split(); intro(); cases(e); unfold(f, k); apply(L(a)); inst(..); smt(..); show(); .. }` | `fip` (1.100) | [assert ... by(tactic)](./reference-assert-by-tactic.md) |
| A proof checked on its own, with its own rlimit or solver | `isolate()`, `isolate(rlimit = N, backend = cvc5)` in a `by(tactic)` script; `#![verifier::tactic(isolate(..))]` on an `ensures` clause, `#[verifier::tactic(isolate(..))]` on a function | `fip` (1.100) | [`isolate`](./reference-assert-by-tactic.md#checking-a-proof-on-its-own-isolate) |
| rlimits and `isolate` kept out of the source, pinned to the code by a hash | a `.verus-hints` file (`-V hints=<path>`, `-V hints-locked`) | `fip` (1.100) | [`.verus-hints`](./reference-assert-by-tactic.md#keeping-the-rlimits-out-of-the-source-verus-hints) |

The new vstd items for these features are in `vstd::alloc_check` (marker traits such as
`AllocFreeDrop` and `NoDeallocDrop`, and the operator markers such as `FipAdd` and `FipOrd`).

## Changes that apply without the new options

The new checks run only when their option is given (`-V alloc-check`, `-V alloc-check-strict`,
`-V fip-lint`). These changes apply in every run:

* **New syntax.** The `allocates` clause is parsed and kept on every run. Without
  `-V alloc-check`, it is not checked and no bound is assumed from it.
* **`trusted_only` functions.** A function marked `#[verifier::trusted_only]` may be called only
  inside a `#[verifier::trusted_call]` block, and cannot be used as a value. vstd marks
  `Allocator::{deallocate, grow, grow_zeroed, shrink}` (and their implementations) and
  `UnsafeCell::{as_ref_unchecked, as_mut_unchecked, replace}` this way.
* **`--no-cheating`** rejects `#[verifier::trusted_call]` in the crate being verified.
* **Exec types decided by ghost code.** Verus type-checks the crate once with its ghost code, to
  verify it, and once without, to compile it. When only ghost code fixes the type of exec code (an
  integer literal that a `proof` block uses as a `u64`, for example), the compiled program gets
  another type (`i32`) and runs code that was not verified (upstream issue #3172). The erase run
  now compares the types of exec code, what it calls with which type arguments, and its literals,
  with the verified program, and reports an error where they differ. See
  [Ghost erasure](./erasure.md#exec-types-must-not-depend-on-ghost-code).
* **`-V fip-lint=fix`** cannot be combined with options that verify only part of the crate
  (`--no-verify`, `--verify-module`, `--verify-function`, `--no-lifetime`, ...), since a rewrite is
  kept only if the whole crate still verifies.
* **vstd.** Besides the modules above, the std specifications carry `allocates` bounds, and
  `vstd::std_specs::ptr` specifies `ptr::NonNull` (taken from upstream pull request #3258, which
  was not merged at the base commit).

## Tools and tests

* **verita** has a `use_verus_repo` key: a project with it is taken from the Verus repository
  being tested, instead of from `git_url`. `run_configuration_all.toml` uses it for vstd, whose
  sources must match the verifier.
* **rust_verify_test** finds `target-verus` next to the test binary as it was invoked, so the tests
  also work when `source/target` is a symbolic link. It also finds test binaries in the build
  directory layout of cargo 1.100.
* **`alloc_check_runtime`** (a test suite) runs verified programs with a counting
  `#[global_allocator]` at several optimization levels, and compares the allocator calls they make
  with their verified bounds.
* **Formatter and editor.** The syntax this fork adds (the `allocates` clause, bound
  specifications `T: Tr with { .. }`, and `become` in Verus code) is parsed by the `fip`
  branches of forks of [verusfmt](https://github.com/newsniper-org/verusfmt) and
  [verus-analyzer](https://github.com/newsniper-org/verus-analyzer). The released versions of
  both report it as a syntax error. (vstd is formatted with that verusfmt.)

## What is not changed

* **The SMT side.** The solver is unchanged: Z3, at the version that upstream pins. `air` (the
  encoding into SMT queries) encodes queries as upstream does. It adds two things:
  - `-V triage` runs its diagnostics in a solver process of its own;
  - `isolate(..)` checks a query in parts. This check is the one addition to what has to be
    trusted ([assert ... by(tactic)](./reference-assert-by-tactic.md#checking-a-proof-on-its-own-isolate)).
* **Command-line options.** No upstream option is removed or changes its meaning. The fork only
  adds options.

The fork has not been compared with upstream on code outside this repository's tests.
