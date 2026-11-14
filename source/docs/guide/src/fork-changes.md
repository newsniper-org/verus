# Changes from upstream Verus (fork)

> **This page describes a fork of Verus.** It lists what the `fip-beta` branch of this fork changes
> relative to upstream Verus ([verus-lang/verus](https://github.com/verus-lang/verus)), and links
> to the pages that describe each change. A Korean version of this page is
> [here](./fork-changes.ko.md).

## Base and branches

The fork branches off upstream at commit `8bf68ee74` (2026-11-02, "Update no-cheating to disallow
various command-line flags that violate the spirit of not cheating", #3392). Its changes come in
two layers:

| Branch | Toolchain | Adds |
|---|---|---|
| `fip` | Rust 1.99.1 (as upstream) | allocation bounds: the `allocates` clause, `-V alloc-check`, `-V alloc-check-strict`, bounds in vstd's std specifications |
| `fip-beta` | Rust 1.100.0-beta.10 (`beta-2026-11-05`) | everything in `fip`, plus Rust 1.100, custom allocators and allocator state, fully in-place functions, `-V fip-lint`, `trusted_only`/`trusted_call` |

Everything on this page is in `fip-beta`. The column "since" in the tables below says which of the
two branches introduced it.

All of the new verification features are experimental.

## Toolchain: Rust 1.100 beta

`rust-toolchain.toml` (and the CI workflows) select `beta-2026-11-05`, that is Rust
1.100.0-beta.10, where upstream uses 1.99.1. The parts of rustc that Verus carries in its own
source tree (`rustc_hir_analysis`, `rustc_hir_typeck`, `rustc_mir_build`) are updated to the
same version.

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
| Custom allocators | `unsafe impl BoundedAllocator for A`, then `Vec<T, A>`, `Box<T, A>`, ... | `fip-beta` | [Custom allocators](./reference-allocates.md#custom-allocators) |
| Allocators with a state | `vstd::alloc_heap` (`allocator_state`, `AllocAuth`) | `fip-beta` | [Allocators with a state](./reference-allocates.md#allocators-with-a-state) |
| Bound specifications | `T: Tr with { .. }` on type parameters, in `where` clauses, impls and structs | `fip-beta` | [Bound specifications](./reference-allocates.md#bound-specifications-t-tr-with---) |
| Fully in-place functions (no deallocation) | `#[verifier::fip]` | `fip-beta` | [FIP and FBIP](./fip-fbip.md), [reference](./reference-allocates.md#fully-in-place-functions-verifierfip) |
| Constant stack space | `#[verifier::fip(strict)]` with `become` | `fip-beta` | [reference](./reference-allocates.md#constant-stack-space-verifierfipstrict) |
| Generic operator calls in fip code | `T: FipAdd`, `T: FipOrd`, ... (`FbipOp`, `FipOp`, `FipStrictOp` for each operator trait of `core`) | `fip-beta` | [Operator traits](./reference-allocates.md#operator-traits-fipadd-fipord-) |
| Stack-growth linter | `-V fip-lint`, `-V fip-lint=fix` | `fip-beta` | [FIP and FBIP: Tools](./fip-fbip.md#tools) |
| Calls whose safety cannot be specified | `#[verifier::trusted_only]`, `#[verifier::trusted_call]` | `fip-beta` | [Attributes](./reference-attributes.md#verifiertrusted_only-and-verifiertrusted_call) |

The new vstd items for these features are in `vstd::alloc_check` (marker traits such as
`AllocFreeDrop`, `NoDeallocDrop`, `BoundedAllocator`, `FipAllocator`, and the operator markers
such as `FipAdd` and `FipOrd`), `vstd::alloc_heap`, and
`vstd::resource::impls::preorder_auth` (`PreorderAuth`, an authoritative state with an exclusive
lower-bound fragment, which the allocator heap uses).

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

## What is not changed

* **The SMT side.** `air` (the encoding into SMT queries) is unchanged, and so is the solver: Z3,
  at the version that upstream pins.
* **Command-line options.** No upstream option is removed or changes its meaning. The fork only
  adds options.

The fork has not been compared with upstream on code outside this repository's tests.
