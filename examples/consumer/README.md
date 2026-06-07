# Consumer justfile example

A copy-paste `justfile` for a project that uses this verus-fork as its
verification toolchain — verifying Verus code with a **pluggable SMT backend**
(z3 / cvc5 / oxiz / **adsmt**), warming an **adsmt AOT prelude bank** (§3.5.H)
for faster checks, cross-checking backends, and emitting the adsmt certificate
to **Isabelle/HOL or Rocq**.

The motivating consumer is **Y4** (`github.com/newsniper-org/y4`), which unifies
a fragmented verification workflow — seL4 verified in Isabelle/HOL, new code
verified in Verus — by routing both through **adsmt as the common engine**:

```
Verus code ──▶ adsmt (verify) ──▶ adsmt-cert ──▶ adsmt-emit-isabelle ──▶ .thy
                                                  (~/adsmt-contrib)        │
                                                                          ▼
                                          merges into the same logic as the
                                          seL4 Isabelle/HOL proofs
```

## Usage

1. Copy `justfile` into your project root.
2. Adjust the `_*` variables at the top (or set the matching env vars):
   - `VERUS_FORK` — path to a built verus-fork checkout (`vargo build --release`).
   - `VERUS_ADSMT_PATH` — your `lu-smt` binary.
   - `VERUS_SRC` — your top-level Verus source/crate.
   - `VERUS_FLAGS`, `VERUS_ADSMT_AOT_CACHE_DIR`, `ADSMT_CERT_DIR` — optional.
3. `just --list`.

## Recipes

| recipe | what it does |
|---|---|
| `verify` | verify with the default z3 backend |
| `verify-adsmt` | verify with the adsmt backend (`-V adsmt`) |
| `verify-cvc5` / `verify-oxiz` | the other pluggable backends |
| `verify-adsmt-fast` | bake the §3.5.H AOT prelude bank, then verify with it activated |
| `aot-bake` | (re)bake the bank + print its `export VERUS_ADSMT_AOT_LUART=…` line |
| `cross-check` | verify with z3 **and** adsmt, diff the verdict (differential soundness audit) |
| `emit-isabelle` / `emit-rocq` | emit the adsmt cert to a proof assistant via `~/adsmt-contrib` |

## Soundness notes

- The adsmt backend is sound across all paths (baseline / `--aot-load` /
  `--jit-trace-load`) since **rc.28** (the opaque-assert-masks-`false` P0 fix +
  its AOT-path extension), and complete on OR-of-AND structure since **rc.29**
  (Tseitin). Pin `EXPECTED_ADSMT_VERSION` accordingly.
- `cross-check` is a cheap guard while you're still gaining trust in a new
  backend: if z3 and adsmt ever disagree on a verdict, that's a soundness bug —
  capture a minimal reproducer and file it.
- The AOT bank's cache key is `(sha256 of the baked SMT-LIB text, lu-smt
  version)`, so a prelude change or an `lu-smt` bump never serves a stale bank.
