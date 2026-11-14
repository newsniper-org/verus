# Pluggable SMT backends (fork)

> **This page describes a fork of Verus.** The branch `backend-pluggable-beta` is `fip-beta` (see
> [Changes from upstream Verus](./fork-changes.md)) plus the changes on this page: two more SMT
> solvers that Verus can run, adsmt and OxiZ, and the options that go with adsmt. A Korean
> version of this page is [here](./fork-changes-backend-pluggable.ko.md).
>
> All of this is experimental. Z3 stays the default solver. A result from adsmt or OxiZ is not a
> substitute for a result from Z3.

## Solvers

Upstream Verus runs Z3 by default, and cvc5 with `-V cvc5`. This branch adds:

| Option | Solver | Executable | Path override | Version Verus expects |
|---|---|---|---|---|
| `-V oxiz` | OxiZ, a reimplementation of Z3 in Rust | `oxiz` | `VERUS_OXIZ_PATH` | `0.2.4` |
| `-V adsmt` | adsmt, an abductive-deductive solver | `lu-smt` | `VERUS_ADSMT_PATH` | `1.0.0-rc.42.1` |

Verus finds the executable as it finds Z3 and cvc5: the path in the variable if it is set, the
executable name otherwise. It also checks the solver's version as it does for them; the expected
versions are in `tools/common/consts.rs`.

With `-V adsmt`, the SMT queries change in one way: a `(distinct ...)` with more than 48 operands
is written as pairwise disequalities. When this was added, adsmt's native engine modeled an
uninterpreted sort as a finite domain of about 52 elements. A larger `distinct` (Verus's prelude
has one over the fuel identifiers) then made every query unsatisfiable, so every function
"verified". The limit is `[package.metadata.adsmt] distinct_max_arity` in
`source/air/Cargo.toml`, read at build time. The other solvers get the queries unchanged.

## A fourth verdict: abductive

An SMT query has three results in upstream Verus: valid, invalid (with a model), and unknown.
adsmt can give a fourth: *abductive*, a list of ranked candidate hypotheses that would make the
query valid. Verus reports it as a verification failure, with the candidates in the error
message. Two options control it (both do nothing with the other solvers):

* `-V report-abductive-on-unknown`: when adsmt returns an abductive verdict, also put the
  candidates into the JSON output (`--output-json`, field `abductive_candidates`).
* `-V request-abductive-on-unknown`: when adsmt does not verify a query, ask it to search for a
  missing hypothesis (verify-or-explain), and report the result as an abductive verdict.

## Certificates and proof assistants

adsmt can write a certificate for each query it proves. On this branch:

* `ADSMT_CERT_DIR=<dir>` makes Verus pass `--emit-cert-dir <dir>` to adsmt, which then writes one
  certificate per proved query. `VERUS_ADSMT_CERT_FORMAT` (`cbor` or `json`) selects the format;
  adsmt's default is `cbor`.
* `-V emit-isabelle[=<dir>]` and `-V emit-rocq[=<dir>]`: after a `-V adsmt` run with no errors,
  turn each certificate in `ADSMT_CERT_DIR` into an Isabelle/HOL theory or a Rocq file, by running
  `adsmt-emit run isabelle` (or `rocq`). The default output directory is
  `$ADSMT_CERT_DIR/emit-isabelle` (or `emit-rocq`). `VERUS_ADSMT_EMIT_PATH` names the `adsmt-emit`
  executable. This needs an installed `adsmt-emit` and its emitters.

  **Known issue, not fixed:** the Isabelle emitter writes every assumption of a certificate as an
  axiom. For a proof by refutation those assumptions include the negated goal and are jointly
  unsatisfiable, so the theory it writes is inconsistent and proves any statement. This has been
  reported to adsmt. Until it is fixed, an emitted theory is not evidence that anything holds, and
  must not be imported into another development.

## Other adsmt options

* `-V emit-lukb`: write each query also as a `.lukb` file (adsmt's own input language) into the
  log directory (`--log-dir`, or `.verus-log` by default). Constructs it cannot express yet become `#` comments. The `.lukb` file is a log
  only: the verdict still comes from the SMT-LIB query.
* `-V jit-trace-load=<path>` (or `VERUS_ADSMT_JIT_TRACE`) and `VERUS_ADSMT_AOT_LUART`: pass a
  replay trace and a precompiled prelude to adsmt (`--jit-trace-load`, `--aot-load`). They are
  meant to change how fast adsmt answers, not what it answers. `scripts/aot-bake-prelude.sh` makes
  both.
* **`verus.toml` and adsmt's manifest.** With `-V adsmt`, if `ADSMT_CAS_MANIFEST` is not set,
  Verus sets it to the nearest `verus.toml`, so adsmt can read an `[adsmt.cas]` table from it.
  An `adsmt.toml` in the current directory or above still takes precedence. Verus passes the
  path only; it does not read the table.

## Repository additions

* `scripts/`: `aot-bake-prelude.sh` (see above), `a2-abduction-regression.sh` (a regression run
  of `-V request-abductive-on-unknown` on the fixtures in `scripts/a2-fixtures/`), and
  `snapshot-status.sh` (a progress snapshot for the people working on the fork). The `justfile`
  runs the first and the last (`just aot-bake-prelude`, `just status`) and has recipes for the
  fork's own bookkeeping. `examples/consumer/` is a `justfile`
  for a project that uses this fork with several backends.
* `docs/roadmap-interactive-tooling.md`: plans for interactive tooling on top of the backends.
* The `.local-*` directories and `.claude-memories/` hold working notes and the correspondence
  with the adsmt project (requests, replies, reproductions). They do not affect how Verus runs.

## `backend-pluggable-inline-beta`

The branch `backend-pluggable-inline-beta` is `backend-pluggable-beta` plus a design memo for
*inline proofs*: proof fragments in another language (an SMT query with its own logic and
backend, MaxSAT/MaxSMT, ASP, or an interactive prover) embedded in a Verus proof, much as inline
assembly is embedded in code. The memo is in `.local-backlog/inline-proof/`. It is at the
discussion stage and waits on adsmt's input language. The branch does not change Verus.
