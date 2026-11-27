# assert ... by(tactic) (fork)

> **Fork extension, experimental.** `by(tactic)` and `-V triage` exist only in this Verus fork.
> The Korean version of this page is [here](./reference-assert-by-tactic.ko.md).

When the SMT solver does not find a proof, you can tell it how to proceed, step by step, the
way an interactive theorem prover takes tactics:

```rust
assert(forall|i: int| 0 <= i < n ==> #[trigger] f(i) > i) by(tactic) {
    intro();
    apply(lemma_f(i));
}
```

Each step expands into ordinary proof code before the rest of `verus!` sees it: `assert`,
`assert ... by`, `assert forall ... implies ... by`, `if`, `match`, `reveal_with_fuel` and lemma
calls. That code is then checked like any other proof, and the block still ends with the
assertion of the goal. **A step changes how the goal is proved, never what is proved**: a
wrong step makes the proof fail, it cannot make a false assertion pass. The expansion is not
part of what you have to trust. (`isolate(..)` adds one small trusted check; see
[below](#checking-a-proof-on-its-own-isolate).)

### Syntax

```verus-grammar
V@[assert_by_tactic_stmt] ::=
    assert ( V@[spec_expr] ) by ( tactic ) { V@[tactic_item]* }

V@[tactic_item] ::= V@[tactic_step] ; | V@[stmt]
```

A script mixes steps with ordinary proof statements, which pass through as they are. A step is
a call of one of the names below, written as a bare name at the top of the script. A function
with the same name can still be called with a path (`self::split(x)`).

### Steps

The steps work on the current goal (`G` below), which starts as the asserted expression.

| Step | For the goal | Expands to |
|---|---|---|
| `have(Q)` | any | `assert(Q);`; `Q` is a fact for the rest of the script |
| `split()` | `A && B`, `{ &&& A &&& B }` | `assert(A) by { .. }; assert(B) by { .. };` |
| | `A <==> B` | `assert(A ==> B) by { .. }; assert(B ==> A) by { .. };` |
| | `if c { A } else { B }` | `if c { assert(A) by { .. } } else { assert(B) by { .. } }` |
| `intro()` | `forall\|x\| A ==> B` | `assert forall\|x\| A implies B by { .. }` |
| | `forall\|x\| B` | `assert forall\|x\| B by { .. }` |
| | `A ==> B` | `if A { assert(B) by { .. } }` |
| `cases(b)` (a `bool`) | any | `if b { assert(G) by { .. } } else { assert(G) by { .. } }` |
| `cases(e)` (a value of an enum) | any | `match e { E::A => assert(G) by { .. }, E::B(..) => assert(G) by { .. }, .. }`, an arm for each variant ([below](#cases-on-an-enum)) |
| `cases(match e { P => { .. }, .. })` | any | the `match`, with `G` asserted in every arm |
| `induct(n)` (a `nat`), `induct(i, from(lo))` (an `int`) | any | the base case and the step of an induction on the variable, each `assert(G) by { .. }`, and a vstd lemma ([below](#induction-induct)) |
| `unfold(f)`, `unfold(f, k)` | any | `reveal(f);`, `reveal_with_fuel(f, k);`; before a `split` or an `intro()` that needs it, also the goal with `f` unfolded ([below](#unfolding-the-goal-unfold-then-split)) |
| `apply(L(a))` | any | `L(a);` (its `ensures` become facts) |
| `inst(forall\|x: T\| Q, t)` | any | `assert(forall\|x: T\| Q); assert({ let x: T = t; Q });` |
| `smt()` | any | `assert(G);` |
| `smt(nonlinear_arith, R, ..)`, `smt(bit_vector, R, ..)` | any | `assert(G) by(nonlinear_arith) requires R, ..;` (or `bit_vector`) |
| `compute()` | any | `assert(G) by(compute);` |
| `show()` | any | nothing; a note with the goal and the facts the script added |
| `isolate()`, `isolate(rlimit = N, backend = cvc5)` | any | `assert(G) by { .. }`, checked as a part of the query of its own ([below](#checking-a-proof-on-its-own-isolate)) |

The `..` in a step's expansion is where the rest of the script goes.
- **Rest of the script.** After `split()` or `cases(e)`, it applies to each part. After
  `intro()`, it proves the new goal (`B`, with `x` in scope).
- **Parts with their own steps.** `split({ .. }, { .. })` and `cases(b, { .. }, { .. })` take one
  block of steps per part instead, and `cases(match ..)` takes the arms' blocks. The rest of the
  script then goes in those blocks: nothing may follow these forms.
- <a id="cases-on-an-enum"></a>**`cases(e)` on an enum.** The step takes the variants from the
  type of `e`: each arm has the rest of the script. An error names the variant whose case
  failed: the assertion of the goal in the arm says ``(`e` is `E::C`)``, and the assertions of
  the steps in the rest add ``where `e` is `E::C` ``. The `match` also checks that its arms cover every value. The arms do not bind the
  fields; to name them, use `cases(match ..)`. An enum with one variant has nothing to split
  (an error), and for a reference, write `cases(*e)`.
- <a id="unfolding-the-goal-unfold-then-split"></a>**Unfolding the goal: `unfold` then `split`.**
  When a `split` comes after `unfold(f)` and the goal as written is not one that `split` can
  split (a conjunction, an `<==>` or an `if`; a call of `f`, say), or an `intro()` that the goal
  as written does not fit (a `forall` or an `==>`), `unfold(f)` also works on the goal: rust_verify replaces each call of `f` in it by `f`'s body (one level: the calls of `f` in
  the body stay calls), with the arguments in place of the parameters, and the rest of the
  script proves that goal. `split` then splits it into its parts (a conjunction, or an `if` with
  an `else`; an `<==>` is not split there yet), and `intro()` proves the body of its `forall`
  (whose variables are not named in the script) or the conclusion of its `==>` under the
  condition. `show()` shows the goal as the text of `f`'s body, with the arguments in place of
  the parameters listed after it.
  - Between the `unfold` and the `split` there may be `have`, `apply`, `inst`, `show`, `cases(b)`
    and `isolate`. Another `unfold(g)` there works on the result when the goal calls `f`
    (`unfold(f); unfold(g); split()`); otherwise only the `unfold` nearest the `split` works on the
    goal, and the ones before it only reveal their function. For a function inside one part, use
    a block: `unfold(f); split({ unfold(g); split(); }, { .. })`.
  ```rust
  #[verifier::opaque]
  spec fn inv(x: int) -> bool { x > 0 && x < 10 && x != 5 }
  proof fn p(x: int) requires x == 5 {
      assert(inv(x)) by(tactic) { unfold(inv); split(); }
      // error: assertion failed, at `x != 5` in `inv`'s body
      // (from the tactic step `split` (part 3 of 3, after `unfold`))
  }
  ```
  - The unfolded goal is asserted after `f` is revealed, and the goal of the step is still
    asserted after it, so the unfolding changes only how the goal is proved.
  - `f` is a spec function that is not a trait method, whose body is visible here; it may be in
    another crate (with a public body), generic, opaque or recursive (but not with a
    `decreases .. when` clause, yet). Its body must be an expression (no proof block). A proof
    in `f` (or in a function that it unfolds) may not unfold the function being defined: that is
    an error. An argument that goes into a trigger of `f`'s body must be one that a trigger can
    hold (not a closure, a comparison or a boolean operator): bind it to a variable first.
  - After `unfold` and `split()`, the rest of the script is shared by the parts, whose goals are
    not known when it is expanded: there, no step may look at the goal (`unfold` before a
    `split` or an `intro`, `split`, `intro`). Give each part its own block, `split({ .. }, { .. })`, for such
    steps. `induct` after such an `unfold` is not supported.
- <a id="induction-induct"></a>**Induction: `induct`.** `induct(n)` proves the goal `G` for a
  variable `n` of type `nat` by induction on `n`. The goal as a function of `n`
  (`let p = |n: nat| G`) is proved for `n == 0` (the base case) and, for `n > 0`, from the goal
  for `n - 1` (the step), each as an `assert forall`; then
  `vstd::tactic::lemma_induct_nat(p, n)` gives the goal for `n`. These `assert forall`
  statements are the lemma's `requires`, so nothing is assumed.
  - The rest of the script proves both cases; `induct(n, { .. }, { .. })` takes a block for each
    instead, and then nothing may follow it.
  - `induct(i, from(lo))` does the same for an `int` from `lo`. It needs `lo <= i`: if that does
    not hold, the error is a failed precondition of `vstd::tactic::lemma_induct_int_from`. `lo`
    may not use `i`.
  - The cases see the function's `requires` and the conditions around the assertion. But in the
    cases, `n` is a new variable: what those facts say about `n` is about the `n` outside, and
    does not hold for it (the base case is checked at `n == 0` whatever they say). To use a
    hypothesis about `n`, put it in the goal, `assert(H ==> G) by(tactic) { induct(n); intro(); .. }`,
    or, for an `int`, start at its bound with `from(lo)`. Other variables are not generalized
    either: a variable defined from `n` before the assertion keeps its value in the step.
  - It needs vstd.
- **Steps that close the goal.** `smt(..)` and `compute()` prove the goal; nothing may follow
  them, neither a step nor a statement.
- **When the script ends.** If the script ends without closing the goal, the solver proves it
  from what the script has established.

```rust
proof fn t(x: int, y: int) {
    assert(f(x) > x && f(y) > y) by(tactic) {
        split({ apply(lemma_f(x)); }, { apply(lemma_f(y)); });
    }
    assert(x * x >= 0) by(tactic) {
        cases(x >= 0, { smt(nonlinear_arith, x >= 0); }, { smt(nonlinear_arith, x < 0); });
    }
    assert(sum(3) == 6) by(tactic) { unfold(sum, 4); }
}
```

When an assertion that `have`, `inst`, `split`, `cases`, `induct`, `smt()` or `intro` (on an `==>`)
generated fails, the error says which step it came from (for `induct`, whether it was the base case
or the step). For `intro` on a `forall` written in the goal, `smt(<prover>, ..)` and
`compute()`, it points at the goal without naming the step; on the goal after `unfold`, `intro`
names the step (`intro` (after `unfold`)).

```
error: assertion failed
   |
   |     assert(x > 0 && y > 0) by(tactic) { split(); }
   |                     ^^^^^
   |                     assertion failed
   |                     note: from the tactic step `split` (part 2 of 2)
```

The goal is asserted where the step puts it, so a name means what it means there. A `let` in the
script that reuses a name the goal uses changes what the later steps assert (the goal itself is
still checked as written, at the end). A pattern in `cases(match ..)` may not bind a name the goal
uses; that is an error. `split()` does not take an `if let` goal; use `cases(match ..)`.

### What a script may not do

- **No new assumptions.** `assume`, `admit` and `inline_air_stmt` are errors anywhere in the
  script. That includes nested blocks, closures, the blocks the steps generate, and code that a
  macro expands to.
- **No functions or constants.** A script may not declare them, because their bodies would be
  checked on their own, outside the script.

Calls of lemmas work as everywhere else; an `external_body` lemma is trusted wherever it is
called.

### `show()`

`show()` prints the goal at that step and the facts the script added before it (`have`, the
condition of a case, what `intro` introduced). It works on the source text, at macro-expansion
time (after `unfold`, rust_verify makes the note instead, from the text of the unfolded bodies,
with the arguments in place of the parameters listed after it), so:
- the facts of the context, such as `requires` and the statements before the assertion, are
  not listed;
- nothing it prints has been checked yet;
- it prints even when the proof later fails, and also when verification passes;
- after a bare `cases(e)`, the rest of the script is expanded once for all the cases (the type of
  `e` is not known yet), so `show()` prints one note that names `e` but not the case. To see
  each case's condition, use `cases(b, { ..; show(); }, { ..; show(); })` or `cases(match ..)`.

### Checking a proof on its own: `isolate`

`isolate()` makes the rest of the script (the proof of the current goal, and the assertion of
the goal at its end) a part of the function's query of its own. With `isolate(rlimit = N)`, that
part gets its own rlimit, in the units of `#[verifier::rlimit(N)]` (`infinity` for none).
Everything else in the function is checked with the function's rlimit.

```rust
#[verifier::rlimit(1)]
proof fn p() {
    assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
    // .. the rest of the proof, checked with rlimit 1
}
```

The query is checked once for each part, with the assertions of the other parts disabled, and it
counts as verified only if every part is. The assertions in each part are those of the same
query, with the same facts before them. Disabling the assertions of the other parts only leaves
out what those parts check, not what they assume. This check is the one thing `by(tactic)` adds
to what has to be trusted:
- every assertion is in exactly one part;
- a query is valid exactly when each part is.

For why the second holds, see `smt_check_partitions` in `air/src/smt_verify.rs`.

- **Several parts.** `isolate` may be used more than once, in parts of a `split`, and in an
  isolated proof (each assertion goes to the innermost one).
- **Inside a loop body.** There, the part belongs to the loop body's query. This also works in
  the body of a `#[verifier::nonlinear]` function.
- **Order.** The isolated proofs are checked first, and the rest of the function last, wherever
  it is in the source.
- **When a part fails.** The parts after it are not checked, and a note says so. So an error in
  the rest of the function, even one before the isolated proof, is reported only once the
  isolated proofs pass.
- **When a part exceeds its rlimit.** The error points at the isolated goal.
- **Another solver.** `isolate(backend = cvc5)` (or `backend = z3`) checks the isolated proof
  with that solver.
  - It runs in a solver process of its own, with the same query.
  - The query counts as verified only if both solvers find their parts valid.
  - The part's `rlimit` applies to its solver.
  - It is checked after the run's solver has checked the rest of the query, whatever that
    found; **Order** and **When a part fails** hold among the parts that the run's solver
    checks. Errors of both are reported.
  - cvc5 reads the queries only in the encoding for it. So `backend = cvc5` needs
    `-V cvc5-smtlib` (Z3, with queries that cvc5 also reads) or `-V cvc5`; otherwise it is an
    error.
- **cvc5 as the run's solver.** The run's cvc5 cannot change its rlimit once it has started (nor
  can `#[verifier::rlimit]` apply). So a part with an `rlimit` is checked by a cvc5 process of its
  own, as for `backend = cvc5`.
- **`ensures` clauses.** `#![verifier::tactic(isolate(..))]` at the start of an `ensures` clause
  makes the clause's checks, at every return, a part of their own, with the same options. On a
  function, `#[verifier::tactic(isolate(..))]` does this for all its `ensures` clauses together
  (not on a trait method declaration: put it on the implementations).
  See [the attribute](./reference-attributes.md#verifiertacticisolate-and-verifiertacticisolate).
- **Not checked in parts.** Queries that only report are checked as a whole: recommends,
  `--expand-errors`, the `--profile` rerun and `-V triage`. A `by(bit_vector)` assertion, and a
  `#[verifier::bit_vector]` or `#[verifier::integer_ring]` function, is a single query with no
  parts (an `isolate` there has no effect).

## Keeping the rlimits out of the source: `.verus-hints`

An rlimit that a proof needs depends on the machine and the solver version. A hints file keeps
such settings out of the source. It says only *how* an obligation is checked, never *what*: a
function's rlimit, and which of its `ensures` checks are a part of the query of their own
(`isolate`, with its rlimit and solver). So a hint, applied or not, cannot make a program verify
that does not hold.

```toml
# .verus-hints
[[hint]]
function = "m::f"            # the function's path in the crate (or `crate::m::f`)
hash = "2b0eec1c584267d1"    # the code the hint is for
rlimit = 30                  # as #[verifier::rlimit(30)]; a number, or "infinity"

[[hint]]
function = "m::g"
ensures = 2                  # the second `ensures` clause; or proof_note = "the clause's note"
hash = "4bad7b5d14bdf35f"
isolate = { rlimit = 10, backend = "cvc5" }   # as #![verifier::tactic(isolate(..))] on it

[[hint]]
function = "m::h"
hash = "05a5f377e6de6c25"
isolate = {}                 # all its `ensures` clauses, as #[verifier::tactic(isolate())] on h
```

- **Where.** `-V hints=<path>` (relative to the directory Verus runs in), or else the first
  `.verus-hints` found in the directory of the crate root file and its parents, up to the nearest
  one with a `Cargo.toml`. With cargo, `-V hints` is for the packages being verified (the primary
  packages); a crate that is not verified (`--no-verify`, such as a dependency) takes no hints.
  When the file changes, cargo checks the crate again.
- **Names.** A function is named by its path in the crate (`m::f`, `S::f`), with or without
  `crate::` in front, or by rustc's full path (`<S as T>::f`), which tells apart methods of the
  same name in several `impl`s. If a name stands for several functions, the hint is for the one
  whose code the hash matches.
- **Several crates, one file.** A package's library, binaries and tests share its
  `.verus-hints`. `root = "src/main.rs"` (relative to the hints file) says which crate a hint is
  for; other crates skip it.
- **What a hint does.** A hint replaces the attribute it stands for: `#[verifier::rlimit(..)]`,
  or `isolate` on the function or on the clause. Only the functions of the crate being verified
  take hints; crates that use it do not see them.
- **The hash.** Each hint is pinned to the code it was written for by a hash of that code's text,
  with the whitespace normalized: the whole function for a hint about a function, the clause for
  a hint about a clause. Write a hint without a `hash` first: Verus does not apply it, and its
  warning shows the entry with the hash of the current code, to paste into the file. (For a
  function that a `macro_rules!` macro generates, the hash covers the macro's text, not the
  arguments of its call.)
- **A hint that does not apply** is not applied: the obligation is checked as the source alone
  says, with a warning. If its hash does not match the code or it has none, the warning shows
  the entry for the current code (one per function, if the name stands for several). If there is
  no such function, clause or body to check, the warning says so. With `-V hints-locked` (for
  CI), such a hint is an error.
- **Errors.** These hints are errors, with or without `-V hints-locked`:
  - a key other than those above;
  - both `ensures` and `proof_note`, or `ensures` less than 1;
  - a hint for a clause with `rlimit` (put it in `isolate = { rlimit = .. }`), or without
    `isolate`; a hint for a function with neither `rlimit` nor `isolate`;
  - an rlimit that is not a number (at least 0) or `"infinity"`;
  - a backend other than `"z3"` and `"cvc5"`, or `backend = "cvc5"` without the encoding for cvc5
    (`-V cvc5-smtlib` or `-V cvc5`);
  - `isolate` for a trait method declaration;
  - a `proof_note` that several clauses of the function have;
  - the same function or clause as another hint.
- When hints are applied, a note says how many and from which file.

## Finding the obligation the solver is stuck on: `-V triage`

With `-V triage`, when a function fails to verify or exceeds the rlimit, Verus checks each of
its proof obligations again on its own, the others disabled, and reports the ones that are not
proved alone:

```
note: triage of the function body check: 15 proof obligations, each checked alone with the
      others disabled: 14 proved, 0 not proved, 1 exceeded the rlimit
note: triage (7/15): postcondition not satisfied: exceeded the rlimit alone
```

The kinds of answer:
- **"exceeded the rlimit alone"**: the obligation is too expensive by itself.
- **"the solver found a counterexample"**: the obligation does not follow from the facts in the
  query. This is rare with Z3 as Verus runs it, which answers `unknown` instead.
- **"the solver gave up on nonlinear arithmetic"**: comes with a hint about `by(nonlinear_arith)`.
- **`unknown (incomplete quantifiers)`**: Verus's usual answer for an obligation it does not
  prove, whether the obligation holds or not.

When the query exceeded the rlimit, up to three obligations that are proved alone but use at
least a tenth of the rlimit are listed too (Z3 only: cvc5 does not report the resources a check
used). If every obligation is proved alone, the summary says that only all of them together
exceed the rlimit.

This is diagnostics only:
- the result of verification does not change;
- the checks run in a solver process of their own, so the other queries are not affected;
- only Z3 and cvc5 are triaged;
- `by(bit_vector)` queries, recommends checks and `--expand-errors` reruns are not triaged.
