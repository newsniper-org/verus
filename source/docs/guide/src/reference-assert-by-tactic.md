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
| `cases(b)` | any | `if b { assert(G) by { .. } } else { assert(G) by { .. } }` |
| `cases(match e { P => { .. }, .. })` | any | the `match`, with `G` asserted in every arm |
| `unfold(f)`, `unfold(f, k)` | any | `reveal(f);`, `reveal_with_fuel(f, k);` |
| `apply(L(a))` | any | `L(a);` (its `ensures` become facts) |
| `inst(forall\|x: T\| Q, t)` | any | `assert(forall\|x: T\| Q); assert({ let x: T = t; Q });` |
| `smt()` | any | `assert(G);` |
| `smt(nonlinear_arith, R, ..)`, `smt(bit_vector, R, ..)` | any | `assert(G) by(nonlinear_arith) requires R, ..;` (or `bit_vector`) |
| `compute()` | any | `assert(G) by(compute);` |
| `show()` | any | nothing; a note with the goal and the facts the script added |
| `isolate()`, `isolate(rlimit = N, backend = cvc5)` | any | `assert(G) by { .. }`, checked as a part of the query of its own ([below](#checking-a-proof-on-its-own-isolate)) |

The `..` in a step's expansion is where the rest of the script goes.
- **Rest of the script.** After `split()` or `cases(b)`, it applies to each part. After
  `intro()`, it proves the new goal (`B`, with `x` in scope).
- **Parts with their own steps.** `split({ .. }, { .. })` and `cases(b, { .. }, { .. })` take one
  block of steps per part instead, and `cases(match ..)` takes the arms' blocks. The rest of the
  script then goes in those blocks: nothing may follow these forms.
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

When an assertion that `have`, `inst`, `split`, `cases`, `smt()` or `intro` (on an `==>`) generated
fails, the error says which step it came from. For `intro` on a `forall`, `smt(<prover>, ..)` and
`compute()`, it points at the goal without naming the step.

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
time, so:
- the facts of the context, such as `requires` and the statements before the assertion, are
  not listed;
- nothing it prints has been checked yet;
- it prints even when the proof later fails, and also when verification passes.

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
