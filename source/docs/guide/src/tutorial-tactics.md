# Walkthrough: tactic scripts, induction, `isolate`, `.verus-hints`, `-V triage` (fork)

> **Fork extension.** This page walks through the proof tools that are new in this fork, step by
> step. The page with all the rules is [assert ... by(tactic)](./reference-assert-by-tactic.md). The
> Korean version of this page is [here](./tutorial-tactics.ko.md).

## Before you start

The code on this page is in two files of the repository. Both are checked by the tests
(`examples` in `rust_verify_test`), so the code here matches what Verus does.

- `examples/guide/tactics_tutorial.rs`: examples that verify
- `examples/guide/tactics_tutorial_errors.rs`: examples that fail on purpose (to see the errors)

In a built repository:

```
cd source
source ../tools/activate
./target-verus/release/verus ../examples/guide/tactics_tutorial.rs --crate-type lib
#   verification results:: 32 verified, 0 errors
./target-verus/release/verus ../examples/guide/tactics_tutorial_errors.rs --crate-type lib
#   verification results:: 4 verified, 4 errors
```

To follow along, copy a file and change it as each "Try it" says.

**One thing to remember:** the steps of `assert(P) by(tactic) { .. }` decide *how* `P` is proved,
never *what* is proved. A step becomes ordinary proof code (`assert`, `assert .. by`, `if`,
`match`, lemma calls, `reveal`) that is checked, and at the end of the script `P` is asserted again
as written. A wrong step makes the proof fail; it cannot make a false assertion pass. `assume` and
`admit` are not allowed in a script.

## Step 1: a first script, `split()`

```rust
proof fn t_split(x: int, y: int)
    requires
        x > 0,
        y > 0,
{
    assert(x > 0 && y > 0) by(tactic) {
        split();
    }
}
```

- `split()` splits the goal `x > 0 && y > 0` into two parts and asserts each.
- At the end of the script, `x > 0 && y > 0` is asserted once more.

**Try it.** Remove `y > 0` from the `requires`. The error points at the second part, and the note
says which step made the assertion.

```rust
proof fn e_split(x: int, y: int)
    requires
        x > 0,
{
    // FAILS at `y > 0`: from the tactic step `split` (part 2 of 2)
    assert(x > 0 && y > 0) by(tactic) {
        split();
    }
}
```

```
error: assertion failed
   |
   |     assert(x > 0 && y > 0) by(tactic) {
   |                     ^^^^^
   |                     |
   |                     assertion failed
   |                     note: from the tactic step `split` (part 2 of 2)
```

Besides `A && B`, `split()` splits `A <==> B` (into the two directions), `if c { A } else { B }`
(into the two branches) and `{ &&& A &&& B }`.

## Step 2: adding facts, `apply`, `have`, a block for each part

```rust
spec fn f(x: int) -> int {
    x + 1
}

proof fn lemma_f(x: int)
    ensures
        f(x) > x,
{
}

proof fn t_apply(x: int, y: int) {
    assert(f(x) > x && f(y) > y) by(tactic) {
        split({ apply(lemma_f(x)); }, { apply(lemma_f(y)); });
    }
    assert(f(f(x)) > x) by(tactic) {
        apply(lemma_f(x));
        apply(lemma_f(f(x)));
        have(f(f(x)) > f(x));
    }
}
```

- `apply(lemma_f(x))` calls the lemma; its `ensures` (`f(x) > x`) is a fact from then on.
- `have(Q)` asserts `Q` and uses it as a fact from then on: an intermediate step for the solver.
- `split({ .. }, { .. })` takes a block of steps for each part: the first proves `f(x) > x`, the
  second `f(y) > y`. Nothing may follow a form that takes blocks.
- After a `split()` without blocks, the steps that follow run *in each part*.

**Try it.** In the second assertion, remove `apply(lemma_f(f(x)));`. The `have` fails, and the note
says `from the tactic step `have``.

## Step 3: `forall` and `==>`, `intro()`

```rust
proof fn t_intro(n: int) {
    assert(forall|i: int| 0 <= i < n ==> #[trigger] f(i) > i) by(tactic) {
        intro();
        apply(lemma_f(i));
    }
    assert(n > 0 ==> f(n) > 1) by(tactic) {
        intro();
        apply(lemma_f(n));
    }
}
```

- On `forall|i| A ==> B`, `intro()` gives `assert forall|i| A implies B by { .. }`; the steps that
  follow can use `i` by its name.
- On `A ==> B`, it gives `if A { assert(B) by { .. } }`.

## Step 4: a `forall` fact at a given term, `inst`

```rust
uninterp spec fn g(x: int) -> int;

proof fn t_inst(a: int)
    requires
        forall|x: int| #[trigger] g(x) >= 0,
{
    assert(g(a + 1) >= 0) by(tactic) {
        inst(forall|x: int| #[trigger] g(x) >= 0, a + 1);
    }
}
```

- `inst(fact, t)` asserts `fact`, then the fact with `t` in place of the variable.
- Use it when the solver does not instantiate the fact by itself (no matching trigger). Give one
  term per variable (`inst(forall|x, y| Q, a, b)`).

## Step 5: cases, `cases`

By a `bool` condition:

```rust
proof fn t_cases_bool(x: int) {
    assert(x * x >= 0) by(tactic) {
        cases(x >= 0, { smt(nonlinear_arith, x >= 0); }, { smt(nonlinear_arith, x < 0); });
    }
}
```

- `cases(b, { .. }, { .. })` gives a block for the case where `b` holds and one where it does not.
- `smt(nonlinear_arith, R, ..)` proves the goal as `assert(G) by(nonlinear_arith) requires R, ..;`.
  It closes the goal: nothing may follow it (the same for `smt()` and `compute()`).

By the value of an enum:

```rust
enum Shape {
    Dot,
    Line(u64),
    Rect(u64, u64),
}

spec fn corners(s: Shape) -> nat {
    match s {
        Shape::Dot => 1,
        Shape::Line(_) => 2,
        Shape::Rect(_, _) => 4,
    }
}

proof fn t_cases_enum(s: Shape) {
    // one case per variant
    assert(corners(s) >= 1) by(tactic) {
        cases(s);
    }
    // the fields, named by a pattern
    assert(corners(s) <= 4) by(tactic) {
        cases(match s {
            Shape::Rect(w, h) => { have(corners(s) == 4); },
            _ => { },
        });
    }
}
```

- `cases(s)` takes the variants from the type of `s` and makes one case per variant. When one
  fails, the error says which variant (`` (`s` is `Shape::Line`) ``).
- To name the fields, use `cases(match ..)` with a block per arm; the goal is asserted in every arm.

## Step 6: unfolding functions, `unfold`

```rust
spec fn sum(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + sum((n - 1) as nat)
    }
}

#[verifier::opaque]
spec fn inv(x: int) -> bool {
    0 < x && x < 10 && x != 5
}

proof fn t_unfold(x: int)
    requires
        x == 3,
{
    // more fuel for a recursive function
    assert(sum(3) == 6) by(tactic) {
        unfold(sum, 4);
    }
    // the body of an opaque function, split into its parts
    assert(inv(x)) by(tactic) {
        unfold(inv);
        split();
    }
}
```

- `unfold(sum, 4)` is `reveal_with_fuel(sum, 4)`: the recursive function can be unfolded that far.
- `inv` is opaque, so the solver does not see its body. When `split()` follows `unfold(inv)`,
  `unfold` replaces `inv(x)` in the goal with the body `0 < x && x < 10 && x != 5` (one level), and
  `split()` splits its three parts.

**Try it.** With `x == 5`, the third part fails, and the error points at `x != 5` in the body of
`inv`:

```rust
#[verifier::opaque]
spec fn inv(x: int) -> bool {
    0 < x && x < 10 && x != 5
}

proof fn e_unfold(x: int)
    requires
        x == 5,
{
    // FAILS at `x != 5` in the body of `inv`:
    // from the tactic step `split` (part 3 of 3, after `unfold`)
    assert(inv(x)) by(tactic) {
        unfold(inv);
        split();
    }
}
```

```
error: assertion failed
   |
   |     0 < x && x < 10 && x != 5
   |                        ^^^^^^
   |                        |
   |                        assertion failed
   |                        note: from the tactic step `split` (part 3 of 3, after `unfold`)
```

`intro()` works on the unfolded goal too:

```rust
spec fn small(i: int) -> bool {
    i < 100
}

#[verifier::opaque]
spec fn all_small(n: int) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] small(i)
}

proof fn t_unfold_intro(n: int)
    requires
        n <= 100,
{
    assert(all_small(n)) by(tactic) {
        unfold(all_small);
        intro();
    }
}
```

- `all_small(n)` is an opaque function around a `forall`. `unfold(all_small); intro();` proves the
  body of that `forall`; its variable has no name in the script (the steps that follow cannot use
  it).
- `unfold(f); unfold(g); split()` also unfolds the `g` in the result of unfolding `f`.

## Step 7: seeing the goal, `show()`

```rust
proof fn t_show(y: int)
    requires
        y == 2,
{
    assert(inv(y + 1)) by(tactic) {
        have(y > 1);
        unfold(inv);
        show();
        split();
    }
}
```

`show()` checks nothing: it shows the goal at that point and the facts that the script added, as a
note:

```
note: tactic: the goal here is
          0 < x && x < 10 && x != 5
      (`inv` unfolded: in its body, `x` is `y + 1`)
      facts that the script added before this step:
          y > 1
          `inv` unfolded in the goal
      (nothing here has been checked yet, and the facts of the context, such as `requires` and the statements before the assertion, are not listed)
```

- After `unfold`, it shows the text of the body, and what is in place of each parameter (`x` is
  `y + 1`).
- Facts of the context, such as `requires`, are not listed. It prints even when verification
  passes; remove it when you are done.

## Step 8: induction 1, `nat` and `int`

```rust
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

spec fn tri(i: int) -> int
    decreases i,
{
    if i <= 0 {
        0
    } else {
        i + tri(i - 1)
    }
}

proof fn t_induct_nat(n: nat, i: int)
    requires
        i >= 0,
{
    // the rest of the script proves both cases
    assert(pow2(n) >= 1) by(tactic) {
        induct(n);
    }
    // a block for each case
    assert(pow2(n) >= 1) by(tactic) {
        induct(n, { }, { have(pow2(n) == 2 * pow2((n - 1) as nat)); });
    }
    // an `int`, from a start
    assert(tri(i) >= 0) by(tactic) {
        induct(i, from(0));
    }
}
```

- `induct(n)` takes the goal as a function of `n` and proves two cases: the base case `n == 0`, and
  the step `n > 0` with the goal for `n - 1` as a hypothesis. Then vstd's `lemma_induct_nat` gives
  the goal for `n`.
- For different steps in each case, write `induct(n, { base }, { step })`.
- An `int` needs a start: `induct(i, from(lo))`, with `lo <= i`. Without `from` on an `int`, the
  error says to write it.

## Step 9: induction 2, recursive datatypes

```rust
enum List {
    Nil,
    Cons(int, Box<List>),
}

spec fn len(l: List) -> nat
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(_, t) => 1 + len(*t),
    }
}

spec fn total(l: List) -> int
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(h, t) => h + total(*t),
    }
}

spec fn append(a: List, b: List) -> List
    decreases a,
{
    match a {
        List::Nil => b,
        List::Cons(h, t) => List::Cons(h, Box::new(append(*t, b))),
    }
}

proof fn t_induct_list(a: List, b: List) {
    assert(len(append(a, b)) == len(a) + len(b)) by(tactic) {
        induct(a);
    }
    assert(total(append(a, b)) == total(a) + total(b)) by(tactic) {
        induct(a);
    }
}
```

- `induct(a)` makes one case per variant of `List`. The case `Nil` has no hypothesis; the case
  `Cons` has the goal for the tail (field `1`, of type `Box<List>`) as a hypothesis.
- Then rust_verify calls the induction principle that it generates for this function
  (`tactic_induct%t_induct_list%..%List`). It is an ordinary proof function, verified with this
  function, which is why it counts among the verified items.

A goal that needs a hypothesis puts it in the goal with `==>`:

```rust
spec fn allpos(l: List) -> bool
    decreases l,
{
    match l {
        List::Nil => true,
        List::Cons(h, t) => h > 0 && allpos(*t),
    }
}

proof fn t_induct_hyp(l: List)
    requires
        allpos(l),
{
    // a hypothesis about the induction variable goes into the goal
    assert(allpos(l) ==> total(l) >= len(l)) by(tactic) {
        induct(l);
    }
}
```

The function's `requires allpos(l)` does not hold for the *new* `l` of each case (it is another
variable), so `allpos(l) ==>` goes into the goal.

Two recursive fields give two hypotheses:

```rust
enum Tree {
    Leaf,
    Node { left: Box<Tree>, val: int, right: Box<Tree> },
}

spec fn size(t: Tree) -> nat
    decreases t,
{
    match t {
        Tree::Leaf => 1,
        Tree::Node { left, right, .. } => size(*left) + 1 + size(*right),
    }
}

spec fn leaves(t: Tree) -> nat
    decreases t,
{
    match t {
        Tree::Leaf => 1,
        Tree::Node { left, right, .. } => leaves(*left) + leaves(*right),
    }
}

proof fn t_induct_tree(t: Tree) {
    // two hypotheses in the case `Node`: for `left` and for `right`
    assert(size(t) + 1 == 2 * leaves(t)) by(tactic) {
        induct(t);
    }
}
```

It works in the `proof` block of an exec function, and on `Ghost`/`Tracked` parameters:

```rust
fn t_induct_exec(Ghost(l): Ghost<List>, k: u64) -> (r: u64)
    ensures
        r == k,
{
    proof {
        assert(len(l) >= 0) by(tactic) {
            induct(l);
        }
    }
    k
}
```

**Try it.** When a case fails, the error says which variant; the other steps in a case add
`where`:

```rust
enum List {
    Nil,
    Cons(int, Box<List>),
}

spec fn len(l: List) -> nat
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(_, t) => 1 + len(*t),
    }
}

spec fn total(l: List) -> int
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(h, t) => h + total(*t),
    }
}

proof fn e_induct_base(l: List) {
    // not true for `Nil`; FAILS: from the tactic step `induct` (`l` is `List::Nil`)
    assert(len(l) > 0) by(tactic) {
        induct(l);
    }
}

proof fn e_induct_step(l: List) {
    // not true: the elements may be negative; the `have` fails in the case `Cons`
    assert(total(l) >= 0) by(tactic) {
        induct(l);
        have(total(l) >= 0);  // FAILS: from the tactic step `have`, where `l` is `List::Cons`
    }
}
```

```
note: from the tactic step `induct` (`l` is `List::Nil`)
note: from the tactic step `have`, where `l` is `List::Cons`
```

The limits of induction on a datatype (each has an error that says why):
- The type of the variable must be written where it is bound: a parameter, `Ghost(t)`/`Tracked(t)`,
  a `let`/`let ghost` with its type, a closure or `forall` variable with its type. An untyped `let`
  such as `let k = l;` is not enough.
- The datatype and all its fields must be visible in the module (so not vstd's `Seq`).
- No const parameters, and no trait bounds on its type parameters. Only in the body of a function
  (not of a `const` or `static`). For `self`, write `let s: T = self;` and `induct(s)`.
- Fields such as `Option<Box<T>>` or `Seq<T>` get no hypothesis.

## Step 10: an expensive proof on its own, `isolate`

```rust
#[verifier::rlimit(1)]
proof fn t_isolate() {
    // only this proof gets the larger rlimit
    assert(sum(12) == 78) by(tactic) {
        isolate(rlimit = 10);
        unfold(sum, 13);
    }
}

#[verifier::rlimit(1)]
proof fn t_isolate_ensures(n: nat)
    ensures
        #![verifier::tactic(isolate(rlimit = 10))]
        sum(12) == 78,
        n + 0 == n,
{
    reveal_with_fuel(sum, 13);
}
```

- `isolate(rlimit = 10)` makes the rest of the script (the proof of the goal and the assertion at its
  end) a part of the function's query of its own, checked with rlimit 10. The rest of the function
  keeps `#[verifier::rlimit(1)]`.
- `#![verifier::tactic(isolate(rlimit = 10))]` at the start of an `ensures` clause does the same for
  the clause's checks. `#[verifier::tactic(isolate(..))]` on a function makes all its `ensures`
  checks one part.
- `isolate(backend = cvc5)` checks the part with cvc5 (it needs `-V cvc5-smtlib` or `-V cvc5`).
- When a part exceeds its rlimit, the error points at it ("rlimit exceeded in the proof isolated
  here").

`isolate` is the one feature here that adds to what has to be trusted (`smt_check_partitions` in
`air/src/smt_verify.rs`: checking a query in parts gives the same result). The other steps and the
generated lemma are all checked code.

## Step 11: rlimits out of the source, `.verus-hints`

rlimits depend on the machine and the solver, which makes them awkward to fix in the source. A
`.verus-hints` file keeps them out of the source and pins them to the code by a hash. A hint can
only say rlimits and `isolate`, so applied or not, it cannot make a wrong program pass.

1. Next to the crate root (or above it, up to the directory with `Cargo.toml`; with no
   `Cargo.toml`, only next to it), write `.verus-hints` without a hash:

   ```toml
   [[hint]]
   function = "costly"
   rlimit = 10
   ```

2. Run Verus: the hint is not applied, and a warning shows the entry with the hash of the current
   code:

   ```
   warning: `…/.verus-hints`, hint 1: the hint was not applied: it has no `hash` (which pins it to the code it is for)
     = help: if the hint is right for the current code, replace it with:
             [[hint]]
             function = "costly"
             hash = "61bde1fd7a51523c"
             rlimit = 10
   ```

3. Paste it in, and it applies: `note: 1 hint from `…/.verus-hints` applied`.

4. When the function changes, the hash no longer matches: the hint is not applied, and a warning
   shows the new hash. In CI, pass `-V hints-locked` to make this an error:

   ```
   error: `…/.verus-hints`, hint 1: the hint was not applied: `costly` has changed since it was written
     = help: if the hint is right for the current code, replace it with:
             hash = "18614df41599a299"
   error: 1 hint of `…/.verus-hints` did not apply to the code (`-V hints-locked`)
   ```

For one `ensures` clause, write `ensures = 2` (the second clause) and `isolate = { rlimit = 10 }`. The
file can also be given with `-V hints=<path>`.

## Step 12: where is it stuck? `-V triage`

When a function fails or exceeds its rlimit, `-V triage` checks its proof obligations again, one at
a time (with the others disabled), and says which one is stuck:

```
note: triage of the function body check: 3 proof obligations, each checked alone with the others disabled: 2 proved, 1 not proved, 0 exceeded the rlimit
error: postcondition not satisfied
note: triage (2/3): postcondition not satisfied: not proved alone: the solver answered `unknown` (incomplete quantifiers), as it does for most obligations that it does not prove, whether or not they hold
```

- "exceeded the rlimit alone": that obligation is expensive by itself; give it its own rlimit (steps
  10 and 11).
- "not proved alone": facts are missing; help with `have`, `apply`, `unfold` or `induct`.
- It is a diagnostic: verification results do not change.

## Appendix A: the steps at a glance

| Step | When | In one line |
|---|---|---|
| `split()` / `split({..}, {..})` | `A && B`, `A <==> B`, `if` | split into parts |
| `intro()` | `forall`, `==>` | introduce the variables or the condition |
| `cases(b)` / `cases(b, {..}, {..})` | any goal | cases on a `bool` |
| `cases(e)` | any goal | one case per enum variant |
| `cases(match e { .. })` | any goal | cases with named fields |
| `induct(n)`, `induct(i, from(lo))`, `induct(t)` | any goal | induction on a `nat`, an `int`, a datatype |
| `unfold(f)`, `unfold(f, k)` | any goal | reveal (and unfold the goal before `split`/`intro`) |
| `apply(L(a))` | any goal | call a lemma |
| `have(Q)` | any goal | an intermediate fact |
| `inst(forall\|x\| Q, t)` | any goal | a `forall` fact at `t` |
| `smt()`, `smt(nonlinear_arith, ..)`, `smt(bit_vector, ..)`, `compute()` | any goal | close the goal |
| `show()` | any goal | show the goal and the facts |
| `isolate(rlimit = N, backend = ..)` | any goal | check the rest on its own |

## Appendix B: common errors

| Error | Meaning and what to do |
|---|---|
| `note: from the tactic step `X` (..)` | an assertion that step made failed; the parenthesis says which part or case |
| "`split`: the goal `..` is not a conjunction (`&&`, `&&&`), an `<==>` or an `if`" | the goal has the wrong shape; for a call, put `unfold(f)` first, and look at the goal with `show()` |
| "write the type of `k` where `k` is bound" | write the type of the variable of an induction on a datatype (`let k: List = ..`) |
| "`induct(i)`: `i` is an `int`; write `induct(i, from(lo))`" | an `int` needs a start |
| "the field `..` of `..` is not visible here" | that datatype cannot be inducted on in this module |
| "rlimit exceeded in the proof isolated here" | raise the rlimit of the isolated part |
| "the hint was not applied: `f` has changed since it was written" | the code changed; check the new hash in the warning and paste it in |
| "`assume`, `admit` and `inline_air_stmt` are not allowed in a `by(tactic)` script" | a script cannot add assumptions |

## Appendix C: what is trusted

- Steps, unfolded goals, the cases of an induction and the generated induction principles are all
  checked as ordinary proof code, and the goal is asserted again at the end of the script: they are
  not trusted.
- The generated principle belongs to the function's module and is verified with the function; under
  `--verify-function` it is selected with the function.
- The one addition to what is trusted is `smt_check_partitions`, for `isolate`. A part with
  `isolate(backend = cvc5)` is proved by cvc5 alone, even in a Z3 run, so for that part cvc5 is
  trusted (as in a `-V cvc5` run).
- `.verus-hints` and `-V triage` change only how the query is checked (rlimits, parts) and the
  diagnostics.
