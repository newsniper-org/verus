# 따라 하기: tactic script, 귀납, `isolate`, `.verus-hints`, `-V triage` (fork)

> **fork 확장.** 이 문서는 이 fork에 새로 생긴 증명 도구를 직접 따라 하며 익히는 안내서입니다. 각 기능의
> 규칙을 모두 적은 문서는 [assert ... by(tactic)](./reference-assert-by-tactic.ko.md)입니다. 영어판은
> [여기](./tutorial-tactics.md)에 있습니다.

## 시작하기 전에

이 문서의 코드는 저장소의 두 파일에 그대로 있습니다. 둘 다 시험(`rust_verify_test`의 `examples`)에서
검증되므로 문서의 코드가 실제와 어긋나지 않습니다.

- `examples/guide/tactics_tutorial.rs`: 모두 검증되는 예
- `examples/guide/tactics_tutorial_errors.rs`: 일부러 실패하는 예(오류가 어떻게 보이는지 보는 용도)

빌드한 저장소에서 다음처럼 돌립니다.

```
cd source
source ../tools/activate
./target-verus/release/verus ../examples/guide/tactics_tutorial.rs --crate-type lib
#   verification results:: 32 verified, 0 errors
./target-verus/release/verus ../examples/guide/tactics_tutorial_errors.rs --crate-type lib
#   verification results:: 4 verified, 4 errors
```

따라 할 때는 파일을 하나 복사해 두고, 각 단계의 "해 보기"대로 고쳐 가며 돌려 보세요.

**기억할 한 가지:** `assert(P) by(tactic) { .. }`의 step은 `P`를 *어떻게* 증명할지만 정하고, *무엇을*
증명할지는 바꾸지 못합니다. step은 평범한 증명 코드(`assert`, `assert .. by`, `if`, `match`, lemma 호출,
`reveal`)가 되어 검사되고, script가 끝나면 `P`를 쓰인 그대로 다시 assert합니다. 그래서 step을 잘못 써도
증명이 실패할 뿐, 거짓이 통과하지는 않습니다. script 안에서는 `assume`과 `admit`을 쓸 수 없습니다.

## 1단계: 첫 script — `split()`

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

- `split()`은 goal `x > 0 && y > 0`을 두 부분으로 나눠 각각 assert합니다.
- script가 끝나면 `x > 0 && y > 0`을 한 번 더 assert합니다.

**해 보기.** `requires`에서 `y > 0`을 지워 보세요. 오류가 두 번째 부분을 가리키고, 어느 step이 만든
assertion인지 note가 알려 줍니다.

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

`split()`은 `A && B` 말고도 `A <==> B`(두 방향으로), `if c { A } else { B }`(두 갈래로),
`{ &&& A &&& B }`를 나눕니다.

## 2단계: 사실 더하기 — `apply`, `have`, 부분마다 블록

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

- `apply(lemma_f(x))`는 lemma를 부릅니다. 그 `ensures`(`f(x) > x`)가 이후의 사실이 됩니다.
- `have(Q)`는 `Q`를 assert하고, 이후의 사실로 씁니다. solver에게 중간 단계를 알려 줄 때 씁니다.
- `split({ .. }, { .. })`는 부분마다 따로 step 블록을 줍니다. 첫 블록은 `f(x) > x`를, 둘째 블록은
  `f(y) > y`를 증명합니다. 블록을 받는 형태 뒤에는 아무 step도 올 수 없습니다.
- 블록 없는 `split()` 뒤의 step은 *각 부분마다* 실행됩니다.

**해 보기.** 두 번째 assertion에서 `apply(lemma_f(f(x)));`를 지워 보세요. `have`가 실패하고, note가
`from the tactic step `have``라고 알려 줍니다.

## 3단계: `forall`과 `==>` — `intro()`

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

- `forall|i| A ==> B`에 `intro()`를 쓰면 `assert forall|i| A implies B by { .. }`가 됩니다. 이후 step에서
  `i`를 그 이름 그대로 쓸 수 있습니다.
- `A ==> B`에 쓰면 `if A { assert(B) by { .. } }`가 됩니다.

## 4단계: `forall` 사실을 특정 값으로 꺼내기 — `inst`

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

- `inst(fact, t)`는 먼저 `fact`를 assert하고, 그다음 변수 자리에 `t`를 넣은 식을 assert합니다.
- trigger가 맞지 않아 solver가 스스로 꺼내지 못할 때 씁니다. 변수가 여럿이면 항을 그만큼
  줍니다(`inst(forall|x, y| Q, a, b)`).

## 5단계: 경우 나누기 — `cases`

`bool` 조건으로 나누기:

```rust
proof fn t_cases_bool(x: int) {
    assert(x * x >= 0) by(tactic) {
        cases(x >= 0, { smt(nonlinear_arith, x >= 0); }, { smt(nonlinear_arith, x < 0); });
    }
}
```

- `cases(b, { .. }, { .. })`는 `b`가 참인 경우와 거짓인 경우에 각자 블록을 줍니다.
- `smt(nonlinear_arith, R, ..)`는 goal을 `assert(G) by(nonlinear_arith) requires R, ..;`로 증명합니다. goal을
  닫는 step이라 뒤에 아무것도 올 수 없습니다(`smt()`, `compute()`도 마찬가지).

enum 값으로 나누기:

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

- `cases(s)`는 `s`의 타입에서 variant를 가져와, variant마다 경우를 하나씩 만듭니다. 실패하면 어느
  variant였는지 오류가 알려 줍니다(`` (`s` is `Shape::Line`) ``).
- 필드에 이름을 붙이려면 `cases(match ..)`를 쓰고, 갈래마다 블록을 줍니다. 모든 갈래에서 goal을
  assert합니다.

## 6단계: 함수 펼치기 — `unfold`

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

- `unfold(sum, 4)`는 `reveal_with_fuel(sum, 4)`입니다. 재귀 함수를 그만큼 펼칠 수 있게 됩니다.
- `inv`는 opaque라 그 본문을 solver가 모릅니다. `unfold(inv)` 뒤에 `split()`이 오면, `unfold`는 goal 안의
  `inv(x)`를 본문 `0 < x && x < 10 && x != 5`로 바꿉니다(한 단계만). 그래서 `split()`이 그 세 부분을
  나눌 수 있습니다.

**해 보기.** `x == 5`이면 셋째 부분이 실패합니다. 오류는 `inv` 본문의 `x != 5`를 가리킵니다.

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

펼친 goal에 `intro()`도 쓸 수 있습니다:

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

- `all_small(n)`은 `forall`을 감싼 opaque 함수입니다. `unfold(all_small); intro();`는 그 `forall`의 본문을
  증명합니다. 이때 `forall`의 변수는 script에서 이름이 없습니다(그래서 이후 step에서 쓸 수 없습니다).
- `unfold(f); unfold(g); split()`처럼 이어 쓰면 `f`를 펼친 결과 안의 `g`도 펼칩니다.

## 7단계: 지금 goal 보기 — `show()`

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

`show()`는 아무것도 검사하지 않고, 그 자리의 goal과 script가 더한 사실을 note로 보여 줍니다.

```
note: tactic: the goal here is
          0 < x && x < 10 && x != 5
      (`inv` unfolded: in its body, `x` is `y + 1`)
      facts that the script added before this step:
          y > 1
          `inv` unfolded in the goal
      (nothing here has been checked yet, and the facts of the context, such as `requires` and the statements before the assertion, are not listed)
```

- 펼친 뒤에는 본문의 텍스트와, 매개변수 자리에 무엇이 들어갔는지(`x`는 `y + 1`)를 보여 줍니다.
- `requires`처럼 문맥에서 오는 사실은 나오지 않습니다. 검증이 통과해도 출력됩니다. 다 쓴 뒤에는 지우세요.

## 8단계: 귀납 1 — `nat`과 `int`

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

- `induct(n)`은 goal을 `n`의 함수로 보고 두 경우를 증명합니다. 기저 경우는 `n == 0`이고, 단계는
  `n > 0`이며 `n - 1`에 대한 goal을 가정으로 받습니다. 그다음 vstd의 `lemma_induct_nat`가 `n`에 대한 goal을
  줍니다.
- 경우마다 다른 step을 주려면 `induct(n, { 기저 }, { 단계 })`를 씁니다.
- `int`는 시작점이 필요합니다: `induct(i, from(lo))`. `lo <= i`이어야 합니다. `from` 없이 `int`에 쓰면
  그렇게 쓰라는 오류가 납니다.

## 9단계: 귀납 2 — 재귀 datatype

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

- `induct(a)`는 `List`의 variant마다 경우를 하나씩 만듭니다.
  - `Nil` 경우: 가정 없음
  - `Cons` 경우: 꼬리(필드 `1`, 타입 `Box<List>`)에 대한 goal을 가정으로 받음
- 그다음 rust_verify가 이 함수를 위해 만든 귀납 원리 보조정리(`tactic_induct%t_induct_list%..%List`)를
  부릅니다. 이 보조정리는 평범한 proof 함수이고, 이 함수와 함께 검증됩니다. 검증 개수에 들어가는 것은
  그래서입니다.

가정이 필요한 goal은 `==>`로 goal에 넣습니다:

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

함수의 `requires allpos(l)`은 각 경우의 *새* `l`에 대해서는 성립하지 않습니다(경우의 `l`은 다른
변수입니다). 그래서 `allpos(l) ==>`를 goal에 넣습니다.

재귀 필드가 둘이면 가정도 둘입니다:

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

exec 함수의 `proof` 블록에서도, `Ghost`/`Tracked` 매개변수에도 됩니다:

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

**해 보기.** 실패하면 오류가 어느 variant의 경우인지 알려 줍니다. 경우 안의 다른 step에는 `where`가
붙습니다.

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

datatype 귀납의 제한(각각 오류 메시지가 이유를 알려 줍니다):
- 변수가 묶이는 곳에 타입이 쓰여 있어야 합니다. 매개변수, `Ghost(t)`/`Tracked(t)`, 타입을 쓴 `let`/`let ghost`,
  타입을 쓴 closure·`forall` 변수는 됩니다. `let k = l;`처럼 타입 없는 `let`은 안 됩니다.
- datatype과 그 모든 필드가 그 모듈에서 보여야 합니다(그래서 vstd의 `Seq`는 안 됩니다).
- const 매개변수가 없고, 타입 매개변수에 trait bound가 없어야 합니다. 함수 본문에서만 됩니다(`const`·
  `static` 본문은 안 됨). `induct(self)`는 `let s: T = self;`로 묶은 뒤 `induct(s)`로 씁니다.
- `Option<Box<T>>`나 `Seq<T>` 같은 필드에는 가정이 생기지 않습니다.

## 10단계: 비싼 증명만 따로 — `isolate`

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

- `isolate(rlimit = 10)`은 script의 나머지(그 goal의 증명과 끝의 assert)를 함수 질의의 독립된 부분으로
  떼어, 그 부분만 rlimit 10으로 검사합니다. 함수의 나머지는 `#[verifier::rlimit(1)]` 그대로입니다.
- `ensures` 절 맨 앞의 `#![verifier::tactic(isolate(rlimit = 10))]`는 그 절의 검사를 같은 방식으로 뗍니다.
  함수에 `#[verifier::tactic(isolate(..))]`를 붙이면 모든 `ensures` 검사가 한 부분이 됩니다.
- `isolate(backend = cvc5)`는 그 부분을 cvc5로 검사합니다(`-V cvc5-smtlib`이나 `-V cvc5`가 필요합니다).
- 부분 하나가 rlimit을 넘으면 오류가 그 부분을 가리킵니다("rlimit exceeded in the proof isolated here").

`isolate`는 이 기능들 가운데 신뢰 대상을 하나 더하는 유일한 것입니다(`air/src/smt_verify.rs`의
`smt_check_partitions`: 질의를 부분으로 나눠 검사해도 결과가 같다는 것). 다른 step과 생성되는 보조정리는
모두 검사되는 코드입니다.

## 11단계: rlimit을 소스 밖에 — `.verus-hints`

rlimit은 기계와 solver에 따라 달라서 소스에 박아 두기 곤란할 때가 있습니다. `.verus-hints`는 그것을
소스 밖에 두고 hash로 코드에 묶습니다. hint는 rlimit과 `isolate`만 말할 수 있으므로, 적용되든 안 되든
틀린 프로그램을 통과시킬 수 없습니다.

1. crate root 옆(또는 그 위, `Cargo.toml`이 있는 디렉터리까지. `Cargo.toml`이 없으면 crate root 옆만)에
   `.verus-hints`를 만들고 hash 없이 씁니다.

   ```toml
   [[hint]]
   function = "costly"
   rlimit = 10
   ```

2. 돌리면 적용하지 않고, 지금 코드의 hash가 든 항목을 경고로 보여 줍니다.

   ```
   warning: `…/.verus-hints`, hint 1: the hint was not applied: it has no `hash` (which pins it to the code it is for)
     = help: if the hint is right for the current code, replace it with:
             [[hint]]
             function = "costly"
             hash = "61bde1fd7a51523c"
             rlimit = 10
   ```

3. 그대로 붙여 넣으면 적용됩니다: `note: 1 hint from `…/.verus-hints` applied`.

4. 함수를 고치면 hash가 맞지 않아 hint가 적용되지 않고, 경고가 새 hash를 보여 줍니다. CI에서는
   `-V hints-locked`를 주면 이것이 오류가 됩니다.

   ```
   error: `…/.verus-hints`, hint 1: the hint was not applied: `costly` has changed since it was written
     = help: if the hint is right for the current code, replace it with:
             hash = "18614df41599a299"
   error: 1 hint of `…/.verus-hints` did not apply to the code (`-V hints-locked`)
   ```

`ensures` 절 하나를 떼려면 `ensures = 2`(두 번째 절)와 `isolate = { rlimit = 10 }`을 씁니다. 파일 위치는
`-V hints=<path>`로 정할 수도 있습니다.

## 12단계: 어디서 막혔나 — `-V triage`

함수가 실패하거나 rlimit을 넘으면, `-V triage`는 그 함수의 proof obligation을 하나씩(나머지는 끄고) 다시
검사해서 어느 것이 막혔는지 알려 줍니다.

```
note: triage of the function body check: 3 proof obligations, each checked alone with the others disabled: 2 proved, 1 not proved, 0 exceeded the rlimit
error: postcondition not satisfied
note: triage (2/3): postcondition not satisfied: not proved alone: the solver answered `unknown` (incomplete quantifiers), as it does for most obligations that it does not prove, whether or not they hold
```

- "exceeded the rlimit alone"이면 그 obligation 자체가 비쌉니다. 10단계·11단계로 따로 큰 rlimit을 주세요.
- "not proved alone"이면 사실이 모자랍니다. `have`, `apply`, `unfold`, `induct`로 도와주세요.
- 진단용이라 검증 결과는 바뀌지 않습니다.

## 부록 A: step 한눈에

| step | 언제 | 한 줄 설명 |
|---|---|---|
| `split()` / `split({..}, {..})` | `A && B`, `A <==> B`, `if` | 부분으로 나눔 |
| `intro()` | `forall`, `==>` | 변수·조건을 들여옴 |
| `cases(b)` / `cases(b, {..}, {..})` | 아무 goal | `bool`로 나눔 |
| `cases(e)` | 아무 goal | enum variant마다 나눔 |
| `cases(match e { .. })` | 아무 goal | 필드에 이름을 붙여 나눔 |
| `induct(n)`, `induct(i, from(lo))`, `induct(t)` | 아무 goal | `nat`·`int`·datatype 귀납 |
| `unfold(f)`, `unfold(f, k)` | 아무 goal | reveal (뒤에 `split`/`intro`면 goal도 펼침) |
| `apply(L(a))` | 아무 goal | lemma 호출 |
| `have(Q)` | 아무 goal | 중간 사실 |
| `inst(forall\|x\| Q, t)` | 아무 goal | `forall` 사실을 `t`로 꺼냄 |
| `smt()`, `smt(nonlinear_arith, ..)`, `smt(bit_vector, ..)`, `compute()` | 아무 goal | goal을 닫음 |
| `show()` | 아무 goal | goal과 사실을 보여 줌 |
| `isolate(rlimit = N, backend = ..)` | 아무 goal | 나머지를 따로 검사 |

## 부록 B: 자주 보는 오류

| 오류 | 뜻과 대처 |
|---|---|
| `note: from the tactic step `X` (..)` | 그 step이 만든 assertion이 실패했습니다. 괄호 안이 어느 부분·경우인지입니다 |
| "`split`: the goal `..` is not a conjunction (`&&`, `&&&`), an `<==>` or an `if`" | goal 모양이 맞지 않습니다. 함수 호출이면 `unfold(f)`를 앞에 두고, `show()`로 goal을 보세요 |
| "write the type of `k` where `k` is bound" | datatype 귀납의 변수에 타입을 써 주세요(`let k: List = ..`) |
| "`induct(i)`: `i` is an `int`; write `induct(i, from(lo))`" | `int`에는 시작점이 필요합니다 |
| "the field `..` of `..` is not visible here" | 그 datatype은 이 모듈에서 귀납할 수 없습니다 |
| "rlimit exceeded in the proof isolated here" | 떼어 낸 부분의 rlimit을 늘리세요 |
| "the hint was not applied: `f` has changed since it was written" | 코드가 바뀌었습니다. 경고의 새 hash를 확인하고 붙여 넣으세요 |
| "`assume`, `admit` and `inline_air_stmt` are not allowed in a `by(tactic)` script" | script 안에서는 새 가정을 쓸 수 없습니다 |

## 부록 C: 무엇을 신뢰하나

- step, 펼친 goal, 귀납의 경우, 생성되는 귀납 보조정리는 모두 평범한 증명 코드로 검사됩니다. script 끝에서
  goal도 다시 assert됩니다. 그래서 신뢰 대상이 아닙니다.
- 귀납 보조정리는 그 함수와 같은 모듈에 속해 함께 검증되고, `--verify-function`에서도 그 함수와 함께
  골라집니다.
- 더해진 신뢰 대상은 `isolate`의 `smt_check_partitions` 하나입니다. 다만 `isolate(backend = cvc5)`인 부분은
  Z3로 실행해도 cvc5만 증명하므로, 그 부분에서는 cvc5를 신뢰하게 됩니다(`-V cvc5`로 실행할 때처럼).
- `.verus-hints`와 `-V triage`는 검사 방법(rlimit, 나누기)과 진단만 바꿉니다.
