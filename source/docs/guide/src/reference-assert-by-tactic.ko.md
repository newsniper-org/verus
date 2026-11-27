# assert ... by(tactic) (fork)

> **fork 확장, 실험적 기능.** `by(tactic)`과 `-V triage`는 이 Verus fork에만 있습니다.
> 이 문서의 영어판은 [여기](./reference-assert-by-tactic.md)에 있습니다.

SMT solver가 증명을 찾지 못하면, 어떻게 나아갈지 한 단계씩 직접 지시할 수 있습니다. 대화형 정리
증명기가 tactic을 받는 방식과 같습니다.

```rust
assert(forall|i: int| 0 <= i < n ==> #[trigger] f(i) > i) by(tactic) {
    intro();
    apply(lemma_f(i));
}
```

각 step은 `verus!`의 나머지 처리보다 먼저 평범한 증명 코드로 펼쳐집니다. 펼친 결과는 `assert`,
`assert ... by`, `assert forall ... implies ... by`, `if`, `match`, `reveal_with_fuel`, lemma 호출입니다.
이 코드는 다른 증명과 똑같이 검사되고, 블록의 끝에서는 여전히 goal을 assert합니다.

**step은 goal을 "어떻게" 증명할지만 바꾸고, "무엇을" 증명할지는 바꾸지 않습니다.** 잘못된 step은
증명을 실패하게 할 뿐, 거짓인 assertion을 통과시키지 못합니다. 따라서 펼치는 과정은 신뢰해야 할 대상이
아닙니다. 다만 `isolate(..)`는 작은 검사 하나를 신뢰 대상에 더합니다(아래 `isolate` 절).

### 구문

```verus-grammar
V@[assert_by_tactic_stmt] ::=
    assert ( V@[spec_expr] ) by ( tactic ) { V@[tactic_item]* }

V@[tactic_item] ::= V@[tactic_step] ; | V@[stmt]
```

script에는 step과 평범한 증명 문장을 섞어 쓸 수 있습니다. 평범한 문장은 그대로 지나갑니다.

step은 script의 맨 위 수준에서, 아래 이름을 경로 없이 호출한 것입니다. 같은 이름의 함수는 경로를
붙여 부를 수 있습니다(`self::split(x)`).

### step

step은 현재 goal(아래 표의 `G`)에 작용합니다. 처음 goal은 assert하는 식입니다.

| step | goal | 펼친 결과 |
|---|---|---|
| `have(Q)` | 무엇이든 | `assert(Q);`. 이후 script에서 `Q`는 사실로 쓰입니다 |
| `split()` | `A && B`, `{ &&& A &&& B }` | `assert(A) by { .. }; assert(B) by { .. };` |
| | `A <==> B` | `assert(A ==> B) by { .. }; assert(B ==> A) by { .. };` |
| | `if c { A } else { B }` | `if c { assert(A) by { .. } } else { assert(B) by { .. } }` |
| `intro()` | `forall\|x\| A ==> B` | `assert forall\|x\| A implies B by { .. }` |
| | `forall\|x\| B` | `assert forall\|x\| B by { .. }` |
| | `A ==> B` | `if A { assert(B) by { .. } }` |
| `cases(b)` | 무엇이든 | `if b { assert(G) by { .. } } else { assert(G) by { .. } }` |
| `cases(match e { P => { .. }, .. })` | 무엇이든 | 그 `match`. 모든 갈래에서 `G`를 assert합니다 |
| `unfold(f)`, `unfold(f, k)` | 무엇이든 | `reveal(f);`, `reveal_with_fuel(f, k);` |
| `apply(L(a))` | 무엇이든 | `L(a);` (그 `ensures`가 사실이 됩니다) |
| `inst(forall\|x: T\| Q, t)` | 무엇이든 | `assert(forall\|x: T\| Q); assert({ let x: T = t; Q });` |
| `smt()` | 무엇이든 | `assert(G);` |
| `smt(nonlinear_arith, R, ..)`, `smt(bit_vector, R, ..)` | 무엇이든 | `assert(G) by(nonlinear_arith) requires R, ..;` (또는 `bit_vector`) |
| `compute()` | 무엇이든 | `assert(G) by(compute);` |
| `show()` | 무엇이든 | 없음. goal과 script가 더한 사실을 note로 보여 줍니다 |
| `isolate()`, `isolate(rlimit = N)` | 무엇이든 | `assert(G) by { .. }`. 질의의 독립된 한 부분으로 검사됩니다(아래 `isolate` 절) |

펼친 결과의 `..` 자리에는 script의 나머지가 들어갑니다.
- **나머지 step:** `split()`이나 `cases(b)` 뒤의 step은 각 부분에 적용됩니다. `intro()` 뒤의 step은
  새 goal(`B`)을 증명하고, 이때 `x`를 쓸 수 있습니다.
- **부분마다 따로 주는 step:** `split({ .. }, { .. })`와 `cases(b, { .. }, { .. })`는 부분마다 step
  블록을 하나씩 받습니다. `cases(match ..)`는 각 갈래의 블록을 받습니다. 이때 script의 나머지는
  그 블록들 안에 씁니다. 이런 형태 뒤에는 아무것도 올 수 없습니다.
- **goal을 닫는 step:** `smt(..)`와 `compute()`는 goal을 증명합니다. 그 뒤에는 step도 평범한 문장도
  올 수 없습니다.
- **script가 끝날 때:** goal을 닫지 않고 script가 끝나면, solver가 script가 세운 사실로 goal을
  증명합니다.

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

`have`, `inst`, `split`, `cases`, `smt()`, `==>`에 쓴 `intro`가 만든 assertion이 실패하면, 오류가 그
assertion을 만든 step을 알려 줍니다. `forall`에 쓴 `intro`, `smt(<prover>, ..)`, `compute()`는 step
이름 없이 goal을 가리킵니다.

```
error: assertion failed
   |
   |     assert(x > 0 && y > 0) by(tactic) { split(); }
   |                     ^^^^^
   |                     assertion failed
   |                     note: from the tactic step `split` (part 2 of 2)
```

goal은 step이 놓은 자리에서 assert되므로, 이름은 그 자리에서의 뜻을 가집니다. script 안의 `let`이
goal이 쓰는 이름을 다시 쓰면, 그 뒤 step들이 assert하는 내용이 달라집니다. 끝에서는 goal을 쓰인
그대로 검사합니다. `cases(match ..)`의 패턴이 goal이 쓰는 이름을 묶으면 오류입니다. `split()`은
`if let` goal을 받지 않으니 `cases(match ..)`를 쓰세요.

### script에서 할 수 없는 것

- **새 가정 금지:** script 안 어디에서든 `assume`, `admit`, `inline_air_stmt`는 오류입니다. 중첩된
  블록, closure, step이 만든 블록, 매크로가 펼쳐 넣은 코드도 마찬가지입니다.
- **함수와 상수 선언 금지:** 그 본문은 script 밖에서 따로 검사되기 때문입니다.

lemma 호출은 다른 곳에서와 같습니다. `external_body` lemma는 어디서 부르든 신뢰됩니다.

### `show()`

`show()`는 그 step에서의 goal과, 그 전에 script가 더한 사실을 보여 줍니다. 더한 사실은 `have`,
case의 조건, `intro`가 들여온 것입니다.

매크로를 펼치는 시점에 소스 텍스트를 보고 만듭니다. 그래서 다음 두 가지에 주의해야 합니다.
- `requires`나 assertion 앞의 문장처럼 문맥에서 오는 사실은 나오지 않습니다.
- 보여 주는 내용은 아직 아무것도 검사되지 않은 것입니다.
- 나중에 증명이 실패해도, 검증이 통과해도 출력됩니다.

### 증명을 따로 검사하기: `isolate`

`isolate()`는 script의 나머지를 함수 질의의 독립된 한 부분으로 만듭니다. 나머지란 현재 goal의 증명과,
그 끝에서 goal을 assert하는 것입니다.

`isolate(rlimit = N)`을 쓰면 그 부분은 자기 rlimit을 받습니다. 단위는 `#[verifier::rlimit(N)]`과
같고, 제한을 두지 않으려면 `infinity`를 씁니다. 함수의 나머지는 함수의 rlimit으로 검사됩니다.

```rust
#[verifier::rlimit(1)]
proof fn p() {
    assert(sum(12) == 78) by(tactic) { isolate(rlimit = 10); unfold(sum, 13); }
    // .. 나머지 증명은 rlimit 1로 검사됩니다
}
```

질의는 부분마다 한 번씩 검사되고, 이때 다른 부분의 assertion은 끕니다. 모든 부분이 통과해야만 검증된
것으로 칩니다.

각 부분의 assertion은 같은 질의의 assertion이고, 그 앞의 사실도 같습니다. 다른 부분의 assertion을
끄면 그 부분이 검사하는 것만 빠지고, 그 부분이 가정하는 것은 빠지지 않습니다.

이 검사는 `by(tactic)`이 신뢰 대상에 더하는 유일한 것이며, 다음 두 가지에 기댑니다.
- 모든 assertion은 정확히 한 부분에 속합니다.
- 질의가 valid인 것은 각 부분이 valid인 것과 같습니다.

두 번째가 왜 성립하는지는 `air/src/smt_verify.rs`의 `smt_check_partitions`에 적혀 있습니다.

- **여러 부분:** `isolate`는 여러 번 쓸 수 있습니다. `split`의 각 부분 안에서도, isolate된 증명 안에서도
  쓸 수 있습니다. 각 assertion은 가장 안쪽 isolate에 속합니다.
- **루프 본문 안:** 그 부분은 루프 본문의 질의에 속합니다. `#[verifier::nonlinear]` 함수의 본문에서도
  됩니다.
- **순서:** isolate된 증명을 먼저 검사하고, 함수의 나머지는 소스에서의 위치와 상관없이 맨 마지막에
  검사합니다.
- **한 부분이 실패할 때:** 그 뒤의 부분은 검사되지 않고, 그렇다는 note가 나옵니다. 그래서 함수의 나머지에
  있는 오류는, isolate된 증명보다 앞에 있더라도, isolate된 증명이 모두 통과해야 보고됩니다.
- **한 부분이 rlimit을 넘을 때:** 오류가 isolate된 goal을 가리킵니다.
- **cvc5:** 부분의 rlimit을 따로 정할 수 없습니다(`#[verifier::rlimit]`도 마찬가지입니다). 경고와 함께
  전역 `--rlimit`이 적용됩니다.
- **부분으로 나누지 않는 질의:** 보고만 하는 질의는 통째로 검사됩니다. recommends, `--expand-errors`,
  `--profile`의 재실행, `-V triage`가 여기에 해당합니다. `by(nonlinear_arith)`나 `by(bit_vector)`
  assertion은 이미 그 자체로 하나의 질의이므로, 나눌 부분이 없습니다.

## solver가 막힌 obligation 찾기: `-V triage`

`-V triage`를 주면, 함수가 검증에 실패하거나 rlimit을 넘을 때 Verus가 그 함수의 proof obligation을
하나씩 다시 검사합니다. 이때 나머지 obligation은 끕니다. 그리고 혼자서도 증명되지 않는 것을
알려 줍니다.

```
note: triage of the function body check: 15 proof obligations, each checked alone with the
      others disabled: 14 proved, 0 not proved, 1 exceeded the rlimit
note: triage (7/15): postcondition not satisfied: exceeded the rlimit alone
```

답은 다음과 같이 나뉩니다.
- **"exceeded the rlimit alone":** 그 obligation 하나만으로도 너무 비쌉니다.
- **"the solver found a counterexample":** 그 obligation이 질의의 사실들에서 나오지 않습니다. Verus가
  돌리는 방식의 Z3에서는 드뭅니다. 대신 `unknown`으로 답하기 때문입니다.
- **"the solver gave up on nonlinear arithmetic":** `by(nonlinear_arith)`를 쓰라는 안내가 함께
  나옵니다.
- **`unknown (incomplete quantifiers)`:** Verus가 증명하지 못한 obligation에 보통 주는 답입니다.
  obligation이 참이든 거짓이든 이렇게 나옵니다.

질의가 rlimit을 넘으면, 혼자서는 증명되지만 rlimit의 10분의 1 이상을 쓰는 obligation도 셋까지
보여 줍니다. 이것은 Z3에서만 됩니다. cvc5는 검사가 쓴 자원을 알려 주지 않습니다. 모든 obligation이
혼자서 증명되면, 모두 합쳤을 때만 rlimit을 넘는다고 요약에 적습니다.

이 기능은 진단용일 뿐입니다.
- 검증 결과는 바뀌지 않습니다.
- 검사는 별도 solver 프로세스에서 돌기 때문에, 다른 질의에 영향을 주지 않습니다.
- Z3와 cvc5에서만 동작합니다.
- `by(bit_vector)` 질의, recommends 검사, `--expand-errors`의 재실행은 triage하지 않습니다.
