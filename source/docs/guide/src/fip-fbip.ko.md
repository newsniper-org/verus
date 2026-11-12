# 완전 제자리 함수 (FIP와 FBIP)

> **fork 확장, 실험적 기능.** 이 페이지의 내용은 이 Verus fork에만 있으며 `-V alloc-check`가 필요합니다. 기능을
> 안내하는 페이지이고, 정확한 규칙은 [할당 상한 (`allocates`)](./reference-allocates.ko.md)에 있습니다. 영어판은
> [여기](./fip-fbip.md)에 있습니다.

## 개념

함수형 프로그램은 옛 값을 고치지 않고 새 값을 만듭니다. 그래서 보통 새 칸마다 할당이, 버려지는 칸마다 해제가
일어납니다. FP² 논문(Lorenzen, Leijen, Swierstra, "FP²: Fully in-Place Functional Programming", ICFP 2023)은
둘 다 필요 없는 함수들을 가려냅니다. 이런 함수는 소비하는 칸을 새로 만드는 칸으로 다시 씁니다. 논문은 두 부류를
정의합니다.

| FP² 부류 | 할당 | 해제 | 스택 |
|---|---|---|---|
| `fip` | 없음 | 없음 | 상수 |
| `fip(n)` | 최대 `n` | 없음 | 상수 |
| `fbip` | 없음 | 제한 없음 | 제한 없음 |
| `fbip(n)` | 최대 `n` | 제한 없음 | 제한 없음 |

`fip` 함수는 정해진 양의 메모리만으로 돌아갑니다. 그래서 할당을 쓸 수 없거나 할당이 실패하면 안 되는 곳(인터럽트
처리기, 할당기 안, 운영체제가 없는 환경)에서도 쓸 수 있습니다. `fbip`("functional but in place")는 더 약합니다.
메모리를 해제해도 되고, 입력 크기에 비례하는 스택을 써도 됩니다.

## fork에서 검사하는 방법

Rust는 꼬리 위치의 호출이 호출자의 스택 프레임을 다시 쓴다고 보장하지 않습니다. 그래서 fork는 FP²의 `fip`를 둘로
나눕니다.

| 쓰는 것 | 할당 | 해제 | 스택 | FP² 부류 |
|---|---|---|---|---|
| `allocates n` | 최대 `n` | 제한 없음 | 제한 없음 | `fbip(n)` |
| `#[verifier::fip]` | 없음 (`allocates n`과 함께면 최대 `n`) | 정상 반환 경로에서 없음 | 제한 없음 | 스택 조건을 뺀 `fip(n)` |
| `#[verifier::fip(strict)]` | 없음 (`allocates n`과 함께면 최대 `n`) | 정상 반환 경로에서 없음 | 상수 | `fip` / `fip(n)` |

셋 다 Verus를 `-V alloc-check`로 실행할 때 검사합니다.

* `allocates n`은 `ensures`처럼 SMT 솔버가 증명합니다. 각 호출에는 호출되는 함수의 상한만큼을 셉니다.
* `#[verifier::fip]`은 검사 두 가지를 더합니다.
  - 모든 호출은 해제할 수 없는 함수로 가야 합니다. 다른 fip 함수이거나, 언제 해제할 수 있는지 vstd 명세가 밝힌 std
    함수여야 합니다.
  - 컴파일러가 넣는 모든 drop은 drop해도 해제가 일어날 수 없는 값의 것이어야 합니다.
* `#[verifier::fip(strict)]`은 재귀를 `become`(`#![feature(explicit_tail_calls)]`)으로만 하라고 요구합니다. 다른
  strict 함수와 std, vstd만 부를 수 있습니다.

drop 검사와 스택 검사는 컴파일된 프로그램(유령 코드를 지우고 drop을 배치한 뒤의 MIR) 위에서 돕니다. 그래서 소스에
보이지 않는 drop도 봅니다.

## 예

아래 예들은 다음 리스트 타입을 씁니다.

```rust
pub enum List { Nil, Cons(u64, Box<List>) }

pub open spec fn len(l: List) -> nat
    decreases l
{
    match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
}
```

### `fbip(n)`: 할당 횟수의 상한

`Vec::push`는 최대 한 번 할당합니다. 벡터가 커져야 하면 옛 버퍼를 해제합니다. 할당 상한만 따질 때는 문제가
없습니다.

```rust
fn push_one(v: &mut Vec<u64>)
    allocates 1
{
    v.push(1);
}
```

### `fip`: 소비한 것을 다시 쓰기

들어왔다가 다시 나가는 `Box`는 해제되지 않습니다.

```rust
#[verifier::fip]
fn halve(mut b: Box<List>) -> (r: Box<List>) {
    match &mut *b {
        List::Cons(x, _) => { *x = *x / 2; }
        List::Nil => {}
    }
    b
}
```

FP²의 대표 예는 리스트를 제자리에서 뒤집는 것입니다. 각 칸의 box를 결과의 칸으로 다시 씁니다. 내용은
`mem::replace`로 바꿔 꺼내고, box는 새 칸에 넣습니다.

```rust
#[verifier::fip]
fn reverse(l: List, acc: List) -> (r: List)
    ensures len(r) == len(l) + len(acc),
    decreases l
{
    match l {
        List::Nil => acc,
        List::Cons(x, mut b) => {
            let next = core::mem::replace(&mut *b, acc);
            reverse(next, List::Cons(x, b))
        }
    }
}
```

### `fip(n)`: 새 칸 몇 개

`allocates n`과 함께 쓰면 fip 함수도 할당할 수 있습니다. 해제는 여전히 안 됩니다.

```rust
#[verifier::fip]
fn cons(x: u64, l: List) -> (r: List)
    allocates 1
{
    List::Cons(x, Box::new(l))
}
```

### 상수 스택: `fip(strict)`

위의 `reverse`는 재귀이고, 재귀 호출은 꼬리 위치에 있습니다. 그래도 Rust는 이런 호출이 스택 프레임을 다시 쓴다고
약속하지 않습니다(`opt-level=0`에서는 다시 쓰지 않습니다). 그래서 긴 리스트에서는 스택이 넘칠 수 있습니다.
`become`은 이를 약속하고, 지킬 수 없으면 rustc가 프로그램을 거부합니다.

```rust
#![feature(explicit_tail_calls)]

#[verifier::fip(strict)]
fn reverse(l: List, acc: List) -> (r: List)
    ensures len(r) == len(l) + len(acc),
    decreases l
{
    match l {
        List::Nil => acc,
        List::Cons(x, mut b) => {
            let next = core::mem::replace(&mut *b, acc);
            become reverse(next, List::Cons(x, b))
        }
    }
}
```

루프도 상수 스택을 씁니다. 꼬리 호출이 아닌 재귀(`len(t) + 1`)는 거부됩니다.

### 제네릭 코드

타입 매개변수의 값을 drop하는 fip 함수는 그 drop이 메모리를 해제할 수 없다는 것을 알아야 합니다. unsafe marker
trait `vstd::alloc_check::NoDeallocDrop`이 이를 나타냅니다.

```rust
#[verifier::fip]
fn first<T: vstd::alloc_check::NoDeallocDrop>(a: T, b: T) -> (r: T) {
    a // 여기서 `b`가 drop됩니다
}
```

strict 함수는 그런 drop이 어떤 소멸자를 실행하는지도 알아야 합니다. 그래서 타입 매개변수의 값은 아예 drop할 수
없습니다(`Copy` bound가 있으면 소멸자가 없습니다). 그래도 값을 drop하지 않고 옮기기만 하는 std 함수는 부를 수
있습니다. `mem::swap`, `mem::replace`, slice와 `Vec`의 뷰 함수들이 그렇습니다.

```rust
#[verifier::fip(strict)]
fn swap_ends<T: vstd::alloc_check::AllocFreeDrop>(xs: &mut [T])
    requires old(xs)@.len() >= 2,
    allocates 0
{
    let n = xs.len();
    xs.swap(0, n - 1);
}
```

## 자주 만나는 거부

| 코드 | 거부되는 이유 | 대신 |
|---|---|---|
| `fn unbox(b: Box<List>) -> List { *b }` | `Box`에서 내용을 꺼내면 box가 해제됩니다 | box를 유지해 다시 쓰거나 돌려줍니다 |
| `**tail = t;` | 대입은 먼저 옛 값을 drop합니다 | `mem::replace(&mut **tail, t)`로 바꾸고 옛 값을 돌려주거나 다시 씁니다 |
| 어떤 경로에서 쓰지 않는 매개변수 | 함수 끝에서 drop됩니다 | 돌려주거나, 저장하거나, 결과에 옮겨 넣습니다 |
| fip 함수 안의 `v.push(x)` | `push`는 커질 때 옛 버퍼를 해제할 수 있습니다 | `old(v)@.len() < spec_vec_capacity(&*old(v))`를 요구하거나, fip 함수 밖에서 미리 reserve합니다 |
| `b`를 drop하는 `fn f<T>(a: T, b: T)` | `T`의 drop이 알려져 있지 않습니다 | `T: NoDeallocDrop` (strict 함수에서는 쓸 수 없습니다) |
| strict 함수 안의 `count(n - 1, acc)` | 평범한 꼬리 호출은 여전히 스택을 키울 수 있습니다 | `become count(n - 1, acc)` |
| strict 함수 안의 `len(t) + 1` | 꼬리 호출이 아닙니다 | 누산기와 `become`을 쓰거나 루프로 바꿉니다 |

자리표시자는 drop 없이 덮어쓸 수 있습니다.

```rust
#[verifier::fip]
fn fill(hole: &mut List, v: List)
    requires *old(hole) is Nil,
{
    core::mem::forget(core::mem::replace(hole, v));
}
```

`Nil`은 아무것도 소유하지 않으므로 forget해도 새는 것이 없습니다.

## 도구

`-V fip-lint`(`-V alloc-check`가 필요 없습니다)는 스택을 키우는 재귀를 알려 줍니다.

* `become`이 아닌 꼬리 호출. verus-analyzer의 quick fix가 고쳐 줍니다.
* 생성자를 사이에 둔 재귀(TRMC), 예를 들어 `List::Cons(n, Box::new(range(n - 1)))`. 린터는 같은 일을 하는 루프를
  제안합니다. 이 루프는 매 단계 `&mut` 구멍을 채웁니다. `-V fip-lint=fix`는 이 재작성을 적용하고, crate가 여전히
  검증될 때만 남깁니다.

재작성이 적용되는 조건은 레퍼런스에 있습니다.

## 다루지 않는 것

* **unwinding.** 검사는 정상 반환 경로만 봅니다. unwind하는 panic은 메모리를 해제할 수 있습니다. panic을 배제하려면
  `no_unwind`를 씁니다.
* **누수.** FP²의 함수는 소유한 칸을 정확히 한 번씩 씁니다. 여기서 `#[verifier::fip]`은 해제가 없다는 것만
  약속합니다. `mem::forget`은 허용되고, forget한 것은 샙니다.
* **신뢰.** vstd에 있는 std 명세(`Vec::push`가 언제 해제할 수 있는지, 어떤 std 함수가 아무것도 drop하지 않는지)와
  marker trait impl은 신뢰합니다. 스택 규칙은 `become`에 대한 rustc의 보장과, std와 vstd 함수가 유한한 스택을 쓴다는
  가정을 신뢰합니다.
* **할당기.** 전역 할당기나 시스템 할당기가 아닌 할당기를 쓰는 컨테이너는, 그 할당기가 `FipAllocator`(strict
  함수에서는 `FipStrictAllocator`)를 구현할 때만 fip 함수에서 쓸 수 있습니다.
  [사용자 정의 할당기](./reference-allocates.ko.md)를 보세요.

전체 규칙은 레퍼런스의 `#[verifier::fip]`과 `#[verifier::fip(strict)]` 절([할당 상한](./reference-allocates.ko.md))을
보세요.
