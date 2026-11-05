# 할당 상한 (`allocates`)

> **fork 확장, 실험적 기능.** `allocates` 절과 `-V alloc-check` / `-V alloc-check-strict` 옵션은
> 이 Verus fork에만 있습니다. 이 문서의 영어판은 [여기](./reference-allocates.md)에 있습니다.

`exec` 함수는 자신이 하는 할당기 호출 수의 상한을 명시할 수 있습니다.

```rust
fn make_pair(x: u64) -> (r: (Box<u64>, Box<u64>))
    allocates 2
{
    (Box::new(x), Box::new(x))
}
```

상한은 함수 매개변수에 대한 `int` 타입의 spec 식 하나입니다. 이 식은 함수에 진입할 때 평가됩니다.
그래서 `&mut` 매개변수는 진입 시점의 값(`old(v)`)을 가리킵니다.

```rust
fn push_one(v: &mut Vec<u64>, x: u64)
    allocates if old(v)@.len() == vstd::std_specs::vec::spec_vec_capacity(&*old(v)) { 1int } else { 0int }
{
    v.push(x);
}
```

이 절은 다른 시그니처 절(`requires`, `ensures`, `opens_invariants`, `no_unwind`, ...)과 함께 씁니다.
`exec` 함수와 `exec` 클로저에만 쓸 수 있습니다.

## 상한 검사: `-V alloc-check`

플래그가 없으면 `allocates`는 파싱되어 남아 있을 뿐, 검사하지도 않고 상한을 가정하지도 않습니다.

`-V alloc-check`를 주면, Verus는 `allocates` 상한이 있는 모든 함수를 검사합니다.

* ghost 카운터 `allocated()`는 함수에 진입할 때 0에서 시작합니다.
* exec 호출마다 피호출 함수 자신의 `allocates` 상한(호출 인자를 대입한 값)이 카운터에 더해집니다.
  검사 대상 함수 안에서 `allocates` 상한이 없는 함수를 호출하면 할당 수를 알 수 없으므로 거부됩니다.
* 정상 반환하는 모든 지점에서 카운터는 함수의 상한 이하여야 합니다.

`allocated()`는 루프 불변식과 assertion에 쓸 수 있습니다.

```rust
fn boxes(n: usize) -> (r: Vec<Box<usize>>)
    allocates 1 + n
{
    broadcast use vstd::std_specs::vec::group_vec_axioms;
    let mut v: Vec<Box<usize>> = Vec::with_capacity(n);
    for i in 0..n
        invariant
            v@.len() == i,
            n <= vstd::std_specs::vec::spec_vec_capacity(&v),
            allocated() <= 1 + i,
    {
        v.push(Box::new(i));
    }
    v
}
```

이 계산의 말단에 있는 것은 두 가지입니다.
* vstd가 std 함수에 준 상한입니다. 예를 들어 `Box::new`는 1, `Vec::push`는 벡터가 가득 찼을 때만 1,
  `Vec::with_capacity(0)`는 0입니다.
* `external_body` 함수의 상한입니다. 이 상한은 그 함수의 다른 명세와 마찬가지로 신뢰됩니다.

## 상한의 의미

`allocates e`는 **정상 반환**하는 호출 한 번 동안 Rust *추상 기계*, 곧 소스 프로그램이 하는
할당기 호출 수의 상한입니다. 세는 호출은 메모리를 얻는 것들, 즉 allocate, allocate-zeroed,
reallocate(grow·shrink)입니다. deallocate는 세지 않습니다.

바이트 수, 최대 메모리 사용량(peak), unwind하는 경로의 호출은 제한하지 않습니다.

컴파일된 프로그램은 호출을 더 적게 할 수 있습니다. 컴파일러가 할당을 없애거나 합쳐도 된다는 점이
문서로 정해져 있습니다.
* LLVM LangRef(main @932a5ca)는 할당 생략을 허용합니다. `realloc`을 할당과 해제로 나누고
  그중 하나를 생략하는 것도 허용합니다.
* rustc 1.99.1의 `core::alloc::GlobalAlloc` 문서(`core/src/alloc/global.rs`, rust-lang/rust#159720)는
  할당을 합치는 것도 허용합니다.

소스에 없는 할당기 호출을 컴파일러가 *새로 만드는 것*을 허용하거나 금지하는 현행 문서는 없습니다.
상한은 그런 컴파일러에 대한 주장이 아닙니다. 테스트 `rust_verify_test/tests/alloc_check_runtime.rs`는
검증된 프로그램을 계수용 `#[global_allocator]`와 함께 여러 최적화 수준으로 실행합니다. 그리고 실제
호출 수를 검증된 상한과 비교합니다.

## drop

암묵적인 drop(스코프 끝, 임시값, 재대입, 컨테이너의 drop glue)은 호출로 나타나지 않습니다. 그래서
그 자리에서 비용을 셀 수 없습니다. 대신 `-V alloc-check`는 검사 대상 함수가 실행할 수 있는 모든
`Drop::drop`이 할당하지 않을 것을 요구합니다. 함수가 drop할 수 있는 것은 매개변수 타입과 본문의 모든
식의 타입으로 과대 근사합니다. 이 타입 각각에 대해 다음을 요구합니다.

* `Drop` impl이 있는 사용자 타입은 그 `drop`에 `allocates 0`이 있어야 합니다. 그 `drop`은
  `-V alloc-check`로 검증된 것이어야 합니다.

  ```rust
  pub struct Handle { pub id: u64 }

  impl Drop for Handle {
      fn drop(&mut self)
          opens_invariants none
          no_unwind
          allocates 0
      {
      }
  }
  ```

  `external_body`(또는 `assume_specification`)인 `drop`은 `allocates 0`이 있어도 신뢰하지 않습니다.
  Verus는 그런 `drop`의 본문을 검증 없이 받아들입니다. 그리고 `drop`은 명시적으로 호출되는 일이 없으므로,
  그 주장이 모든 암묵적 drop에 조용히 적용되어 버립니다. vstd 자신의 것만 신뢰합니다.
* 타입의 필드는 재귀적으로 검사합니다.
* 필드가 가려진 타입(`external_body`, 또는 여기서 보이지 않는 private 필드)은 다음 경우에만 받습니다.
  `Copy`이거나, drop이 신뢰되는 std 또는 vstd 타입인 경우입니다.
  std 쪽은 목록에 있는 타입만 신뢰합니다(예: `Vec`, `Box`, `String`, `HashMap`, 그 반복자들, 반복자 어댑터).
  다음 타입은 목록에 없습니다.
  * `BufWriter`: `drop`이 flush하면서 할당할 수 있습니다.
  * `vec::Splice`: `Vec::splice`가 메모리를 확보하는 곳이 바로 그 `drop`입니다.

  `impl<A: Copy> Copy for W<A>`는 인자가 `Copy`일 때만 `W<args>`를 `Copy`로 만듭니다.
* 타입 매개변수 `T`에는 `T: Copy` 또는 `T: vstd::alloc_check::AllocFreeDrop` bound가 필요합니다.

  ```rust
  fn consume<T: AllocFreeDrop>(t: T)
      allocates 0
  {
  }

  unsafe impl AllocFreeDrop for Handle {}
  ```

  `AllocFreeDrop`은 `unsafe trait`입니다. 해당 타입을 drop해도 할당하지 않을 때(drop 규칙을 통과할 때)만
  impl을 받습니다. 그리고 프로그램 안의 모든 impl이 Verus가 검사하는 것이어야 합니다. `verus!` 밖의 impl이나,
  `.vir`를 import하지 않은 의존 crate의 impl은 거부합니다. vstd는 원시 타입, 참조, `Option`, `Result`, 튜플,
  `Box`, `Vec`, `String` 등에 이 trait을 구현해 둡니다.
* 클로저는 자신의 캡처를 drop합니다. 상한이 붙은 클로저는 함수처럼 검사합니다. 그 클로저가 drop할 수 있는
  다른 클로저를 포함해, 캡처가 모두 drop 규칙을 통과해야 합니다.

사용자 정의 할당기(전역이 아닌 `A`에 대한 `Vec<T, A>`)는 아직 지원하지 않습니다. 그 할당기의 `deallocate`와
`clone`에도 상한이 필요하기 때문입니다.

## 콜백, 클로저, trait

제네릭 함수 값을 통한 호출에는 `call_allocates(f, args)`가 청구됩니다. 이는 `f`가 실제로 무엇이든
그것의 상한입니다. 호출자의 상한에 이 항을 쓸 수 있습니다.

```rust
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64
    requires f.requires((x,)),
    allocates call_allocates(*f, (x,))
{
    f(x)
}

fn use_apply() -> u64
    allocates 0
{
    let half = |y: u64| -> (r: u64) allocates 0 { y / 2 };
    apply(&half, 7)
}
```

`allocates` 상한이 있는 클로저나 함수에서는 `call_allocates`가 곧 그 상한입니다. 사용자 코드를 부르는
std 함수에 대한 vstd 명세도 같은 방식으로 그 호출을 청구합니다. 예를 들어 `Vec::clone`은 원소마다
`T::clone`을 한 번씩 청구합니다. `HashMap::insert`는 `Hash`/`Eq` 콜백을 `hash_ops_cost(m, k)`로 청구합니다.

trait 메서드 선언에 붙은 상한은 모든 구현을 제한합니다.

```rust
pub trait Shape {
    fn area(&self) -> u64 allocates 0;
}

fn total<S: Shape>(a: &S, b: &S) -> u64
    allocates 0
{
    let x = a.area();
    let y = b.area();
    if x < 1000 && y < 1000 { x + y } else { 0 }
}
```

각 impl은 선언의 상한에 대해 검사합니다. 그 결과 다음이 성립합니다.

* 그런 메서드의 impl은 모두 Verus가 검사한 것이어야 합니다. 다음 impl은 이 crate가 그 impl을 쓰지 않더라도
  거부합니다.
  * `-V alloc-check` 없이 검증된 crate의 impl
  * `verus!` 밖의 impl
  * `.vir`를 import하지 않은 의존 crate의 impl
* 사용자가 쓴 `external_trait_specification`의 메서드에는 상한을 붙일 수 없습니다. 그 trait의 구현과
  기본 메서드는 Verus가 검사하지 않기 때문입니다.

  예외는 std trait에 vstd가 붙인 상한입니다. 이 상한은 모두 구현별 항(`iter_next_cost`,
  `iter_adapter_cost`, ...)이고, std 자신의 타입에 대해서만 값이 정해집니다. 예를 들어
  `Iterator::rev`의 비용은 `iter_adapter_cost::<Self>()`이며, std 반복자에서는 0입니다.
  제네릭 반복자 `I`에서는 `iter_aux_alloc_free::<I>()`가 성립할 때만 0입니다.
* `-V check-api-safety`에서는 공개된 안전 trait 메서드에 붙은 상한을 거부합니다. 검증되지 않은 안전한 코드가
  상한을 지키지 않고 그 trait을 구현할 수 있기 때문입니다. `requires`, `no_unwind`, `opens_invariants`와
  같은 규칙입니다.

## 라이브러리와 다른 crate

import한 crate의 상한은 그 crate가 다음 조건으로 검증되었을 때만 신뢰합니다.
* `-V alloc-check`로 검증했습니다.
* 전체를 검증했습니다(`--no-verify`나 `--verify-*` 필터를 쓰지 않았습니다).
* 검증이 성공했습니다.

구체적으로는 다음 규칙이 적용됩니다.

* export된 `.vir` 파일은 먼저 상한을 "검사 안 됨"으로 표시해 기록됩니다. 검증과 컴파일이 모두 성공한
  뒤에야 "검사됨"으로 표시해 다시 기록됩니다. 따라서 다른 crate가 그 상한을 쓰려면 라이브러리를
  `--compile`과 함께 빌드해야 합니다. `cargo verus`와 vstd 빌드는 이미 그렇게 합니다.
* `.vir` 파일에는 컴파일된 crate의 SVH가 기록됩니다. 가져오는 쪽은 링크된 crate가 다른 빌드(예: 소스의
  예전 버전)인 `.vir`를 거부합니다.
* 이름이 `std`, `core`, `alloc`인 의존 crate는 toolchain의 sysroot에서 와야 하고, 각각 하나만 있어야 합니다.
  import한 crate가 `vstd`라는 이름이면, vstd로 검증된 것이어야 하고 링크된 vstd와 함께 빌드된 것이어야 합니다.
* `-V alloc-check`로 검증하는 crate 자신의 이름은 `std`, `core`, `alloc`일 수 없습니다. vstd 자신이 아니면
  `vstd`일 수도 없습니다.

## `-V alloc-check-strict`

`-V alloc-check-strict`는 `-V alloc-check`가 하는 일에 더해, `allocates` 상한이 있는 모든 함수가 `no_unwind`일
것을 요구합니다. 그래서 panic 경로가 존재하지 않습니다. 또 클로저에는 상한을 붙일 수 없습니다.
할당하는 std 함수(`Box::new`, `Vec::push`, ...)에 대한 vstd 명세는 `no_unwind`가 아닙니다. capacity
overflow가 unwind할 수 있는 `panic!`이기 때문입니다. 그래서 실제로는 할당하는 함수가 아직 strict 모드를
통과할 수 없습니다.

## 신뢰 기반과 한계

`-V alloc-check`가 신뢰하는 것:
* std 함수에 대한 vstd 명세의 상한, 그리고 위에서 설명한 std trait 메서드에 대한 vstd 상한의 설계
* `drop`이 아닌 `external_body` 함수
* toolchain의 std(신뢰하는 drop과 불투명 타입)

알려진 한계는 다음과 같습니다. 모두 프로그램을 거부하는 쪽이며, 불건전하지는 않습니다.
* 사용자 정의 할당기
* `dyn` 값이나 불투명 `impl Trait` 값의 drop
* drop glue 안의 projection 타입(예: `Cow`)
* 구조체의 필드 하나만 캡처하는 클로저를 구조체 전체를 캡처한 것처럼 검사하는 점
* 프로그램 어디에든 상한 있는 trait 메서드의 검사되지 않은 구현이 있는 경우

검사 대상 함수 안에서 `catch_unwind`는 거부합니다. panic을 잡으면 unwind 경로에서 일어난 할당 뒤에도
실행이 계속되는데, `allocates`는 그 할당을 세지 않기 때문입니다.
