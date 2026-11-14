# 업스트림 Verus 대비 변경 사항 (fork)

> **이 페이지는 Verus의 fork를 설명합니다.** 이 fork의 `fip-beta` 브랜치가 업스트림 Verus
> ([verus-lang/verus](https://github.com/verus-lang/verus))에서 무엇을 바꾸는지 정리하고, 각 변경을 설명하는
> 페이지로 안내합니다. 영어판은 [여기](./fork-changes.md)에 있습니다.

## 기준점과 브랜치

fork는 업스트림 커밋 `8bf68ee74`(2026-11-02, "Update no-cheating to disallow various command-line flags
that violate the spirit of not cheating", #3392)에서 갈라졌습니다. 변경은 두 층으로 되어 있습니다.

| 브랜치 | 툴체인 | 더하는 것 |
|---|---|---|
| `fip` | Rust 1.99.1 (업스트림과 같음) | 할당 상한: `allocates` 절, `-V alloc-check`, `-V alloc-check-strict`, vstd의 std 명세에 붙은 상한 |
| `fip-beta` | Rust 1.100.0-beta.10 (`beta-2026-11-05`) | `fip`의 전부, 그리고 Rust 1.100, 사용자 정의 할당기와 할당기 상태, 완전한 제자리 함수, `-V fip-lint`, `trusted_only`/`trusted_call` |

이 페이지의 내용은 모두 `fip-beta`에 있습니다. 아래 표의 "도입" 열은 두 브랜치 중 어디서 들어왔는지를 나타냅니다.

새 검증 기능은 모두 실험적입니다.

## 툴체인: Rust 1.100 beta

`rust-toolchain.toml`과 CI workflow는 `beta-2026-11-05`, 즉 Rust 1.100.0-beta.10을 씁니다. 업스트림은 1.99.1을
씁니다. Verus가 자기 소스 트리에 들고 있는 rustc 부분(`rustc_hir_analysis`, `rustc_hir_typeck`,
`rustc_mir_build`)도 같은 버전으로 올렸습니다.

검증 코드에 생기는 차이는 다음과 같습니다.

* **`box` 패턴이 없어졌습니다.** Rust 1.100에서 제거되었습니다. 대신 Verus는 `Box`, `Rc`, `Arc`를 통과하는
  `deref!(p)` 패턴을 받습니다. 뜻은 예전의 `box p`와 같습니다. 예전에 `box_patterns` feature를 켰던 것처럼,
  검증하는 crate에 `deref_patterns` feature를 켭니다. 다른 타입을 통과하는 deref 패턴은 지원하지 않습니다.
* **`core::convert::Infallible`이 이제 `!`의 별칭입니다.** 그래서 Verus는 `Infallible` 타입의 필드가 있는
  데이터 타입을 거부합니다("never-to-any coercion is not allowed in spec mode"). Rust 1.99.1에서는 받았습니다.
  never 타입 `!` 자체는 안정화되었고 명세가 필요 없습니다.
* **`allocator_api`가 일부만 안정화되었습니다.** 안정화되지 않은 부분은 이제 `allocator_ext` feature입니다.
  vstd는 이 feature를 켭니다. 그 부분을 쓰는 crate도 켜야 합니다.
* **`BTreeMap`과 그 반복자는 `A: AllocatorClone`을 요구합니다.** vstd의 명세도 그렇게 적습니다.
* **`[const] Destruct` bound**는 std 1.100이 `Iterator for Range<A>` 등에 붙였습니다. const 문맥 밖에서는
  무시합니다.
* **새 std 항목.** `vstd::std_specs::rust_1_100` 모듈이 Rust 1.100에서 안정화된 std 항목 가운데 Verus가 쓸 수
  있는 것들을 명세합니다. `bool::toggle`, `mem::DropGuard`,
  `UnsafeCell::{as_ref_unchecked, as_mut_unchecked, replace}`, 타입으로서의 `Allocator`, `AllocError`,
  `Layout`과 `Global`, `System`의 `Allocator` impl, `Vec::from_fn`, `Vec::allocator`, `Box::allocator`,
  `Box::new_in`, `Box::take`, `Box::map`, `Rc::map`, `Arc::map`, `Default for Once`입니다. 다루지 않는 것과
  그 이유는 모듈 문서에 있습니다(예: 사전조건으로 적을 수 없는 `mem::conjure_zst`). `alloc::Global`은 더
  이상 `external_body`가 아니어서 검증 코드에서 만들 수 있습니다.

## 새 기능

| 기능 | 쓰는 법 | 도입 | 문서 |
|---|---|---|---|
| 할당 상한 | `exec` 함수나 클로저에 `allocates n`, `-V alloc-check`로 검사 | `fip` | [할당 상한](./reference-allocates.ko.md) |
| 할당 상한이 있으면 unwind 없음 | `-V alloc-check-strict` | `fip` | [할당 상한](./reference-allocates.ko.md)의 `-V alloc-check-strict` 절 |
| 사용자 정의 할당기 | `unsafe impl BoundedAllocator for A`, 그다음 `Vec<T, A>`, `Box<T, A>` 등 | `fip-beta` | [할당 상한](./reference-allocates.ko.md)의 "사용자 정의 할당기" 절 |
| 상태 있는 할당기 | `vstd::alloc_heap`(`allocator_state`, `AllocAuth`) | `fip-beta` | [할당 상한](./reference-allocates.ko.md)의 "상태 있는 할당기" 절 |
| bound 명세 | 타입 매개변수, `where` 절, impl, struct의 `T: Tr with { .. }` | `fip-beta` | [할당 상한](./reference-allocates.ko.md)의 "bound 명세" 절 |
| 완전한 제자리 함수 (해제 없음) | `#[verifier::fip]` | `fip-beta` | [FIP와 FBIP](./fip-fbip.ko.md), [레퍼런스](./reference-allocates.ko.md) |
| 상수 스택 공간 | `become`과 함께 `#[verifier::fip(strict)]` | `fip-beta` | [FIP와 FBIP](./fip-fbip.ko.md), [레퍼런스](./reference-allocates.ko.md) |
| fip 코드의 제네릭 연산자 호출 | `T: FipAdd`, `T: FipOrd` 등 (`core`의 연산자 trait마다 `FbipOp`, `FipOp`, `FipStrictOp`) | `fip-beta` | [할당 상한](./reference-allocates.ko.md)의 "연산자 trait" 절 |
| 스택 증가 린터 | `-V fip-lint`, `-V fip-lint=fix` | `fip-beta` | [FIP와 FBIP](./fip-fbip.ko.md)의 "도구" 절 |
| 안전 조건을 명세할 수 없는 호출 | `#[verifier::trusted_only]`, `#[verifier::trusted_call]` | `fip-beta` | [Attributes](./reference-attributes.md#verifiertrusted_only-and-verifiertrusted_call) (영어) |

이 기능들을 위한 새 vstd 항목은 `vstd::alloc_check`(`AllocFreeDrop`, `NoDeallocDrop`, `BoundedAllocator`,
`FipAllocator` 같은 marker trait, 그리고 `FipAdd`, `FipOrd` 같은 연산자 marker), `vstd::alloc_heap`, `vstd::resource::impls::preorder_auth`에 있습니다.
`PreorderAuth`는 권위 있는 상태와 배타적인 하한 조각을 짝지은 것으로, 할당기 heap이 씁니다.

## 새 옵션 없이도 적용되는 변경

새 검사는 해당 옵션(`-V alloc-check`, `-V alloc-check-strict`, `-V fip-lint`)을 줄 때만 돕니다. 다음은 모든
실행에 적용됩니다.

* **새 구문.** `allocates` 절은 언제나 파싱해서 보관합니다. `-V alloc-check`가 없으면 검사하지 않고, 그 상한을
  가정하지도 않습니다.
* **`trusted_only` 함수.** `#[verifier::trusted_only]`가 붙은 함수는 `#[verifier::trusted_call]` 블록 안에서만
  부를 수 있고, 값으로 쓸 수 없습니다. vstd는 `Allocator::{deallocate, grow, grow_zeroed, shrink}`(와 그
  구현)와 `UnsafeCell::{as_ref_unchecked, as_mut_unchecked, replace}`에 이 표시를 붙입니다.
* **`--no-cheating`**은 검증하는 crate 안의 `#[verifier::trusted_call]`을 거부합니다.
* **`-V fip-lint=fix`**는 crate의 일부만 검증하는 옵션(`--no-verify`, `--verify-module`, `--verify-function`,
  `--no-lifetime` 등)과 함께 쓸 수 없습니다. 재작성은 crate 전체가 여전히 검증될 때만 남기 때문입니다.
* **vstd.** 위의 모듈 말고도, std 명세에 `allocates` 상한이 붙었습니다. `vstd::std_specs::ptr`는
  `ptr::NonNull`을 명세합니다. 기준 커밋 시점에 병합되지 않았던 업스트림 pull request #3258에서 가져왔습니다.

## 도구와 테스트

* **verita**에 `use_verus_repo` 키가 생겼습니다. 이 키가 있는 프로젝트는 `git_url` 대신 테스트하는 Verus
  저장소에서 가져옵니다. `run_configuration_all.toml`은 vstd에 이 키를 씁니다. vstd의 소스는 검증기와 맞아야
  하기 때문입니다.
* **rust_verify_test**는 `target-verus`를 실행된 경로 그대로의 테스트 바이너리 옆에서 찾습니다. 그래서
  `source/target`이 심볼릭 링크여도 테스트가 돕니다. cargo 1.100의 빌드 디렉터리 구조에서도 테스트 바이너리를
  찾습니다.
* **`alloc_check_runtime`** 테스트 스위트는 검증된 프로그램을 호출 횟수를 세는 `#[global_allocator]`로 여러
  최적화 수준에서 실행합니다. 그리고 실제 할당기 호출을 검증된 상한과 비교합니다.
* **포매터와 편집기.** 이 fork가 더한 구문(`allocates` 절, bound 명세 `T: Tr with { .. }`, Verus 코드 안의
  `become`)은 [verusfmt](https://github.com/newsniper-org/verusfmt)와
  [verus-analyzer](https://github.com/newsniper-org/verus-analyzer)의 fork의 `fip-beta` 브랜치가 파싱합니다.
  두 도구의 배포판은 이 구문을 구문 오류로 보고합니다. (vstd는 그 verusfmt로 포맷합니다.)

## 바뀌지 않은 것

* **SMT 쪽.** SMT 질의로의 인코딩을 맡는 `air`는 바뀌지 않았습니다. solver도 같습니다. 업스트림이 고정한
  버전의 Z3입니다.
* **명령줄 옵션.** 업스트림 옵션 가운데 없어지거나 뜻이 바뀐 것은 없습니다. fork는 옵션을 더하기만 합니다.

이 저장소의 테스트 밖에 있는 코드에서 업스트림과 fork를 비교해 본 적은 아직 없습니다.
