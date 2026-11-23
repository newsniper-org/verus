# 할당 상한 (`allocates`)

> **fork 확장, 실험적 기능.** `allocates` 절과 `-V alloc-check` / `-V alloc-check-strict` 옵션은
> 이 Verus fork에만 있습니다. 이 문서의 영어판은 [여기](./reference-allocates.md)에 있습니다.
>
> 완전 제자리 함수(FP²의 `fip`과 `fbip`)를 예와 함께 소개하는 글은 [FIP와 FBIP](./fip-fbip.ko.md)에 있습니다.

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

세는 것은 컴파일된 프로그램의 횟수인데, Verus는 crate를 검증하는 단계와 컴파일하는 단계를 따로 거칩니다.
그래서 둘의 코드가 같아야 합니다. `-V alloc-check`에서는(`--no-verify`가 아니고, `--is-vstd`나
`--is-core`가 아니면) 다음을 지켜야 합니다.
* crate 자신의 소스가 cfg `verus_keep_ghost_body`를 쓸 수 없습니다. Verus는 이 cfg를 검증할 때만 켭니다.
  `#[cfg(..)]`, `#[cfg_attr(..)]`, `cfg!(..)`, `macro_rules!` 등 주석과 문자열 밖이면 어디든 마찬가지입니다.
  이 이름을 조각으로 만들 수 있는 `${concat(..)}`의 feature `macro_metavar_expr_concat`도 켤 수 없습니다.
  `verus_no_vstd`도 같습니다. `--no-vstd`에서 Verus는 이것을 컴파일할 때만 켭니다. crate의 소스란 rustc가
  읽는 방식으로 읽은 그 파일들과 `-Z crate-attr` 인자입니다. `include_str!`, `include_bytes!`,
  `#[debugger_visualizer]`가 읽는 파일도 들어가므로, 그런 파일도 Rust로 읽었을 때 이 cfg 이름이 나오면
  거부됩니다. Verus가 빌드할 때만 넣을 코드에는 둘 다에서 켜지는 `verus_keep_ghost`를 쓰십시오.
* Verus의 매크로가 둘 중 한쪽에만 넣는 항목을 구별할 수 있는 것도 crate의 소스에 쓸 수 없습니다. 그런
  항목은 spec·proof 함수와 매크로 자신의 항목(`#[verus_spec(with ..)]` 함수 `f`에 대한
  `_VERUS_VERIFIED_f` 등)입니다. 쓸 수 없는 것은 `cfg_accessible`, 그리고 Verus의 매크로가 만드는
  이름에 예약된 `VERUS_`, `_VERUS_`, `__VERUS_`, `_verus_`로 시작하는 이름입니다.
* crate 루트는 표준 입력이 아니라 파일이어야 합니다.
* 컴파일은 검증이 읽은 것만 읽을 수 있습니다. crate의 파일을 읽을 때마다, 그 내용은 검증이 그 파일에서
  읽은 내용 가운데 하나여야 합니다. cfg도 위의 둘을 빼면 같아야 합니다. (검증이 파일을 더 많이 읽는 것은
  괜찮습니다. proof 함수 안의 `include!`가 읽는 파일 등.)

## 상한의 의미

`allocates e`는 **정상 반환**하는 호출 한 번 동안 Rust *추상 기계*, 곧 소스 프로그램이 하는
할당기 호출 수의 상한입니다. 세는 호출은 메모리를 얻는 것들, 즉 allocate, allocate-zeroed,
reallocate(grow·shrink)입니다. deallocate는 세지 않습니다.

바이트 수, 최대 메모리 사용량(peak), unwind하는 경로의 호출은 제한하지 않습니다.

컴파일된 프로그램은 호출을 더 적게 할 수 있습니다. 컴파일러가 할당을 없애거나 합쳐도 된다는 점이
문서로 정해져 있습니다.
* LLVM LangRef(main @932a5ca)는 할당 생략을 허용합니다. `realloc`을 할당과 해제로 나누고
  그중 하나를 생략하는 것도 허용합니다.
* rustc 1.100의 `core::alloc::GlobalAlloc` 문서(`core/src/alloc/global.rs`, rust-lang/rust#159720)는
  할당을 합치는 것도 허용합니다.

소스에 없는 할당기 호출을 컴파일러가 *새로 만드는 것*을 허용하거나 금지하는 현행 문서는 없습니다.
상한은 그런 컴파일러에 대한 주장이 아닙니다. 테스트 `rust_verify_test/tests/alloc_check_runtime.rs`는
검증된 프로그램을 계수용 `#[global_allocator]`와 함께 여러 최적화 수준으로 실행합니다. 그리고 실제
호출 수를 검증된 상한과 비교합니다.

## drop

암묵적인 drop(스코프 끝, 임시값, 재대입, 컨테이너의 drop glue)은 호출로 나타나지 않습니다. 할당은 그
자리에서 세지 않습니다(해제는 셉니다. "해제 상한" 절 참고). 대신 `-V alloc-check`는 검사 대상 함수가 실행할 수 있는 모든
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
* `dyn` 값은 소멸자를 알 수 없으므로, 함수가 그것(`Box<dyn Tr>`, 또는 그것을 담은 값)을 drop해서는 안 됩니다.
  어떤 값을 drop하는지는 컴파일된 프로그램에서 검사합니다. 옮기기만 하는(돌려주거나 넘기는) `Box<dyn Tr>`는
  괜찮습니다. 그런 타입으로 인스턴스화한 std 호출은, std가 거기서 타입 인자의 값을 drop하지 않는 경우가 아니면
  거부합니다("다른 crate에서 오는 콜백" 참고). 컴파일된 프로그램을 건너뛰는 `--no-lifetime`이나
  `--no-erasure-check`에서는 대신 매개변수와 식의 타입을 검사합니다(`dyn`이 있으면 거부). `allocates` 상한이 붙은
  클로저는 아직 `dyn` 값을 아예 다룰 수 없습니다.

### 사용자 정의 할당기

할당기(`core::alloc::Allocator`)는 FP²의 메모리 관리자처럼 런타임입니다. `-V alloc-check`는 프로그램이
할당기를 부르는 호출을 세고, 할당기가 하는 일은 세지 않습니다. 어떤 할당기든 다음과 같습니다.

* `allocate`, `allocate_zeroed`: 호출마다 할당 1이고, 아무것도 해제하지 않습니다.
* `grow`, `grow_zeroed`, `shrink`: 호출마다 할당 1이고, 해제할 수 있습니다(블록을 옮길 수 있음).
* `deallocate`: 할당은 0이고, 해제합니다.

그래서 커지는 `Vec::push`는 어떤 할당기든 1이고(버퍼가 없는 벡터는 `allocate`를, 버퍼가 있는 벡터는
`grow`를 부릅니다), `Box::new_in`은 1입니다(크기 0인 타입이면 아무것도 부르지 않으므로 0). 이미 가진
메모리를 내주는 arena도 호출마다 1입니다. 그 호출은 프로그램의 것이기 때문입니다.

할당기 자신의 코드(그 타입의 `Allocator`, `Clone`, `Drop` impl)는 `allocates`, `#[verifier::fip]`, drop
규칙으로 검사하지 않습니다. 그 코드가 (전역 할당기나 다른 할당기에서) 할당하는 것, 해제하는 것, 쓰는 스택은
세지 않습니다. 그래서 다음이 성립합니다.

* 할당기는 `verus!` 안에 있을 필요도, 그 crate가 `-V alloc-check`로 검증될 필요도 없습니다. (`verus!`
  안에 있으면 Verus는 나머지, 즉 아래의 `ensures`는 그대로 검증합니다.)
* 컨테이너를 drop하면 할당기의 `deallocate`를 부르고 할당기를 drop합니다. 그래서 상한 있는 함수는 어떤
  할당기를 쓰는 컨테이너든 drop할 수 있습니다. (fip 함수는 여전히 안 됩니다. 버퍼를 해제하는 것은 프로그램의
  해제이기 때문입니다.)
* 컨테이너를 clone하면(`split_off`도) 할당기도 clone하는데, 이것은 세지 않습니다. std 컨테이너가 Verus가
  보지 못하는 곳에서 하는 clone도 마찬가지입니다(`BTreeMap`을 drop하면 해제하는 노드마다 할당기를
  clone합니다). 할당기의 `a.clone()` 호출은 0입니다.
* fip 함수와 strict 함수는 어떤 할당기든 쓸 수 있습니다. 제네릭 `A: Allocator`도 됩니다.

```rust
use std::alloc::{Allocator, AllocError, Global, Layout};
use std::ptr::NonNull;

pub struct Twice;

unsafe impl Allocator for Twice {
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>) {
        let _ = Global.allocate(layout); // 할당기 자신의 것: 세지 않음
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) { }
}

fn push_one(v: &mut Vec<u64, Twice>, x: u64)
    allocates if old(v)@.len() == spec_vec_capacity(&*old(v)) { 1int } else { 0int }
{
    v.push(x);
}
```

따라서 사용자 정의 할당기를 쓰는 함수의 상한은 그 할당기가 전역 할당기를 몇 번 부르는지에 대해서는 아무것도
말하지 않습니다. 상한은 할당기로 들어가는 호출을 셉니다("신뢰와 한계" 참고).

`deallocate`, `grow`, `grow_zeroed`, `shrink`는 `#[verifier::trusted_only]`입니다. std는 포인터가 이
할당기의 살아 있는 블록이고 layout이 맞을 것을 요구하는데, 이 조건은 전제조건으로 쓸 수 없습니다.
그래서 검증된 코드는 이 메서드들을(어떤 할당기든, 제네릭 `A: Allocator`를 거치더라도) 위의 전달 호출처럼
[`#[verifier::trusted_call]`](./reference-attributes.md#verifiertrusted_only-and-verifiertrusted_call) 블록
안에서만 부를 수 있습니다. 그 호출은 신뢰되고, 함수의 나머지는 그대로 검증되며, 블록 안에서 만든 클로저는
신뢰되지 않습니다. `--no-cheating`은 이 블록을 거부하므로, 그 아래에서는 할당기가 `deallocate`를 다른
할당기에 넘길 수 없습니다.

검증된 코드에서 메모리를 해제하려면 대신 `vstd::raw_ptr::deallocate`와 그 `Dealloc` 권한을 씁니다
(`raw_ptr::allocate`는 할당 한 번, `raw_ptr::deallocate`는 0번). 할당기도 `--no-cheating` 아래에서 같은
방법을 쓸 수 있습니다. 할당기가 돌려준 메모리는 호출자(std의 컨테이너)의 것이므로, Verus는 할당기가 그 블록의
권한을 쥐고 있지 않은지 검사합니다.

* 사용자의 `allocate`(또는 `allocate_zeroed`, `grow`, `grow_zeroed`, `shrink`) 본문에서 `Ok`로 돌려주는 블록은
  다음 중 하나여야 하고, 그 호출에서 마지막으로 그렇게 얻은 블록이어야 합니다.
  * 본문이 `vstd::alloc_check::hand_out(pt, block)`으로 권한을 내놓은 블록. 이 함수는 블록을 정확히 덮는
    `PointsToRaw`를 소비하고 영수증 `Handout`을 돌려줍니다.
  * 다른 할당기에서 받은 블록. 그 메모리의 권한은 Verus에 처음부터 없습니다.
  * `external_body` 함수에서 받은 블록. 다른 `external_body`처럼 신뢰합니다.

  `hand_out`은 이 본문 안에서만 부를 수 있고, 거기서 부르는 함수나 클로저에서는 부를 수 없습니다.
* `deallocate`(또는 `grow`, `grow_zeroed`, `shrink`) 본문에서 `vstd::alloc_check::reclaim(ptr, layout,
  receipt)`은 해제되는 블록의 권한을 되찾습니다.
  * `ptr`은 그 메서드의 `ptr`이어야 하고, 한 번만 부를 수 있습니다.
  * `Err`를 돌려주는 `grow`나 `shrink`는 이것을 부르지 않았어야 합니다. 옛 블록이 여전히 호출자의 것이기
    때문입니다.
  * 영수증이 그 블록이 무엇이었는지(주소, 길이, provenance) 알려 줍니다.
  * `reclaim`은 std의 `Allocator` 계약에 기댑니다. `deallocate`는 이 할당기(또는 동등한 할당기)가 내준, 아직
    살아 있고 호출자가 더는 쓰지 않는 블록만 받습니다. 검증된 코드는 `deallocate`를 부를 수 없습니다
    (`trusted_only`).

* 블록은 충분히 크고 정렬되어 있어야 합니다. `Allocator` 선언의 사후조건 `allocator_block_fits(r, layout)`
  (`grow`와 `shrink`는 `new_layout`)은 `Ok`로 돌려준 블록이 길이 `layout.size()` 이상이고 `layout.align()`에
  맞춰 정렬되어 있다고 말합니다(std 계약 그대로). 사용자 impl은 이를 증명해야 합니다.
* 사용자의 `grow`, `grow_zeroed`, `shrink`는 옛 블록의 내용을 새 블록으로 옮겨야 하는데, Verus는 이를 검사할 수
  없습니다(raw 메모리의 권한은 그 안의 값을 말하지 않습니다). 그래서 `#[verifier::external_body]`(신뢰,
  `--no-cheating`은 거부)로만 받습니다. 정의하지 않으면 std의 기본 본문(할당, 복사, 해제)을 쓰며, 이는
  안전합니다.

그래서 해제하는 할당기는 다음과 같습니다.

* `allocate`는 `raw_ptr::allocate(layout.size(), layout.align())`로 블록을 받습니다(`Layout::size`와
  `Layout::align`이 그 쌍이 `valid_layout`임을 알려 줍니다). 돌려줄 `NonNull<[u8]>`는
  `core::ptr::slice_from_raw_parts_mut`와 `NonNull::new`로 만들고, 그 블록을 내놓습니다. 영수증과 `Dealloc`은
  블록의 포인터·layout과 함께 `&self`에서 닿는 상태에 둡니다(그것들을 기록한 `PCell` 위의 `LocalInvariant`,
  `Sync` 할당기라면 `AtomicInvariant`).
* `deallocate`는 그 기록에서 주소와 layout을 찾았을 때만 블록을 해제합니다. 영수증으로 권한을 되찾고
  `raw_ptr::deallocate`를 부릅니다. 나머지는 건드리지 않습니다(std는 다른 것을 넘기지 않습니다).
  `deallocate`에는 전제조건을 붙일 수 없으므로, 불변식과 셀을 잇는 사실은 타입 불변식으로 둡니다.

테스트 `one_slot_allocator_frees_no_cheating`(`rust_verify_test/tests/alloc_check_custom_allocator.rs`)이
한 번에 블록 하나를 다루는 이런 할당기입니다.

### 자체 API의 할당기: `encapsulates alloc(a, d)`

`core::alloc::Allocator`를 구현하지 않는 할당기(자체 `alloc`과 `free`를 가진 풀이나 slab)는 Verus가 다른 코드와
똑같이 검사합니다. 카운터만 올리는 본문이면 `allocates 0`이 성립하지만, 프로그램의 관점에서는 그 호출이 할당입니다.
이런 함수에는 `encapsulates alloc(a, d)`를 붙입니다. 호출 한 번이 할당 `a`번, 해제 `d`번으로 셉니다(`a`와 `d`는
`nat`이고 인자에 기댈 수 있습니다).

```rust
pub struct Pool { /* .. */ }

impl Pool {
    fn alloc(&mut self) -> (r: Slot) encapsulates alloc(1, 0) { /* .. */ }
    fn free(&mut self, s: Slot) encapsulates alloc(0, 1) { /* .. */ }
    fn release_many(&mut self, k: u64) encapsulates alloc(0, if k > 0 { 1 } else { 0 }) { /* .. */ }
}

fn two(p: &mut Pool) -> (Slot, Slot)
    allocates 2
{
    (p.alloc(), p.alloc())
}
```

* 호출하는 쪽은 할당 `a`번, 해제 `d`번으로 청구되고(함수의 `allocates`가 `a`, `deallocates`가 `d`), 호출은 `d > 0`인
  곳에서 메모리를 해제할 수 있습니다(그래서 fip 함수는 `d == 0`을 보일 수 있는 곳에서만 부를 수 있습니다).
  `call_allocations`/`f.allocations(..)`와 `call_deallocations`/`f.deallocations(..)`는 `a`와 `d`이고,
  `call_allocates`/`f.allocates(..)`와 `call_deallocates`/`f.deallocates(..)`는 `a > 0`과 `d > 0`입니다.
* 본문은 `Allocator`의 본문처럼 런타임의 것입니다. 본문이 할당하거나 해제하거나 스택을 쓰는 것은 검사하지 않으므로,
  전역 할당기로 풀을 다시 채울 수 있습니다. `ensures`는 평소처럼 검증합니다. strict 함수는 이것을 리프로 부를 수
  있습니다.
* `allocates`나 `#[verifier::fip]`과 함께 쓸 수 없고, spec·proof 함수와 trait 메서드 선언에는 쓸 수 없습니다. 상한이나
  조건이 있는 trait 메서드의 구현에서는 `a`가 상한 안에, `d > 0`이 조건 안에 있어야 합니다(진입 시점에, `requires`를
  만족하는 모든 입력에 대해 검사합니다. `#[verifier::fip]` 선언의 구현은 fip여야 하므로 쓸 수 없습니다).
* `assume_specification`에도 쓸 수 있습니다. 다른 언어로 된 할당기라면
  `pub assume_specification[ ffi_alloc ](n: usize) -> *mut u8 encapsulates alloc(1, 0);`처럼 씁니다.
* `Allocator` impl처럼 신뢰합니다. `alloc(0, 0)`이라고 적고 할당하는 함수는 그 할당을 숨깁니다("신뢰 기반과 한계" 참고).

## 콜백, 클로저, trait

제네릭 함수 값을 통한 호출에는 `call_allocations(f, args)`가 청구됩니다. 이는 `f`가 실제로 무엇이든
그것의 상한입니다. 호출자의 상한에 이 항을 쓸 수 있습니다.

```rust
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> u64
    requires f.requires((x,)),
    allocates call_allocations(*f, (x,))
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

`allocates` 상한이 있는 클로저나 함수에서는 `call_allocations`가 곧 그 상한입니다. 사용자 코드를 부르는
std 함수에 대한 vstd 명세도 같은 방식으로 그 호출을 청구합니다. 예를 들어 `Vec::clone`은 원소마다
`T::clone`을 한 번씩 청구합니다. `HashMap::insert`는 `Hash`/`Eq` 콜백을 `hash_ops_cost(m, k)`로 청구합니다.

`call_allocates(f, args)`(`bool`: 그 호출이 할당할 수 있는가)는 `allocates` 상한이 양수인지입니다
(`allocates allocates_when(a, c)`이면 `c`). 횟수가 양수이면 이것이 참이므로, `requires !f.allocates(x)`를 요구하는
제네릭 함수는 그 호출에 0으로 청구됩니다.

해제 쪽도 같습니다("해제 상한" 절 참고). `call_deallocations(f, args)`(횟수)와 `call_deallocates(f, args)`(해제할 수
있는가)는 `#[verifier::fip]` 함수에서는 0과 `false`이고, 그 밖에는 `deallocates` 상한과 그것이 양수인지(또는
`deallocates_when(d, c)`의 조건 `c`)이며, 선언에 상한이 있는 trait 메서드에서는 (모든 구현에 대해) 많아야 그것입니다.
`verus!` 안의 ghost 코드(명세, `assert` 등)에서 `f.allocations(args)`, `f.allocates(args)`, `f.deallocations(args)`,
`f.deallocates(args)`는 `call_allocations(f, (args,))` 등입니다(exec 코드의 같은 이름 메서드는 그대로 둡니다). 그래서
다른 함수에 넘기는 명세는 이것들을 모두, 일부 인자에서만 성립하는 조건도 그대로 넘길 수 있습니다.

```rust
#[verifier::external_body]
fn shrink_if_big(x: u64) -> (r: u64)
    allocates 0
    deallocates deallocates_when(1int, x > 5)
{ x }

#[verifier::external_body]
fn outer(x: u64) -> (r: u64)
    allocates shrink_if_big.allocations(x)
    deallocates deallocates_when(shrink_if_big.deallocations(x), shrink_if_big.deallocates(x))
{ shrink_if_big(x) }

#[verifier::fip]
fn small() -> (r: u64) {
    outer(3) // 됨: `shrink_if_big.deallocates(3)`은 거짓
}
```

std의 blanket `Into`(그리고 `TryInto`, `Into`를 거치는 `TryFrom`)에 대한 vstd 명세도 이렇게 자기가 부르는
`From` impl에 넘깁니다.

함수 값의 호출에도 같은 방식으로 `f.deallocates(x)` 조건이 붙습니다. 그래서 fip 함수는 `#[verifier::fip]`을
붙인 클로저(그 `call_deallocates`는 `false`)를 부를 수 있고, 호출하는 쪽이 조건이 거짓임을 보이는 제네릭 `f`도
부를 수 있습니다.

```rust
#[verifier::fip]
fn apply<F: Fn(u64) -> u64>(f: &F, x: u64) -> (r: u64)
    requires
        f.requires((x,)),
        !(*f).deallocates(x),
    allocates
        (*f).allocations(x),
{
    f(x)
}

#[verifier::fip]
fn halve_seven() -> (r: u64) {
    let half = #[verifier::fip] |y: u64| -> (r: u64) { y / 2 };
    apply(&half, 7)
}
```

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

### bound 명세: `T: Tr with { .. }`

함수의 타입 매개변수에서 마커 trait 대신 bound의 메서드 명세를 직접 적을 수 있습니다:

```rust
fn dup<T: Clone with { fn clone(&self) -> Self allocates 0; fn drop allocates 0; }>(x: &T) -> (r: (T, T))
    allocates 0
{
    (x.clone(), x.clone())
}
```

함수 안에서는 그 메서드를 부르면 bound의 명세를 씁니다. 호출자는 `T`를 인스턴스화한 타입이 그 명세를
만족함을 보여야 합니다. 메서드 명세에는 `requires`(impl이 받아들여야 함), `ensures`(impl이 보장해야 함),
`allocates`를 쓸 수 있습니다. `fn drop allocates 0;`은 `T`를 drop해도 할당하지 않는다는 뜻이고, Verus가
인스턴스의 drop glue로 확인하므로 `T`를 인스턴스화하는 타입에는 `AllocFreeDrop` impl이 필요 없습니다. 이 블록은
`requires`(`call_requires`, `call_ensures`, `call_allocations`)로 풀립니다. 함수의 타입 매개변수 말고도
`where` 절(`where T: Clone with { .. }`, 매개변수가 아닌 타입에도), inherent impl 블록(그 안의 모든 exec·proof
메서드가 받음), struct의 타입 매개변수(같은 `verus!` 블록에 있는 그 struct의 모든 inherent impl 블록이,
매개변수를 인스턴스화한 타입에 대해 받음)에 쓸 수 있습니다. trait impl에서는 메서드가 `requires`를 가질 수
없으므로 거부됩니다.

## 해제 상한: `deallocates`

`deallocates d`는 `allocates`가 할당 횟수를 제한하듯이, exec 함수가 정상적으로 반환할 때까지 하는 해제 횟수를 제한합니다.
`allocates` 다음에 씁니다.

```rust
fn drop_two(v: &mut Pool, a: Slot, b: Slot)
    allocates 0
    deallocates 2
{
    v.free(a);
    v.free(b);
}
```

* 해제 한 번은 프로그램이 블록 하나를 놓는 것입니다. `Allocator::deallocate`는 1, `grow`/`grow_zeroed`/`shrink`는 많아야
  1(블록을 옮길 수 있음), `vstd::raw_ptr::deallocate`는 1, `encapsulates alloc(a, d)`가 붙은 함수는 `d`입니다.
  `#[verifier::fip]` 함수는 `deallocates 0`이고 `deallocates`를 적을 수 없습니다. 그 밖의 피호출자는 `deallocates` 상한이
  있어야 합니다. 상한이 있는 함수는 상한이 없는 함수를 부를 수 없습니다.
* 본문은 `allocates`처럼 검사합니다. ghost 계수기를 두고, 정상 반환 지점마다 (진입 시점에 평가한) 상한과 비교합니다.
  `deallocated()`가 그 계수기이며 루프 불변식에 씁니다.
* `deallocates deallocates_when(d, c)`는 상한 `if c { d } else { 0 }`이고, 그 함수의 `call_deallocates`는 `c`입니다.
  `allocates allocates_when(a, c)`는 할당 쪽의 같은 형태입니다. 조건 없는 상한 `d`에서는 `call_deallocates`가 `d > 0`입니다.
* trait 메서드 선언의 상한은 모든 구현의 계약입니다. 구현의 본문은 그 상한으로 세고, 자기 상한을 적은 구현은 그 안에 있어야
  합니다(진입 시점에 검사).
* `call_deallocations(f, args)` / `f.deallocations(x)`는 함수 값의 상한입니다("콜백, 클로저, trait" 참고).
* 암묵적 drop도 셉니다. 컴파일러가 값을 drop하는 곳에서는 값 가운데 아직 남아 있는(옮겨지지 않은) 부분의
  `vstd::alloc_check::drop_deallocations(v)`를 셉니다. 그런 곳은 이렇습니다.
  - 지역 변수의 스코프가 끝나는 곳. 스코프를 떠나는 모든 경로가 해당합니다(블록 끝, `return`, `break`, `continue`, `?`).
  - 임시값이 속한 문장의 끝.
  - 대입이 덮어쓰는 자리의 원래 값.

  일부 경로에서만 옮겨진 값은 나머지 경로에서만 셉니다(ghost drop flag). 그래서
  `match o { Some(b) => consume(b), None => {} }`는 `o`에 대해 아무것도 세지 않습니다. `match`나 `if let`의 대상도
  마찬가지입니다(`if let Some(x) = v.pop() { .. }`, `while let Some(x) = it.next() { .. }`). 본문에서 값을 drop하는
  루프는 불변식에 `deallocated()`가 있어야 합니다.
* `drop_deallocations`는 타입마다 이렇습니다.
  - 정확한 값:
    - `Box`: 내용물, 그다음 블록 1. 크기 0인 `T`에서는 블록이 0입니다.
    - `Vec`: 원소들, 그다음 버퍼가 있으면 1(`vec_has_buffer`).
    - 배열, `Option`, `Result`, 튜플: 구성 요소들의 합.
  - 상한:
    - `String`: 많아야 1.
    - `VecDeque`: 많아야 원소들 + 1.
    - `Rc`와 `Arc`: 많아야 1 + 내용물. 마지막 참조일 때만 해제합니다.
    - `HashMap`과 `HashSet`: 키·값·해시 함수가 해제할 수 없을 때 많아야 1.
  - 0: `Copy` 타입, `NoDeallocDrop` 타입(`Global`과 `System` 포함).
  - 컨테이너에 대한 위 사실은 drop이 해제할 수 없는 할당기에서만 성립합니다. `Box<A>`·`Rc<A>`·`Arc<A>`도 `Allocator`를
    구현하지만, 이것들을 drop하면 블록이 해제됩니다.
  - 그 밖의 타입(타입 매개변수, 사용자 구조체)에는 정의가 없습니다. 필요한 것을 직접 적거나(예: `deallocates
    drop_deallocations(x)`), 타입 매개변수에 `NoDeallocDrop` bound를 겁니다.
* `drop(x)`(`core::mem::drop`)는 스코프 끝과 같이 `drop_deallocations(x)`로 셉니다.
* Verus는 컴파일된 프로그램에서, 해제할 수 있는 drop이 모두 자기가 센 것인지 검사하고 아니면 거부합니다. 지금 거부하는
  것은 이렇습니다.
  - `&&`나 `||`의 피연산자 안의 임시값. `let`의 초기화 식이 빌려서 블록 끝까지 살아 있는 임시값(`let r = &f();`,
    그리고 블록 꼬리 `{ &f() }`, `if`나 `match`의 갈래, 리터럴의 필드 `(&f(), 1)`, `Some(&f())`를 거친 경우).
    (rustc처럼 Verus도 임시값을 문장의 끝에서 drop합니다. if의 조건이나 갈래, 루프의 조건이나 본문(반복마다),
    match의 팔이나 guard 안에 있으면 그 끝에서 drop합니다. Rust 2024에서는(rustc처럼 코드의 edition으로 정합니다)
    블록 꼬리 식의 임시값을 그 식의 끝에서, 블록의 지역 변수보다 먼저 drop하고, `if let`의 대상은 then 갈래의 끝이나
    else 갈래 직전에 drop합니다. 그래서 edition이 중요합니다. 크레이트의 edition을 넘기십시오(`--edition 2024`.
    없으면 Rust 2021로 컴파일하고, `-V alloc-check`에서는 경고합니다).)
  - 내용물을 꺼낸 `Box`.
  - 캡처한 값을 읽기만 하는 `move` 클로저.
  - 대안마다 값의 다른 부분을 옮기는 or-패턴(예: `(true, x, _) | (false, _, x)`). enum의 서로 다른 variant끼리의
    대안은 괜찮습니다.
  - `deallocates` 상한이 있는 async 함수.
  - 인덱싱을 거친 원소 대입(`v[i] = x`). `let r = &mut v[i]; *r = x;`나 `v.set(i, x)`로 씁니다.

  값을 지역 변수에 묶거나 옮기면 됩니다.
* 클로저에도 `deallocates` 상한을 붙일 수 있고, 같은 방식으로 셉니다(자기 drop 포함). 그 클로저를 부르면 그
  `call_deallocations`를 셉니다. `#[verifier::fip]` 클로저는 해제하지 않으므로 `deallocates`를 적을 수 없습니다.
* 클로저를 drop하면 클로저가 소유한 것이 drop됩니다. drop glue가 없는 클로저(아무것도 캡처하지 않거나 참조와
  `Copy` 값만 캡처한 클로저)의 `drop_deallocations`는 0이고, 함수 항목은 늘 0입니다. rustc가 `Copy`로 판정한
  클로저 타입(제네릭 함수에서는 그 함수의 경계 아래에서)과 함수 항목은 Verus에서도 `Copy`이므로, `Copy`를 경계로
  하는 impl이 그것을 담은 값에 적용됩니다(`unsafe impl<C: Copy> NoDeallocDrop for W<C> {}`이면 `W { f: c }`는 drop될 때
  해제하지 않습니다). 클로저를 값으로 받는 함수는
  그것을 drop할 수 있습니다. 그런 std 함수(`Option::map`, `and_then`, `ok_or_else`, `unwrap_or_else`,
  `Result::map`, `map_err`, `bool::then`, `cmp::min_by`, `max_by`, `Box::map` 등)의 vstd 명세는 호출과 함께
  `drop_deallocations(f)`를 세고, `F: FnOnce(..)`인 `f: F`에 대한 `f(x)`도 그렇습니다(종류가 `Fn`인 클로저를
  `FnOnce`로 부르면 본문을 실행한 뒤 자기 자신을 drop합니다). drop하면 해제될 수 있는 값을 소유한 클로저(`Box`를
  캡처한 `move` 클로저)의 drop은 아직 정의되지 않았습니다. 대신 참조로 캡처하십시오. (종류가 `FnOnce`인
  클로저를 `f(x)`로 부르면, 본문이 자기가 소유한 것을 drop하는데도 그 drop을 한 번 더 셉니다. 실제보다 많이 셉니다.)
* 이전 형태 `allocates deallocates_when(n, c)`(횟수 없는 조건)는 더는 받지 않습니다.
  `allocates n deallocates deallocates_when(d, c)`로 씁니다.
* std 함수에 대한 vstd 명세는 해제를 적습니다. 메모리를 놓을 수 있는 함수는 횟수로 적습니다(`Vec::push`는 기존 버퍼를
  키울 때 1, `String::push_str`은 1, `Vec::clear`와 `truncate`는 지운 원소들의 drop, 사용자 코드를 부르는 비교나
  `clone`은 그 호출들이 해제하는 만큼). 받은 값을 drop하는 함수는 `vstd::alloc_check::drop_deallocations(v)`를 셉니다
  (`Option::unwrap_or`는 옵션이 `Some`이면 `default`를, `Option::insert`는 원래 내용을 drop합니다). 값들의 열에는
  `seq_drop_deallocations(s)`를 씁니다(`drop_deallocations`는 위 항목 참고).
* 몇몇 명세는 상한을 적지 않습니다. vstd가 아직 해제 횟수를 이름 붙일 수 없는 사용자 코드를 부르기 때문입니다. 키를
  해시하는 `HashMap`·`HashSet` 연산(`insert`, `get`, `remove`, `contains_key`, `entry`, `reserve` 등), `to_string`,
  `format!`과 `Formatter::write_fmt`, `Vec::from_fn`입니다. 이런 함수는 `deallocates` 상한이 있는 함수(그리고 fip
  함수)에서 부를 수 없습니다.
* `Iterator::next`(그래서 `for` 루프)의 상한은 `iter_next_deallocations(&*self)`입니다. `iter_next_cost`처럼 구현마다
  정해지는 항입니다. vstd는 `next`가 아무것도 해제하지 않는 std 반복자에 대해 이 값을 0으로 둡니다. std 정수의
  범위(`0..n`, `0..=n`), slice의 반복자(`iter()`, `iter_mut()`, `chunks`, 따라서 `&Vec`), `VecDeque`·`HashMap`·
  `HashSet`·`BTreeMap`·`BTreeSet`의 빌려 쓰는 반복자, `Chars`, `vec::IntoIter`입니다. `allocates`와 마찬가지로 루프는
  불변식에 카운터를 적어야 합니다(`invariant deallocated() == 0`, fip 함수에서는 `invariant allocated() == 0`).
  값을 소유하는 반복자를 도는 루프(`Vec`인 `v`에 대한 `for x in v`)는 여전히 거부합니다. 반복자를 drop할 때 버퍼가
  해제되는데, 이것은 아직 세지 못합니다. `-V alloc-check`에서는 검증되는 `impl Iterator`도 이 상한에 맞춰 셉니다.
  그 `next`는 아무것도 해제하지 않아야 하고, 해제한다면 공리로 `iter_next_deallocations`를 적어야 합니다.

## 완전한 제자리 함수: `#[verifier::fip]`

FP² 논문(Lorenzen·Leijen·Swierstra, ICFP 2023)은 제자리에서 실행되는 함수를 구분합니다. 그 용어로
말하면 `allocates n` 상한은 `fbip(n)`의 힙 부분입니다. 할당은 최대 `n`번이고 해제는 몇 번이든
됩니다. `#[verifier::fip]`는 `fip(n)`입니다. 이 함수는 정상 반환할 때 메모리를 전혀 해제하지 않습니다.
`allocates` 상한이 없으면 `fip`이고, 할당도 하지 않는다는 뜻입니다(`allocates 0`). 이 속성에는
`-V alloc-check`가 필요하며, 한 함수에는 `#[verifier::fip]`와 `#[verifier::fip(strict)]` 중 하나만 붙일 수 있습니다.

이 속성은 일부를 검증이, 일부를 컴파일된 프로그램이 검사합니다. 그래서 둘이 같은 함수와 클로저에서 같은 종류로
이 속성을 봐야 합니다. 한쪽만 보는 속성은 오류입니다. (crate 자신의 소스에서는 이렇게 만드는 방법들을
거부합니다. "상한 검사" 참고. 다른 crate의 매크로는 여전히 만들 수 있습니다.)

`-V alloc-check`에서는 Verus가 검증하지 않는 함수나 클로저에 이 속성을 붙이면 오류입니다. `#[verus_spec]` 없이
`verus!` 밖에 있거나, `#[verifier::external]`이 붙었거나, external·`external_body` 항목 안에 있는 경우입니다. 함수가
아닌 항목(struct, impl, `const` 등)에 붙이면 언제나 오류입니다.

```rust
pub struct Node { pub val: u64, pub next: Option<Box<Node>> }

#[verifier::fip]
fn halve(mut b: Box<Node>) -> (r: Box<Node>) {
    b.val = b.val / 2;
    b
}

#[verifier::fip]
fn push_spare(v: &mut Vec<u64>)
    requires
        old(v)@.len() < spec_vec_capacity(&*old(v)),
{
    v.push(1);
}
```

두 가지를 검사합니다.

* **호출.** callee가 그 자체로 `#[verifier::fip]`이거나 해제 조건을 가져야 하고, 호출자는 그 조건이
  거짓임을 보여야 합니다. 조건은 `deallocates d`에서는 `d > 0`, `deallocates deallocates_when(d, c)`에서는 `c`입니다
  (진입 시점에 평가, "해제 상한" 참고). 예를 들어 `Vec::push`는 기존 버퍼를 키워야 할 때 해제할 수 있습니다. 키우는 것은
  재할당이고, 재할당은 옛 블록을 해제하기 때문입니다. 버퍼가 없는 벡터는 할당기의 `allocate`만 불러서
  키웁니다. 어떤 할당기든 `allocate`는 해제하지 않습니다("사용자 정의 할당기" 참고). 기본 본문이 없는 trait
  메서드 선언도 상한이나 조건을 적을 수 있고, 그러면 모든 구현이 지켜야 하는 계약이 됩니다. 검증된 본문이 있는 구현은
  그 상한으로 셉니다. 본문이 없는 구현(`external_body`, `assume_specification`)은 선언의 것을 따르며 자기 것을 따로 적을
  수 없습니다. 할당기 런타임의 코드는 예외입니다(`Allocator::allocate`는 `deallocates 0`으로 선언되어 있습니다).
 Verus가 검사하지 않는 구현이나 `-V alloc-check`로 검증하지
  않은 crate의 구현은 거부합니다.
  impl로 해석되지 않는 trait 메서드 호출(제네릭 호출)은 그 메서드의 선언이 `#[verifier::fip]`이거나, 선언의
  조건이 거짓임을 호출하는 쪽이 보이거나, 연산자 trait의 메서드를 그 표시 trait을 통해 부를
  때만 허용합니다(아래 "연산자 trait" 참고). 선언에 붙은 이 속성은
  계약입니다. 그 메서드의 모든 구현도 `#[verifier::fip]`여야 하고(strict 선언이면
  `#[verifier::fip(strict)]`) 그래야 구현의 호출과 drop이 검사됩니다. Verus가 검사하지 않는 구현은
  거부합니다(`allocates` 상한이 있는 선언과 같습니다). 기본 본문은 선언된 곳에서 검사합니다. 함수 값의
  호출(클로저, 또는 `F: Fn(..)`인 `f: F`에 대한 `f(x)`)에는 `f.deallocates(x)`(`call_deallocates`) 조건이
  붙고, 호출하는 쪽이 그것이 거짓임을 보여야 합니다. 클로저 식에 `#[verifier::fip]`(또는
  `#[verifier::fip(strict)]`)을 붙인 클로저가 그렇습니다. 그 본문은 fip 함수처럼 검사하며, 상한이 없으면
  할당도 하지 않습니다. 제네릭 함수는 이것을 `requires !f.deallocates(x)`로 요구할 수 있습니다. (strict 함수는
  연산자 trait의 strict 표시 trait을 통해서만 제네릭 호출을 할 수 있습니다. 그 밖에는 호출 대상의 스택 사용을
  알 수 없기 때문입니다. 알고 있는 strict 클로저는 부를 수 있습니다.) std, vstd, 다른 crate의 함수 호출은 그 함수가 이
  crate의 어떤 함수를 되부를 수 있는지도 MIR에서 검사합니다(아래 "다른 crate에서 오는 콜백" 참고). 이런 호출에는
  drop하면 해제될 수 있는 클로저(예: `Box`를 소유한 클로저)를 값으로 넘길 수 없습니다. std가 그 클로저를 drop할 수
  있기 때문입니다. 특히 종류가 `Fn`이나 `FnMut`인 클로저(먼저 지역 변수에 묶은 클로저)를 `Option::map`처럼
  `FnOnce`로 부르면, 컴파일러가 만든 shim이 본문을 부른 뒤 클로저의 환경을 drop합니다. 이 drop은 클로저의 검사도
  상한도 다루지 않습니다. 대신 참조로 캡처하십시오.
* **drop.** 컴파일러는 소스에 나타나지 않는 drop을 넣습니다. 이 drop은 컴파일되는 프로그램의 MIR에서
  검사합니다. ghost 코드를 지우고 drop elaboration을 마친 뒤의 MIR입니다. 정상 반환하는 경로에서
  drop되는 값은 타입에 drop glue가 아예 없거나, unsafe 표시 trait `vstd::alloc_check::NoDeallocDrop`을
  구현해야 합니다. 제네릭 타입에는 `T: NoDeallocDrop` bound가 필요합니다. `Box` 안의 내용을 밖으로
  move하면 그 `Box`가 해제됩니다. 제자리에 머무르려면 대신 `Box`를 재사용하세요(`*b = ..`, 또는
  필드 갱신).

`core::mem::forget`은 해제하지 않으므로, fip 함수는 자신이 가진 값을 forget할 수 있습니다. 그러면 그
값의 메모리가 샙니다. FP²의 선형 규율과 달리 `#[verifier::fip]`는 아무것도 해제하지 않는다는 뜻일 뿐,
가진 모든 셀을 재사용한다는 뜻은 아닙니다.

`unsafe impl NoDeallocDrop for X`는 다음 조건을 모두 만족할 때만 받습니다. `X`가 `Box`가 아니고,
`X` 자신의 `Drop`이 있다면 그것이 `#[verifier::fip]`이며, 각 필드가 drop glue가 없거나 `NoDeallocDrop`이어야
합니다. 이 crate의 impl은 컴파일할 때 검사합니다. 다른 crate의 impl은 그 crate가 `-V alloc-check`로
검증·컴파일되어 라이브러리 파일과 함께 import된 경우에만 받고(그 컴파일이 검사했으므로), 그렇지 않으면
거부합니다.

컨테이너는 std 코드 안에서 할당기의 메서드를 부릅니다. 그 메서드는 런타임의 것이므로("사용자 정의 할당기"
참고), fip 함수와 strict 함수는 어떤 할당기로든 std나 vstd 코드를 쓸 수 있습니다(`Vec<u8, A>::push`,
`Vec::with_capacity_in(n, a)`). 할당기 자신의 코드는 말단으로 보며, 해제 검사도 스택 검사도 따라가지
않습니다.

`allocates`와 마찬가지로 unwind하는 경로는 다루지 않습니다. drop 검사는 Verus의 컴파일 단계에서
돌기 때문에, `--no-lifetime`과 `--no-erasure-check`는 `#[verifier::fip]` 함수를 거부합니다.

### 스택 공간 상수: `#[verifier::fip(strict)]`

FP²의 `fip`은 스택 공간 상수도 요구합니다. `#[verifier::fip(strict)]`는 `#[verifier::fip]`에 이 조건을
더합니다. Rust는 꼬리 위치의 호출이 호출자의 frame을 대체한다고 보장하지 않습니다. `opt-level=0`에서는
대체하지 않고, 호출 뒤에 남은 drop이 있을 때도 대체하지 않습니다. 그래서 엄격한 함수는
`become`(`#![feature(explicit_tail_calls)]`)으로만 재귀합니다. rustc는 `become` 호출이 frame을
대체한다고 보장하거나, 그렇게 할 수 없으면 프로그램을 거부합니다.

```rust
#[verifier::fip(strict)]
fn sum(n: u64, acc: u64) -> (r: u64)
    decreases n
{
    if n == 0 { acc } else { become sum(n - 1, acc.wrapping_add(n)) }
}
```

엄격한 함수의 호출은 컴파일되는 프로그램의 MIR에서, drop elaboration 뒤에 검사합니다. 그 함수의 drop이
실행하는 소멸자도 포함합니다.

* 호출 대상은 다른 엄격한 함수이거나 std나 vstd의 함수일 수 있습니다. 다른 crate의 함수는 엄격한 함수이고,
  그 crate가 `-V alloc-check`로 검증·컴파일되어 라이브러리 파일과 함께 import된 경우에만 부를 수 있습니다
  (`become`의 대상으로도). 그 컴파일이 그 함수와, 그 crate 안에서 거기서 닿는 모든 함수를 검사했습니다
  ("라이브러리와 다른 crate" 참고). 이런 함수는 호출이 인스턴스화한 타입의 trait bound를 통해서만 이
  crate의 코드에 닿습니다. 그 콜백은 따라가서 꼬리 호출이 아닌 호출로 칩니다(아래 "다른 crate에서 오는
  콜백" 참고). 사용자 할당기의 메서드는 예외입니다. 사용자 할당기(`A: FipStrictAllocator`, 엄격한
  메서드가 이 crate에 있음)로 인스턴스화한 호출은 사용자 할당기를 쓰는 것으로 치므로, 할당기의 메서드가
  거기에 닿을 수 없습니다(아래). 그 밖의 다른 crate 함수 호출과 callee를 알 수 없는 호출(함수 값, 그리고
  `FipStrictOp`를 통한 연산자 trait 메서드 호출이 아닌 제네릭 호출)은 거부합니다.
* 소멸자도 호출로 칩니다. 그 함수의 drop이 실행하는 소멸자와, std나 vstd 호출이 인스턴스화된 타입의
  소멸자(std는 `Vec::<T>::clear`처럼 호출 안에서 그런 값을 drop할 수 있습니다)입니다. 다른 crate 타입의
  소멸자는 그 crate의 함수와 같은 조건(`-V alloc-check`로 검증·컴파일된 crate의 엄격한 `Drop::drop`)일 때 받고,
  그렇지 않으면 거부합니다. 타입 매개변수,
  associated 타입이나 불투명 타입, `dyn`이 관련되어 소멸자를 여기서 알 수 없는 drop(또는 그런 호출)은
  거부합니다. `Copy` bound가 있으면 소멸자가 없습니다.
* vstd 명세에 `#[verifier::alloc_check_skip_drops]`가 붙은 std 함수는 타입 인자의 값을 drop하지
  않습니다. 그래서 그 호출은 타입 인자의 소멸자를 실행하지 않고, bound와 상관없이 타입 매개변수로
  인스턴스화해도 됩니다. 대상은 `mem::swap`, `mem::replace`, slice 뷰(`len`, `first`, `last`, `get`,
  `get_unchecked`, 인덱싱, `swap`, `split_at`, `split_first`, `split_last`와 그 `_mut`, `_checked`,
  `_unchecked` 변형), 그리고 `Vec`의 `new`, `new_in`, `len`, `capacity`, `is_empty`, `pop`, `remove`,
  `swap_remove`, `as_slice`, `as_mut_slice`, `deref`, `deref_mut`, 인덱싱, 그리고 아래 "연산자 trait"에
  나오는 비교 함수들(`<[T]>::contains`, `sort_unstable`, `Option`의 비교 등)입니다. `mem::take`는
  `T::default`를 실행하므로 빠집니다. 이 표시는 `external_body`처럼 신뢰하는 것이고, vstd에서만 받습니다.
  `-V alloc-check`의 drop 규칙도 이 표시에 기댑니다. 이런 함수에 어떤 값의 `&mut`를 넘기는 호출은 그 값이
  담은 것을 drop하는 것으로 치지 않습니다.
* 엄격한 함수들 사이의 호출 순환은 `become` 호출로만 이루어져야 합니다. 꼬리가 아닌 호출은 frame을
  하나 더하므로, 그런 호출을 거치는 순환은 스택을 키웁니다.

`-V fip-lint`(`-V alloc-check` 없이도 씀)는 스택을 키우는 재귀를 경고하고, 피하는 방법을 제안합니다.

* 꼬리 위치에 있지만 꼬리 호출이 아닌 재귀 호출. 경고는 호출 뒤에 남은 drop이 있는지, 그리고
  시그니처가 `become`을 허용하는지도 알려 줍니다.
* `List::Cons(n, Box::new(range(n - 1)))`처럼 생성자 안의 재귀(TRMC). 그 결과가 반환되는 값의 필드가
  되므로 이 호출은 꼬리 호출이 아닙니다. 루프로 같은 값을 스택 공간 상수로 만들 수 있습니다. 루프는
  `&mut` 구멍(아직 채우지 않은 필드)을 들고 있다가, 새 값을 만들 때마다 그 구멍에 넣고, 구멍을 새 값의
  필드로 옮깁니다. 이것이 destination-passing 방식이며, Leijen·Lorenzen의 "Tail Recursion Modulo
  Context"에 나오는 방식입니다.

생성자 안의 재귀에는 루프로 바꾸는 재작성이 경고에 suggestion으로 붙습니다. 편집기(verus-analyzer)는
이것을 quick fix로 보여 줍니다. `-V fip-lint=fix`는 대신 재작성을 소스 파일에 씁니다. 재작성은 crate가
여전히 검증될 때만 남습니다. 검증이 성공한 뒤 Verus는 재작성을 하나씩 쓰고 crate를 다시 검증하며,
실패하면 파일을 되돌립니다. 따라서 재작성에 대해 신뢰하는 것은 없습니다. 그래서 `=fix`는 crate의 일부만
검증하거나 검사를 건너뛰는 옵션(`--no-verify`, `--verify-root`, `--verify-module`, `--verify-only-module`,
`--verify-function`, `--no-lifetime`, `--no-erasure-check`, `--no-trait-conflicts`, `-V allow-inline-air`,
`-V ignore-unexpected-smt`)과 함께 쓸 수 없습니다. 각 시도는 검증만 하고(`--export`, `--compile`, `-o`,
`--out-dir`, `--emit` 없이), 재작성이 남으면 모든 옵션으로 한 번 더 실행하므로 산출물은 재작성된 파일을
반영합니다. 파일은 그 자리에서 고쳐 씁니다. 심볼릭 링크를 따라가며, 하드 링크와 파일 권한은 그대로
둡니다. 쓸 수 없는 파일, byte-order mark나 CRLF 줄끝이 있는 파일은 건드리지 않습니다. 실행하는 동안 원본은
`<file>.fip-lint-orig`(링크라면 링크가 가리키는 파일 옆)에 보관되고, crate 루트 옆의 저널
`.fip-lint-journal`에 기록됩니다. SIGINT, SIGTERM, SIGHUP을 받으면 원본을 복원합니다. 프로세스가 강제로
죽으면 백업과 저널이 남고, 다음 `=fix` 실행은 이를 복원하거나 지울 때까지 시작하지 않으며 백업 목록(crate
루트 디렉터리 밖 파일의 백업 포함)을 보여 줍니다. 저널은 한 crate에 대한 `=fix` 실행 둘이 겹치지 않게도
합니다. 다른 도구(편집기, `cargo build`)는 실행 중인 시도를 볼 수 있습니다.

재작성은 호출 그래프의 강하게 연결된 성분(SCC) 단위로 이루어지므로 상호 재귀도 재작성됩니다. 성분 안의
모든 재귀 호출은 꼬리 호출이거나, 꼬리 위치에 있는 생성자 안의 유일한 재귀 호출이어야 합니다(`Box::new`나
중첩된 생성자를 거쳐도 됩니다).

* 함수가 하나이면 그 함수 본문 안의 루프가 됩니다.
* 함수가 여럿이면 새 helper 함수 하나의 루프를 함께 씁니다. 루프의 상태는 함수마다 variant가 하나씩 있는
  enum이며, 각 variant는 그 함수의 인자와 구멍을 담습니다. 그래서 함수들의 반환 타입이 달라도 됩니다.
  각 함수는 자기 상태에서 루프를 시작합니다.

재작성한 코드는 생성자의 필드와 호출의 인자를 원래 코드와 같은 순서로 평가합니다. 재귀 호출 뒤에 오는
필드는 원래 코드에서는 호출이 돌아온 뒤에, 루프에서는 다음 반복 전에 평가되므로, 그런 필드가 리터럴이나
이름일 때만 재작성을 제안합니다. 마찬가지로 drop이 사용자 코드를 실행하는 값(std 밖의 `Drop` impl, 또는 타입
매개변수)은 루프에서 다른 시점에 drop되므로, 그런 타입의 바인딩이나 식(임시값: `match` 대상, 인자)이 있는
함수는 재작성하지 않습니다. 루프 불변식은 두 가지를
말합니다.

* 구멍의 최종 값(`*final(hole)`)이 현재 인자에 대한 `ensures`를 만족하면, 결과는 원래 인자에 대한
  `ensures`를 만족합니다.
* `allocates`가 있으면, 지금까지의 할당 수와 현재 인자에 대한 상한을 더한 값이 원래 상한을 넘지 않습니다.

구멍에 값을 쓸 때는 `core::mem::forget(core::mem::replace(hole, value))`를 씁니다. 바뀌는 값은
자리표시자(필드 없는 variant)이므로 forget해도 새는 것이 없고, `#[verifier::fip]` 함수는 그대로
`#[verifier::fip]`입니다. 재작성한 뒤에는 함수에 `#[verifier::fip(strict)]`를 붙일 수 있습니다.
테스트 `fip_trmc_fix_*`는 깊이 10^6에서 스택이 넘치는 재귀를 재작성하고, 그 결과를 `opt-level=0`과
`3`에서 실행합니다.

다음 경우에는 재작성을 제안하지 않으며, 경고가 그 이유를 알려 줍니다.

* 함수가 자유 함수가 아닌 경우(예: 메서드)
* 매개변수가 `&mut`, ghost, tracked이거나, 이름이 아닌 패턴인 경우
* 본문이 매개변수 이름을 다시 바인딩하는 경우(`let mut k = k + 1;`): 루프는 매개변수에 이름으로 대입합니다.
  이름으로 판단하므로 해가 없는 바인딩도 걸립니다(같은 이름을 바인딩하는 `match` arm, 매크로 안의 같은
  이름의 지역 변수)
* 함수의 소스에 `__trmc`로 시작하는 이름이 나오는 경우: 재작성이 자기 이름으로 씁니다
* 함수가 매크로 확장에서 나온 경우
* 재귀 호출 뒤의 생성자 필드가 리터럴이나 이름이 아니거나, 바인딩이나 임시값의 drop이 사용자 코드를
  실행하는 경우(위 참고). 재귀 호출이 돌아올 때 그 타입의 값이 남아 있지 않더라도 타입 매개변수의 값은
  여기에 해당합니다(`fn f<T>(l: G<T>)`)
* 함수에 `decreases`가 없거나(루프의 `decreases`가 됩니다), `returns`를 쓰거나, `?`로 일찍 반환하는 경우
* 반환 타입이 필드 없는 variant를 가진 enum이 아닌 경우
* 함수가 여럿일 때, 제네릭 매개변수가 서로 다르거나, `decreases` 식이 함수마다 둘 이상이거나, 모두가
  `allocates`를 갖지는 않은 경우

### 연산자 trait: `FipAdd`, `FipOrd` 등

trait 메서드의 제네릭 호출은 impl을 알 수 없습니다. 그래서 `-V alloc-check`는 호출자 자신의 상한
(`call_allocations`)으로만 그 호출을 제한할 수 있고, fip 함수는 그 호출을 아예 할 수 없습니다. `core`의
연산자 trait에 대해서는 vstd가 unsafe 표시 trait을 제공합니다. 표시 trait은 어떤 타입의 그 trait impl이
무엇을 하는지 말합니다. 연산자 trait `Op`마다 셋이 있고, 각각 다음 것의 상위 trait입니다.

| 표시 trait | `X`의 `Op` impl의 메서드 | `T: 표시 trait`을 통한 제네릭 호출 |
|---|---|---|
| `FbipOp` | `allocates 0`로 제한됨 | 0으로 셈 |
| `FipOp` | 또한 `#[verifier::fip]` | `#[verifier::fip]` 함수에서 할 수 있음 |
| `FipStrictOp` | 또한 `#[verifier::fip(strict)]` | `#[verifier::fip(strict)]` 함수에서 할 수 있음 |

`Op`는 vstd가 명세하는 trait 가운데 하나입니다. `Neg`, `Not`, `Add`, `Sub`, `Mul`, `Div`, `Rem`, `BitAnd`,
`BitOr`, `BitXor`, `Shl`, `Shr`, 이들의 `*Assign` 꼴, `Index`, `IndexMut`, `Deref`, `DerefMut`, `PartialEq`,
`PartialOrd`, `Ord`, `Clone`, `From`, `Into`입니다. 표시 trait은 원래 trait의 타입 매개변수를 가지고(`FipAdd<Rhs = Self>`,
`FipIndex<Idx>`), 원래 trait의 상위 trait을 따릅니다. `FipOrd`는 `FipPartialOrd`와 `FipPartialEq`를,
`FipIndexMut`는 `FipIndex`를 함축합니다.

```rust
use vstd::alloc_check::{FipOrd, FipStrictPartialEq};

#[verifier::fip]
fn lt_gen<T: FipOrd>(a: &T, b: &T) -> bool {
    a < b
}

#[verifier::fip(strict)]
fn eq_gen<T: FipStrictPartialEq>(a: &T, b: &T) -> bool {
    a == b
}
```

참조끼리의 비교(`a: &T`일 때 `a == b`)는 참조에 대한 std의 impl을 거쳐 `T`의 메서드를 부릅니다. 그래서
`T`의 표시 trait이 이 비교도 다룹니다.

vstd는 기본 정수 타입, `bool`, `char`에 대해 (그 타입이 구현하는 trait의) 표시 trait을 구현하고, `Clone`의
표시 trait은 `f32`, `f64`에도, `From`의 표시 trait은 인자를 그대로 돌려주는 `From<T> for T`에도 구현합니다. 이
impl은 신뢰합니다. 그 밖의 `unsafe impl FbipOp for X`(또는 `FipOp`, `FipStrictOp`)는 다음일 때만 받습니다. 같은
타입을 같은 꼴로 적은 `X`의 `Op` impl을 Verus가 검사하고, 그 impl이 정의하는 메서드마다 `allocates 0`
(리터럴 `0`)로 제한되어 있고, 위 단계에서는 `#[verifier::fip]`이나 `#[verifier::fip(strict)]`이어야 합니다.
impl이 정의하지 않은 메서드는 `core`가 제공하는 본문을 실행하고, 그 본문은 trait 자신의 메서드만
부릅니다. 파생 impl(`#[derive(PartialEq)]`)은 받지 않습니다. 다만 파생 `clone`은 Verus가 `allocates 0`과
어떤 단계의 속성을 붙여 검사하므로, 그 단계까지의 표시 trait을 받습니다.

* 본문이 `*self`이면(타입 매개변수가 없는 타입에 `#[derive(Clone, Copy)]`) `#[verifier::fip(strict)]`입니다
  (`ensures r == *self`도 그대로).
* struct의 것이고 필드마다 clone하면, 그 단계는 impl이 있는 곳에서 필드 타입들이 가진 `Clone` 표시 trait 중
  가장 낮은 것입니다(타입 매개변수에는 타입 자신의 bound로 표시 trait을 주어야 합니다. `#[derive(Clone)]`이
  그 bound를 impl에 옮깁니다). 필드 타입에 타입 매개변수가 있으면 많아야 `#[verifier::fip]`입니다. 엄격한 스택
  검사는 그런 호출(표시 trait을 거치는 호출)이 이 `clone`을 포함해 crate의 어느 엄격한 `clone`에든 닿을 수 있다고
  보기 때문입니다. 표시 trait이 없는 필드 타입이 있으면 전처럼 할당 상한이 없습니다.

다른 표시 trait처럼, `verus!` 밖의 impl이나
`-V alloc-check`로 검증하지 않은 crate의 impl은 거부합니다.

`Ord`가 제공하는 `max`, `min`, `clamp`는 `Self`의 값을 drop합니다. 그래서 `FbipOrd`에는 `AllocFreeDrop`이,
`FipOrd`에는 `NoDeallocDrop`이 필요합니다. 그리고 엄격한 함수는 이 셋을 표시 trait을 통해 부를 수
없습니다(거기서는 타입 매개변수의 소멸자를 알 수 없기 때문입니다). `Clone`이 제공하는 `clone_from`
(`*self = source.clone()`)도 마찬가지입니다. `FbipClone`에는 `AllocFreeDrop`이, `FipClone`에는
`NoDeallocDrop`이 필요하고, 엄격한 함수는 `FipStrictClone`을 통해 `clone_from`을 부를 수 없습니다.

인자를 비교하는 std 함수는 비교가 해제할 때만 해제하고, 비교가 할당하는 만큼만 할당합니다. vstd는 이것을
표시 trait의 spec 수준 형태로 적습니다. `partial_eq_is_fip::<T, Rhs>()`, `partial_ord_is_fip::<T, Rhs>()`,
`ord_is_fip::<T>()`, `ord_is_fbip::<T>()`(각각 표시 trait이 있는 타입에 대해 참)를 `deallocates_when` 조건에
쓰고, `FbipOp` 타입의 메서드가 할당하지 않는다는 공리(`call_allocations(<T as PartialEq>::eq, ..) == 0`)를
둡니다. 그래서 fip 함수는 표시 trait이 있는 타입에 대해 이 함수들을 부를 수 있습니다.

```rust
#[verifier::fip]
fn sort_it<T: FipOrd>(v: &mut [T]) {
    v.sort_unstable();
}

#[verifier::fip]
fn has<T: FipPartialEq>(s: &[T], x: &T) -> bool {
    s.contains(x)
}
```

대상은 `<[T]>::contains`, `starts_with`, `ends_with`, `sort_unstable`, `binary_search`, `Option`의 `eq`,
`partial_cmp`, `cmp`, 참조끼리의 비교, `Range::contains`, `RangeInclusive::contains`, 그리고 `cmp::min`,
`cmp::max`입니다. (정수, `bool`, `char`의 `min`, `max`, `clamp` 메서드는 직접 `allocates 0 deallocates 0`으로
명세했습니다. `clamp`는 core가 그렇지 않으면 panic하므로 `min <= max`를 요구합니다.) 마지막 둘을 뺀 나머지는 아무것도 drop하지 않으므로(`#[verifier::alloc_check_skip_drops]`),
엄격한 함수도 `FipStrictOp`를 통해 부를 수 있습니다. (`sort_unstable`의 결과는 입력의 순열이고, `T`의 비교가
전순서이면(`vstd::laws_cmp::obeys_cmp::<T>()`) `cmp_spec`으로 정렬되어 있습니다. 그렇게 정렬된 slice에서
`binary_search`는 원소가 `Equal`로 비교되는 `i`에 대해 `Ok(i)`를 돌려주거나, `i` 앞의 원소는 모두 `Less`이고
`i`부터의 원소는 모두 `Greater`인 `Err(i)`를 돌려줍니다. 비교를 몇 번 하는지는 정해져 있지 않아서, 할당량은
타입이 `FbipOrd`가 아니면 해석되지 않는 항입니다.) vstd는 `Option<T>`와 참조에 대해서도, `T`(참조 대상)가 비교 표시 trait을 가지면
그 표시 trait을 구현합니다. 표시 trait이 없는 타입은, 비교가 fip이더라도 거짓임을 보일 수 있는
`deallocates_when`을 얻지 못합니다. 그런 타입에는 표시 trait을 주세요.

같은 방식으로, `<[T]>::to_vec`, `Box::<[T]>::from(&[T])`, `Vec::<T>::from(&[T])`(std가 `to_vec`로 쓰는
`&mut [T]`, `&[T; N]`에서의 변환도)는 한 번 할당하고(빈 slice이면 할당하지 않음)
원소마다 clone합니다. 결과는 입력과 길이가 같고 원소마다 그 clone(`cloned`)이며, 할당량은
`1 + seq_clone_allocates(..)`(빈 slice이면 0)이고, `clone`이 해제할 때만 해제합니다. 이 조건을
`deallocates_when`에 `clone_is_fip::<T>()`(`FipClone` 타입에 대해 참)로 적고, `FbipClone` 타입의 `clone`은
할당하지 않는다는 공리를 둡니다. 둘 다 정상적으로 돌아올 때 `T`를 drop하지 않으므로, 엄격한 함수도
`FipStrictClone`을 통해 부를 수 있습니다.

```rust
#[verifier::fip(strict)]
fn copy<T: Copy + AllocFreeDrop + FipStrictClone>(src: &[T]) -> (r: Vec<T>)
    requires
        forall|a: T, b: T| call_ensures(T::clone, (&a,), b) ==> a == b,
    ensures
        r@ == src@,
    allocates
        if src@.len() == 0 { 0int } else { 1int },
{
    src.to_vec()
}
```

(`r@ == src@`는 `requires`에서 나옵니다. `cloned`는 clone이거나 값 자신이기 때문입니다. `T = i32`나
`T = f64`인 호출자는 vstd의 `clone` 명세로 이 `requires`를 보입니다.)

`From`과 `Into`는 양방향으로 통합니다. std의 blanket `impl<T, U: From<T>> Into<U> for T`는 `U::from(x)`이므로,

* 이 impl을 거치는 `x.into()` 호출은, 그 `From` impl을 Verus가 알면(명세가 있거나 검증된 것이면)
  `<U as From<T>>::from(x)` 호출로 검사합니다. 그 impl의 `allocates`, `deallocates_when`, "drop하지 않음",
  `ensures`가 적용됩니다. (`Box<[T]>`나 `Vec<T>`로의 `src.into()`는 `Box::<[T]>::from(src)`나 `Vec::<T>::from(src)`가 됩니다.) 그 impl을 모르면
  `U::from`을 가리키는 blanket impl의 명세가 적용됩니다.
* `U: FipFrom<T>`이면 `T: FipInto<U>`입니다(vstd가 구현하고, `U: FbipFrom<T>` 같은 bound는 `x.into()` 호출도
  다룹니다). `From` 없이 crate가 직접 쓴 `Into` impl에도 `Into`의 표시 trait을 줄 수 있고, 다른 표시 trait처럼
  검사합니다.

```rust
#[verifier::fip(strict)]
fn conv<T: NoDeallocDrop, U: FipStrictFrom<T> + NoDeallocDrop>(t: T) -> U {
    t.into()
}
```

### 다른 crate에서 오는 콜백

std, vstd, 다른 crate의 코드는 자신을 인스턴스화한 타입의 trait bound를 통해서만 이 crate의 함수를 부를 수
있습니다. 제네릭 함수는 타입 인자의 메서드를 자신의 bound를 통해 부르기 때문입니다. Verus는 fip 함수 안의
그런 함수 호출마다, 컴파일되는 프로그램의 MIR에서 다음을 합니다. callee의 bound를 호출의 타입 인자로
인스턴스화하고, 그 상위 trait과 연관 타입의 bound를 더한 뒤, 그 bound가 고르는 impl을 찾습니다. std의
impl이면 그 impl 자신의 bound로 이어 갑니다(`Vec<L>: PartialEq`에는 `L: PartialEq`가 필요합니다). 이렇게
찾은 이 crate의 impl의 모든 함수와, `Fn` bound로 찾은 모든 클로저와 함수 항목은 되불릴 수 있습니다.

* `#[verifier::fip]` 함수에서는 `#[verifier::fip]`이어야 합니다.
* `#[verifier::fip(strict)]` 함수에서는 엄격한 함수여야 하고, 꼬리 호출이 아닌 호출로 칩니다.
* 제3의 crate의 함수는 `-V alloc-check`로 검증·컴파일된 crate의 엄격한 함수여야 합니다.
* impl을 알 수 없는 타입 매개변수의 bound는 그 trait의 연산자 표시 trait(`FipOp`, 엄격한 함수에서는
  `FipStrictOp`)을 통해서만 받습니다. 엄격한 함수에서는 그런 콜백이 이 crate에 있는, 그 trait과 상위
  trait의 impl의 모든 엄격한 메서드에 닿을 수 있다고 보고, 각각을 꼬리 호출이 아닌 호출로 칩니다.
* 그 밖의 경우(`dyn`의 bound, 함수 포인터)는 거부합니다.

`core::alloc::Allocator`의 bound는 위의 할당기 규칙에 맡깁니다. 콜백을 받는 std 함수의 호출은 대부분
검증기의 검사가 이미 거부합니다. vstd 명세에 `deallocates_when` 조건이 없기 때문입니다. 이 검사는 그것에
기대지 않고, 이 crate의 타입으로 인스턴스화한 다른 crate의 엄격한 함수도 다룹니다.

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
것을 요구합니다. 그래서 panic 경로가 존재하지 않습니다. 상한이 있는 클로저(클로저에 `allocates 0`을 주는 `#[verifier::fip]` 클로저 포함)도 `no_unwind`여야 합니다.
할당하는 std 함수(`Box::new`, `Vec::push`, ...)에 대한 vstd 명세는 `no_unwind`가 아닙니다. capacity
overflow가 unwind할 수 있는 `panic!`이기 때문입니다. 그래서 실제로는 할당하는 함수가 아직 strict 모드를
통과할 수 없습니다.

## 신뢰 기반과 한계

`-V alloc-check`가 신뢰하는 것:
* std 함수에 대한 vstd 명세의 상한, 그리고 위에서 설명한 std trait 메서드에 대한 vstd 상한의 설계
* vstd 명세의 `deallocates_when` 조건(`#[verifier::fip]`용)
* `#[verifier::fip(strict)]`의 경우: std와 vstd의 함수가 유한한 스택 공간을 쓴다는 점, 그리고 rustc가
  `become`을 명세대로 구현한다는 점(고정된 toolchain의 incomplete feature이며, 테스트
  `fip_strict_tail_calls_*`가 `opt-level=0`과 `3`에서 깊이 10^8의 `become` 재귀를 실행해 확인)
* `vstd::alloc_check::reclaim`을 위한 std의 `Allocator` 계약: `deallocate`(또는 `grow`, `shrink`)가 받는 블록은
  이 할당기가 내준, 아직 살아 있는 블록이라는 점("사용자 정의 할당기" 참고)
* 할당기 자신의 코드는 런타임이라는 점: 상한은 프로그램이 할당기를 부르는 호출(한 번에 1)을 세고, 할당기가
  하는 일은 세지 않습니다(그 `Allocator`, `Clone`, `Drop` impl은 할당, 해제, 스택을 검사하지 않음. "사용자
  정의 할당기" 참고)
* `encapsulates alloc(a, d)`의 횟수(그 함수의 본문은 런타임의 것이라 할당, 해제, 스택을 검사하지 않습니다)
* `#[verifier::trusted_call]` 블록 안의 호출(할당기의 전달용 `deallocate` 등). `--no-cheating`은 지금
  검증하는 crate에만 적용됩니다. 그것 없이 검증된 의존 crate의 블록(과 `external_body` 함수)은 그대로
  신뢰되고, `.vir`에는 `--no-cheating` 여부가 기록되지 않습니다
* `drop`이 아닌 `external_body` 함수, 그리고 `external_body` 타입(숨은 필드의 drop은 vstd가 선언한 std
  타입에 대해서만 신뢰)
* crate `std`, `core`, `alloc`, `vstd`, `verus_builtin`: 이들의 함수는 타입 인자의 trait bound를 통해서만
  사용자 코드에 닿고(fip 검사가 이것을 따라갑니다. "다른 crate에서 오는 콜백" 참고), 유한한 스택 공간을
  씁니다. 이름으로 알아보되, 이 이름의 crate는 진짜일 때만 받습니다. `std`,
  `core`, `alloc`은 toolchain의 sysroot에서 온 그 이름의 유일한 crate여야 합니다. `vstd`와
  `verus_builtin`은 Verus가 직접 `--extern vstd=..`, `--extern verus_builtin=..`으로 넘긴 파일이어야
  하고(`--no-vstd`에서는 어떤 의존 crate도 `vstd`라는 이름일 수 없음), 가져온 `vstd`는 vstd로 검증된
  것이어야 합니다. Verus는 이 파일들을 자신의 설치 위치에서 넘깁니다. `--is-core`, `--import-via-core`,
  내부 테스트 모드에서는 넘기지 않으므로, 그때는 명령줄에 준 것을 신뢰합니다. -V alloc-check로 검증하는
  crate는 이 이름을 쓸 수 없습니다. 다만 `--is-vstd`로 검증하는 crate는 `vstd`입니다(그때는 자기
  `external_body` drop과 불투명 타입을 신뢰하며, `--no-cheating`은 `--is-vstd`를 거부합니다)
* vstd가 기본 타입에 대해 제공하는 연산자 표시 trait(`FipAdd`, `FipOrd` 등)의 impl
* toolchain의 std(신뢰하는 drop과 불투명 타입)
* Verus 자신의 매크로(`verus!`, `#[verus_spec]` 등 `verus_builtin_macros`의 매크로와 vstd의 매크로).
  이들은 검증과 컴파일에 일부러 다른 코드를 넣습니다(ghost 코드, 검증에만 필요한 것)
* 다른 crate의 매크로가 이 crate에 넣는 토큰이 검증과 컴파일에서 같다는 점. `verus_keep_ghost_body`를
  쓰는지는 crate 자신의 소스만 검사합니다("상한 검사" 참고). 다른 crate의 매크로도 이 cfg를 시험할 수
  있고, 절차적 매크로는 이 이름을 쓰지 않고도 둘을 구별할 수 있습니다. 그런 매크로가 갈라 놓을 수 있는
  것은 일부만 막습니다. 컴파일은 검증이 읽은 것만 읽을 수 있고 cfg도 같아야 하며, `#[verifier::fip]`은
  두 쪽을 맞대어 보고, 암묵적 drop은 컴파일된 프로그램에서 검사합니다. 하지만 호출은 검증한 코드에서
  셉니다(컴파일된 프로그램에만 있는 호출은 보지 못합니다).

알려진 한계는 다음과 같습니다. 모두 프로그램을 거부하거나 더 약한 상한을 주는 쪽이며, 불건전하지는 않습니다.
* `dyn` 값이나 불투명 `impl Trait` 값의 drop
* drop하면 해제될 수 있는 값을 소유한 클로저의 drop
* drop glue 안의 projection 타입(예: `Cow`)
* 구조체의 필드 하나만 캡처하는 클로저를 구조체 전체를 캡처한 것처럼 검사하는 점
* 프로그램 어디에든 상한 있는 trait 메서드의 검사되지 않은 구현이 있는 경우

검사 대상 함수 안에서 `catch_unwind`는 거부합니다. panic을 잡으면 unwind 경로에서 일어난 할당 뒤에도
실행이 계속되는데, `allocates`는 그 할당을 세지 않기 때문입니다.
