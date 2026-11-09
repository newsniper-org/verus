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
* rustc 1.100의 `core::alloc::GlobalAlloc` 문서(`core/src/alloc/global.rs`, rust-lang/rust#159720)는
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

### 사용자 정의 할당기

전역 할당기가 아닌 할당기를 쓰는 컨테이너(`Vec<T, A>`, `Box<T, A>`, `Rc<T, A>` 등)는 할당 한 번마다
그때 하는 할당기 호출의 비용을 청구합니다. 할당은 말단에서 셉니다. 전역 할당기나 시스템 할당기를 한 번
호출하면 1입니다. 사용자 정의 할당기의 비용은 unsafe 표시 trait `vstd::alloc_check::BoundedAllocator`로
정합니다.

```rust
use std::alloc::{Allocator, AllocError, Global, Layout};
use std::ptr::NonNull;
use vstd::alloc_check::BoundedAllocator;

pub struct Fwd;

unsafe impl Allocator for Fwd {
    fn allocate(&self, layout: Layout) -> (r: Result<NonNull<[u8]>, AllocError>)
        allocates 1
    {
        Global.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout)
        allocates 0
    {
        #[verifier::trusted_call] {
            unsafe { Global.deallocate(ptr, layout) }
        }
    }
}

unsafe impl AllocFreeDrop for Fwd {}

unsafe impl BoundedAllocator for Fwd {
    open spec fn max_cost() -> int { 1 }
}

fn push_one(v: &mut Vec<u64, Fwd>, x: u64)
    allocates 1
{
    v.push(x);
}
```

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

`Allocator` 선언은 `deallocate`의 상한을 `allocates 0`으로 두고, `allocate`, `allocate_zeroed`, `grow`,
`grow_zeroed`, `shrink`의 상한은 표시 trait이 정하는 비용으로 둡니다. `max_cost()`는 모든 호출의
상한입니다. 호출 한 번의 비용인 `allocate_cost(&self, layout)`(`allocate_zeroed`에도 씀),
`grow_cost(&self, ptr, old_layout, new_layout)`, `grow_zeroed_cost`, `shrink_cost`는 할당기의 값과 인자에
따라 달라도 됩니다. 기본값은 `allocate_cost`가 `max_cost()`이고, 나머지는 새 layout의 `allocate_cost`입니다.
`max_cost()`를 넘는 호출 비용은 `max_cost()`로 깎습니다. Verus는 impl을 이 상한에 대해 검증합니다.
impl이 정의하지 않은 메서드는 std의 기본 본문을 실행하는데, 그 본문은 각각 새 layout으로 `allocate`나
`allocate_zeroed`를 한 번 호출합니다. 그래서 표시 trait은 impl이 `grow`, `grow_zeroed`, `shrink`를 정의할
때만 `grow_cost`, `grow_zeroed_cost`, `shrink_cost`를 정의할 수 있습니다.

`Vec<T, A>`와 `Box<T, A>`는 실제로 하는 호출의 비용을 청구합니다. 버퍼가 없는(capacity 0) 벡터가
성장할 때는 대신 `allocate`를 부르므로 새 layout의 `allocate_cost`가 청구됩니다. 크기 0인 `T`(그리고
그런 `T`의 `Box::new_in`)는 아무것도 부르지 않습니다. 기존 버퍼를 키우는 `Vec::push`에는 벡터의
할당기(`spec_vec_allocator`), 버퍼 포인터, 이전 capacity의 layout, 그리고 std의 성장 정책이 고르는
capacity(`vec_amortized_cap`, std 1.100의 정책)의 layout으로 계산한 `grow_cost`가 청구됩니다. 성장한 뒤
벡터의 capacity는 정확히 그 값이고, 할당기는 바뀌지 않습니다. 그래서 설정이나 요청 크기에 따라 비용이
달라지는 할당기도 정확한 상한을 줄 수 있습니다.

```rust
pub struct Chunked { pub limit: usize }

unsafe impl BoundedAllocator for Chunked {
    open spec fn max_cost() -> int { 1 }

    open spec fn allocate_cost(&self, layout: Layout) -> int {
        if spec_layout_size(layout) <= self.limit { 0 } else { 1 }
    }
}

fn push_fits(v: &mut Vec<u64, Chunked>)
    requires
        spec_vec_allocator(&*old(v)).limit == 256,
        old(v)@.len() == 8,
        spec_vec_capacity(&*old(v)) == 8,
    allocates 0
{
    v.push(1); // 16개, 128바이트로 성장
}
```

`VecDeque<T, A>`, `HashMap<K, V, S, A>`, `Rc::map`, `Arc::map`은 할당기 호출의 인자를 vstd가 이름 붙이지
않으므로 대신 `allocator_max_cost::<A>()`를 청구합니다. 이미 가진 메모리를 나눠 주는 arena는 비용을
0으로 둘 수 있고, 그러면 그 arena를 쓰는 컨테이너는 아무것도 할당하지 않습니다.

* 할당기의 `Allocator` impl이 Verus가 검사하는 것(`verus!` 안)일 때만 표시 impl을 받습니다.
  표시 impl도 모두 Verus가 검사하는 것이어야 합니다.
* 컨테이너를 drop하면 그 할당기의 `deallocate`가 호출됩니다. 그래서 할당기가 전역 할당기나 시스템
  할당기이거나 `BoundedAllocator`일 때만 컨테이너를 drop할 수 있습니다. 그런 할당기에 대한 참조도
  됩니다. 제네릭 할당기에는 `A: Allocator + BoundedAllocator` bound가 필요합니다. `AllocFreeDrop`이
  `BoundedAllocator`의 supertrait이므로, 할당기 자체를 drop할 때도 할당하면 안 됩니다.
* 컨테이너를 clone하면(`split_off`도) 할당기도 clone하며, 그 비용은 `allocator_clone_cost::<A>()`입니다.
  std의 컨테이너는 Verus가 보지 못하는 곳에서도 할당기를 clone합니다. `BTreeMap`(또는 그 `IntoIter`)을
  drop하면 해제하는 노드마다 한 번씩 clone합니다. 그래서 `BoundedAllocator`의 `Clone` impl은 Verus가
  검사하는 impl이어야 하고, `allocates 0`으로 묶여야 하며, 할당기 힙을 바꾸면 안 됩니다(다음 절).
  (그래서 할당기에 `#[derive(Clone)]`을 쓰면 거부됩니다. derive로 만든 impl은 Verus가 검사하지 않으므로,
  impl을 `verus!` 안에 직접 씁니다.)
  `Allocator`의 계약도 이미 clone한 할당기가 같은 할당기처럼 동작하기를 요구합니다. 따라서 이 비용은
  `BoundedAllocator`에서 0이며, 전역 할당기와 참조에서도 0입니다. 다른 할당기에서는 해석되지 않는 항입니다.
* `BoundedAllocator`만으로는 비용이 할당기의 값과 인자에만 의존할 수 있습니다. 메서드가 받는 `&self` 뒤의
  가변 상태에는 의존할 수 없습니다. 이 제한은 다음 절에서 풉니다.

### 상태 있는 할당기

이미 가진 블록을 먼저 내주는 풀이나, 다 쓰면 바닥나는 arena는 상태에 따라 비용이 다릅니다.
`vstd::alloc_heap::StatefulAllocator`(`BoundedAllocator` 위의 trait)는 상태의 타입, 그 위의 preorder
("적어도 그만큼 좋다"), 한 상태에서 `allocate`의 비용(`allocate_cost_at`)과 그 뒤의 상태(`allocate_next`)를
줍니다:

```rust
pub struct Free(pub nat);          // 남은 블록 수; 많을수록 좋다

impl Preorder for Free {
    open spec fn le(self, other: Self) -> bool { self.0 <= other.0 }
    proof fn le_refl(a: Self) {}
    proof fn le_trans(a: Self, b: Self, c: Self) {}
}

unsafe impl StatefulAllocator for Pool {
    type State = Free;
    open spec fn loc(&self) -> Loc { self.reg@.loc() }
    proof fn witness<'a>(tracked &'a self) -> (tracked w: &'a Registered<Free>) { self.reg.borrow() }
    open spec fn allocate_cost_at(&self, s: Free, layout: Layout) -> int {
        if s.0 > 0 { 0 } else { 1 }
    }
    open spec fn allocate_next(&self, s: Free, layout: Layout, r: Result<NonNull<[u8]>, AllocError>) -> Free {
        if s.0 > 0 { Free((s.0 - 1) as nat) } else { s }
    }
}

fn two(p: &Pool, l: Layout)
    requires allocator_state(p).0 >= 2,
    ensures allocator_state(p).0 == old_allocator_state(p).0 - 2,
    allocates 0
{
    let _ = p.allocate(l);
    let _ = p.allocate(l);
}
```

Verus는 스레드마다 이 상태들의 하한을 담은 ghost heap을 둡니다. 명세에서는 `allocator_state(a)`(`ensures`에서는
호출 뒤, `requires`와 본문에서는 현재 상태)와 `old_allocator_state(a)`(함수가 불렸을 때의 상태. `allocates`
상한에서는 이 형태만 쓸 수 있습니다)로 읽습니다. `a.allocate(layout)` 호출은
`allocate_cost_at(allocator_state(a), layout)`(`max_cost()`로 자름)만큼 청구되고, 상태를 `allocate_next`로
옮깁니다. impl의 `allocate`는 같은 두 사실에 대해 검증됩니다.

* 구현은 실제 상태를 `AllocAuth<S>`(자기 불변식 안)에 둡니다. `AllocAuth::register(s)`가 이것을 만들고,
  할당기가 가지고 있어야 하는 증인 `Registered<S>`도 돌려줍니다(`witness`). `AllocAuth::step`은 실제 상태와
  heap의 하한을 함께 옮기고(할당), `AllocAuth::raise`는 실제 상태만 올립니다(해제).
* heap은 상태가 아니라 하한을 담습니다. `deallocate`는 Verus가 보지 못하는 곳(컨테이너를 drop할 때)에서
  실행되므로 상태를 올리기만 할 수 있습니다. heap을 바꿀 수 있는 `deallocate`나 `Drop::drop`은 거부됩니다.
* `Registered`는 `Send`도 `Sync`도 아니므로, 이것을 가진 할당기도 그렇습니다. 상태와 그 하한은 한 스레드에
  머뭅니다. 이는 할당기가 스스로 `Send`나 `Sync`를 구현하지 않는다는 데 기댑니다. `verus!` 밖에 쓴
  `unsafe impl Send`/`Sync`는 (auto trait의 `unsafe impl`이 늘 그렇듯) Verus가 검사하지 않으며, 상태를 다른
  스레드로 옮길 수 있게 합니다.
* 명세에서 heap을 언급하는 함수는 그 변화를 호출자에게 전합니다. heap을 바꿀 수 있는 다른 함수(상태 있는
  할당기에서 할당하거나, Verus가 효과를 볼 수 없는 코드: 클로저, Verus의 heap 분석 없이 검증된 crate의
  함수를 부르는 함수)를 부른 뒤에는 상태를 모르게 되고, 그때 비용은 `max_cost()`입니다. 분석은 인스턴스마다
  이루어집니다. 타입 매개변수 `A`를 통해서만 할당기에 닿는 제네릭 함수(`Vec<u8, A>`에 `v.push(1)`)는
  `A = Global`로 부르면 상태를 유지합니다. heap을 바꾸는 proof
  함수는 `ensures`에서 어떻게 바꾸는지 밝혀야 합니다.
* `external_body` 함수와 `assume_specification`은 `allocates` 상한처럼 신뢰합니다. 이들은 타입 인자(타입
  매개변수, 클로저, 사용자 crate의 타입)를 통해서만 heap을 바꿀 수 있다고 봅니다. 그래서 사용자 타입으로
  인스턴스화한 std 호출(`Vec<MyStruct>::push`)도 상태를 모르게 만듭니다.
* `grow`(`grow_zeroed`)와 `shrink`도 `grow_cost_at`/`grow_next`, `shrink_cost_at`/`shrink_next`로 상태를
  옮깁니다. 기본값은 std 기본 본문이 하는 일(새 layout으로 `allocate` 한 번)이고, 할당기는 자기 `Allocator`
  impl이 정의한 메서드에 대해서만 바꿀 수 있습니다. `&A`를 통한 호출은 `A`의 메서드 호출입니다.
* 컨테이너 명세는 heap에 무엇을 하는지 말합니다:
  * `Vec`: 할당하는 모든 연산(`with_capacity_in`, `reserve`, `try_reserve`, `try_reserve_exact`, `push`,
    `insert`, `append`, `extend_from_slice`, `resize`)은 상태에서의 할당기 호출 비용만큼 들고, 상태를 할당기가
    말하는 대로 옮깁니다(전역 할당기이거나 벡터에 자리가 있으면 그대로). 나머지 연산은 heap을 그대로 둡니다.
    `Box::new_in`도 같습니다.
  * `VecDeque`(`new_in`, `with_capacity_in` 포함), `HashMap`, `HashSet`: 할당하는 연산은 할당기를 최대 한 번
    부르고(`allocator_some_call_heap_in`), 비용은 상태 없는 비용입니다. 나머지는 heap을 그대로 둡니다.
    `BTreeMap`/`BTreeSet`의 읽기와 삭제도 그대로 둡니다.
  * 그 뒤에 heap을 모르게 되는 것: 할당기를 clone하는 연산(`clone`, `split_off`), 클로저를 부르는 연산
    (`Box`/`Rc`/`Arc::map`), trait 메서드(`Deref`, `Index`, `IntoIterator`), `BTreeMap`/`BTreeSet`의 삽입
    (`allocates` 상한이 없음).
  * 원소 타입을 통해 사용자 코드가 상태 있는 할당기에 닿을 수 있으면(`Vec<Vec<u8, &Pool>>`: `T::clone`, drop)
    컨테이너 명세는 heap을 말하지 않고, 호출 뒤 heap을 모르게 됩니다.
* 클로저 자신의 명세도 heap을 말할 수 있습니다. `requires`와 본문에서 `allocator_state(a)`는 호출 중 그 지점의
  heap, `ensures`에서는 돌아갈 때의 heap, `old_allocator_state(a)`는 호출됐을 때의 heap입니다. 클로저 값을
  부르면(`f(x)`) 호출자의 heap에서 그 명세를 씁니다. `allocates` 상한은 함수와 마찬가지로 호출될 때 계산되므로
  `old_` 형태만 쓸 수 있습니다.

  ```rust
  let f = |u: u8| -> (r: Result<NonNull<[u8]>, AllocError>)
      allocates if old_allocator_state(p).0 > 0 { 0int } else { 1int }
  {
      p.allocate(l)
  };
  ```

  이런 클로저(`requires`, `ensures`, `allocates` 중 하나라도 heap을 말하는 클로저)는 `call_requires(f, args)`만
  아는 곳(제네릭 코드)에 넘길 수 없습니다. 그것은 "모든 heap에서"를 뜻하기 때문입니다. `allocates` 상한이 heap을
  말하는 함수를 값으로 쓸 때도 같습니다(`let g = take; g(p, l)`은 되고, `take`를 제네릭 코드에 넘기는 것은 안
  됩니다).

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
`requires`(`call_requires`, `call_ensures`, `call_allocates`)로 풀립니다. 함수의 타입 매개변수 말고도
`where` 절(`where T: Clone with { .. }`, 매개변수가 아닌 타입에도), inherent impl 블록(그 안의 모든 exec·proof
메서드가 받음), struct의 타입 매개변수(같은 `verus!` 블록에 있는 그 struct의 모든 inherent impl 블록이,
매개변수를 인스턴스화한 타입에 대해 받음)에 쓸 수 있습니다. trait impl에서는 메서드가 `requires`를 가질 수
없으므로 거부됩니다.

## 완전한 제자리 함수: `#[verifier::fip]`

FP² 논문(Lorenzen·Leijen·Swierstra, ICFP 2023)은 제자리에서 실행되는 함수를 구분합니다. 그 용어로
말하면 `allocates n` 상한은 `fbip(n)`의 힙 부분입니다. 할당은 최대 `n`번이고 해제는 몇 번이든
됩니다. `#[verifier::fip]`는 `fip(n)`입니다. 이 함수는 정상 반환할 때 메모리를 전혀 해제하지 않습니다.
`allocates` 상한이 없으면 `fip`이고, 할당도 하지 않는다는 뜻입니다(`allocates 0`). 이 속성에는
`-V alloc-check`가 필요하며, 한 함수에는 `#[verifier::fip]`와 `#[verifier::fip(strict)]` 중 하나만 붙일 수 있습니다.

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
  거짓임을 보여야 합니다. 검증된 본문이 없는 명세는 이 조건을 `allocates deallocates_when(n, c)`로
  적습니다. 그 함수는 최대 `n`번 할당하고, `c`가 참일 때만 해제할 수 있습니다(`c`는 진입 시점에
  평가). 예를 들어 `Vec::push`는 기존 버퍼를 키워야 할 때 해제할 수 있습니다. 키우는 것은
  재할당이고, 재할당은 옛 블록을 해제하기 때문입니다. 버퍼가 없는 벡터는 할당기의 `allocate`만 불러서
  키웁니다. 전역 할당기와 시스템 할당기의 `allocate`는 해제하지 않습니다. 다른 할당기의 `allocate`는
  사용자 코드입니다(아래 참고).
  impl로 해석되지 않는 trait 메서드 호출(제네릭 호출)과 클로저 호출은 거부합니다.
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

컨테이너는 std 코드 안에서 할당기의 메서드를 부릅니다. 그래서 fip 함수는 전역 할당기나 시스템 할당기가
아닌 할당기로 std나 vstd 코드를 쓸 때(`Vec<u8, A>::push`, `Vec::with_capacity_in(n, a)`), 그 할당기가
unsafe 표시 trait `vstd::alloc_check::FipAllocator`를 구현해야 합니다. 제네릭 할당기에는
`A: FipAllocator` bound가 필요합니다. `unsafe impl FipAllocator for X`는 `X`의 `allocate`, (`Allocator`
impl이 정의한다면) `allocate_zeroed`, (있다면) `Clone::clone`이 모두 같은 crate의 `#[verifier::fip]`
함수일 때만 받습니다. `Allocator`, `BoundedAllocator`, `NoDeallocDrop`이 supertrait입니다.
`#[verifier::fip(strict)]` 함수에는 대신 `FipStrictAllocator`가 필요하고, 그 메서드는
`#[verifier::fip(strict)]`여야 합니다.

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

* 호출 대상은 다른 엄격한 함수이거나 std나 vstd의 함수일 수 있습니다. std와 vstd의 함수는 호출자의
  코드로 되돌아 부르지 않습니다. 그렇게 할 수 있는 호출(콜백을 통한 호출)은 위의 검사가 거부하기
  때문입니다. 다른 crate의 함수는 엄격한 함수이고, 그 crate가 `-V alloc-check`로 검증·컴파일되어 라이브러리
  파일과 함께 import된 경우에만 부를 수 있습니다(`become`의 대상으로도). 그 컴파일이 그 함수와 거기서 닿는
  모든 함수를 검사했고, 엄격한 함수의 호출 대상은 모두 알려져 있으므로 되돌아 부를 수 없습니다("라이브러리와
  다른 crate" 참고). 그 밖의 다른 crate 함수 호출과 callee를 알 수 없는 호출(제네릭 호출, 함수 값)은
  거부합니다.
* 소멸자도 호출로 칩니다. 그 함수의 drop이 실행하는 소멸자와, std나 vstd 호출이 인스턴스화된 타입의
  소멸자(std는 `Vec::<T>::clear`처럼 호출 안에서 그런 값을 drop할 수 있습니다)입니다. 다른 crate 타입의
  소멸자는 그 crate의 함수와 같은 조건(`-V alloc-check`로 검증·컴파일된 crate의 엄격한 `Drop::drop`)일 때 받고,
  그렇지 않으면 거부합니다. 타입 매개변수,
  associated 타입이나 불투명 타입, `dyn`이 관련되어 소멸자를 여기서 알 수 없는 drop(또는 그런 호출)은
  거부합니다. `Copy` bound가 있으면 소멸자가 없습니다.
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
* vstd 명세의 `deallocates_when` 조건(`#[verifier::fip]`용)
* `#[verifier::fip(strict)]`의 경우: std와 vstd의 함수가 유한한 스택 공간을 쓴다는 점, 그리고 rustc가
  `become`을 명세대로 구현한다는 점(고정된 toolchain의 incomplete feature이며, 테스트
  `fip_strict_tail_calls_*`가 `opt-level=0`과 `3`에서 깊이 10^8의 `become` 재귀를 실행해 확인)
* `vstd::alloc_check::reclaim`을 위한 std의 `Allocator` 계약: `deallocate`(또는 `grow`, `shrink`)가 받는 블록은
  이 할당기가 내준, 아직 살아 있는 블록이라는 점("사용자 정의 할당기" 참고)
* `#[verifier::trusted_call]` 블록 안의 호출(할당기의 전달용 `deallocate` 등). `--no-cheating`은 지금
  검증하는 crate에만 적용됩니다. 그것 없이 검증된 의존 crate의 블록(과 `external_body` 함수)은 그대로
  신뢰되고, `.vir`에는 `--no-cheating` 여부가 기록되지 않습니다
* `drop`이 아닌 `external_body` 함수, 그리고 `external_body` 타입(숨은 필드의 drop은 vstd가 선언한 std
  타입에 대해서만 신뢰)
* crate `std`, `core`, `alloc`, `vstd`, `verus_builtin`: 이들의 함수는 타입 인자를 통해서만 사용자 코드에
  닿고, 유한한 스택 공간을 씁니다. 이름으로 알아보되, 이 이름의 crate는 진짜일 때만 받습니다. `std`,
  `core`, `alloc`은 toolchain의 sysroot에서 온 그 이름의 유일한 crate여야 합니다. `vstd`와
  `verus_builtin`은 Verus가 직접 `--extern vstd=..`, `--extern verus_builtin=..`으로 넘긴 파일이어야
  하고(`--no-vstd`에서는 어떤 의존 crate도 `vstd`라는 이름일 수 없음), 가져온 `vstd`는 vstd로 검증된
  것이어야 합니다. Verus는 이 파일들을 자신의 설치 위치에서 넘깁니다. `--is-core`, `--import-via-core`,
  내부 테스트 모드에서는 넘기지 않으므로, 그때는 명령줄에 준 것을 신뢰합니다. -V alloc-check로 검증하는
  crate는 이 이름을 쓸 수 없습니다. 다만 `--is-vstd`로 검증하는 crate는 `vstd`입니다(그때는 자기
  `external_body` drop과 불투명 타입을 신뢰하며, `--no-cheating`은 `--is-vstd`를 거부합니다)
* toolchain의 std(신뢰하는 drop과 불투명 타입)

알려진 한계는 다음과 같습니다. 모두 프로그램을 거부하거나 더 약한 상한을 주는 쪽이며, 불건전하지는 않습니다.
* 할당기가 전역 할당기도, 참조도, `BoundedAllocator`도 아닌 컨테이너의 clone, 그리고 자신이 가진 할당기에
  위임하는 할당기(`Box`, `Rc`, `Arc`, `Pin`을 할당기로 쓰는 경우): 비용이 해석되지 않는 항
  (`allocator_clone_cost::<A>()`, `allocator_max_cost::<A>()`)이므로 그 항을 그대로 쓰는 상한만 검증됩니다
* `dyn` 값이나 불투명 `impl Trait` 값의 drop
* drop glue 안의 projection 타입(예: `Cow`)
* 구조체의 필드 하나만 캡처하는 클로저를 구조체 전체를 캡처한 것처럼 검사하는 점
* 프로그램 어디에든 상한 있는 trait 메서드의 검사되지 않은 구현이 있는 경우

검사 대상 함수 안에서 `catch_unwind`는 거부합니다. panic을 잡으면 unwind 경로에서 일어난 할당 뒤에도
실행이 계속되는데, `allocates`는 그 할당을 세지 않기 때문입니다.
