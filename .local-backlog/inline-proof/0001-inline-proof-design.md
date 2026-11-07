<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# 0001 — inline 증명 (inline (Max)SAT/(Max)SMT/ASPMT/ITP)

- 상태: **논의 단계 (구현하지 않음).** 2026-11-07 사용자와의 논의를 정리한 것이다. 사용자 지시는 "매우 신중하게 검토할
  필요가 있어서, 일단은 논의만"이다.
- adsmt 쪽에 요청이 필요한 항목은 따로 모았다: `../adsmt/DRAFT-request-inline-proof.md` (미발신).

## 1. 아이디어

- **inline asm의 증명판이다.** 자동 증명(SMT) 흐름 안에 다른 언어로 된 증명 조각을 끼워 넣는다. 목적은 두 가지다.
  - 표현력: VIR/SMT로 표현하거나 닫을 수 없는 것을 다룬다.
  - 증명 과정의 최적화: 속도와 안정성을 높인다.
- **interactive theorem proving을 inline embedding 형태로 바꾸어 쓰는 것이다.**
- 사용자가 염두에 둔 구성은 셋이고, 이들끼리 결합하는 것까지 포함한다.
  - (A) inline SMT/ITP 질의: 목표 하나를 좁은 문맥, 선택한 논리, 선택한 백엔드로 닫는다.
  - (C) MaxSAT/MaxSMT: 증명의 *최적화*를 맡는다. 최소 unsat core로 문맥을 가지치기하고, 최소 인스턴스화 집합을 고르고,
    trigger를 선택한다.
  - (D) ASP(MT): 조합적 *증명 계획* 탐색을 맡는다. 어떤 lemma를 어떤 순서로 쓰고 어떻게 경우를 나눌지 고른다. weak
    constraint로 비용을 최소화할 수 있다.
  - 결합 구도: (D)가 계획하고 → (C)가 단계별 문맥과 인스턴스를 최소화하고 → (A)가 닫고 → 인증서를 남긴다.
- 동기: **표현력 한계가 가장 큰 문제이고, 처리 비용도 만만치 않다**(사용자).
- 이 문서의 범위 밖: ASP를 *명세 언어*로 Verus 논리에 들이는 것. stable model과 고전 모델 사이의 의미론 간극
  (completion, loop formula) 때문에 훨씬 위험하다. 여기서 ASP는 탐색(계획)에만 쓴다.

## 2. 확정된 원칙 (사용자 결정, 2026-11-07)

1. **진술은 VIR을 거치고, 본문만 VIR을 건너뛴다.** 진술(가설과 결론)은 인라인 영역과 바깥 영역 사이의 인터페이스다
   (사용자: "진술까지 VIR을 건너뛰는 건 말이 안 된다"). inline asm에서 operand와 제약은 컴파일러가 타입 검사하고
   asm 문자열만 불투명한 것과 같은 구조다.
   - 진술을 VIR 밖에서 번역하면 두 번째 의미론이 생기고, 둘이 어긋나면 그 자체로 불건전하다.
     예: 정수 범위, 나눗셈 의미론, `nat` 뺄셈, datatype 불변식, spec fn 정의와 fuel, mode, allocator heap 숨은 매개변수.
2. **호출마다 프로필을 지정한다.** `inline_proof! "adsmt" { ... }`의 `"adsmt"`가 어떻게 번역해서 누가 처리할지를
   정한다. 프로필의 정의는 설정 쪽에 둔다.
3. **별도 계약을 새로 만들지 않는다.** adsmt-emit의 기존 계약에 *역할(role)* 하나만 추가해 재사용한다(§4).
4. **진술 대조는 Verus 쪽에서 한다.** 먼저 방식 (b)로 시작한다(§5).
5. **`--locked` 모드와 lock 해시 기록을 넣는다**(§6).

## 3. 문법 스케치 (미확정)

```rust
proof fn lemma_foo(x: int, s: Seq<u8>)
    requires P(x, s),
    ensures  Q(x, s),
    by inline_proof!("adsmt", uses(spec_f, lemma_bar)) {
        r#" ... {x} ... {s} ... "#
    }

assert(P) by inline_proof!("plan", uses(...)) { ... }
```

- `uses(...)`: asm의 operand처럼, 블록이 보는 spec fn 정의와 lemma를 **명시**한다.
  - VIR은 이 목록으로 의존성, pruning, 증분 재검증, 캐시 무효화를 계산한다.
  - 경계 번역기는 이 목록만 내보낸다. 문맥 전체를 번역하지 않으므로 처리 비용이 준다.
- `{x}`: asm의 `{0}`처럼 본문에서 Verus 이름을 가리킨다. 무엇으로 치환할지는 경계 번역기가 정한다.
- 본문은 raw string 또는 외부 파일(`file = "..."`)이다. Rust 토큰으로는 Isar의 `‹›`, 균형이 맞지 않는 따옴표,
  `%` 주석을 담기 어렵다.
- 붙는 자리 후보: `proof fn ... by inline_proof!(...)`, `assert(P) by inline_proof!(...)`. (미결)

## 4. 실행 구조 — adsmt-emit 재사용

adsmt-emit의 현재 작동 방식(rc.31~, `~/AD1/adsmt-emit`, `~/adsmt-contrib/adsmt-emit-*-wasm`):

- 패키지 = `wasm32-wasip1` 명령.
  - stdin으로 바이트를 받고 stdout으로 바이트를 낸다.
  - 종료 코드: 0 성공, 2 미지원, 3 잘못된 입력, 그 밖은 내부 오류.
- wasmi로 실행한다. 샌드박스이고 stdio만 열려 있다(파일시스템, 네트워크, 환경 변수 없음). 메모리 상한을 걸 수 있고,
  `-j N`으로 병렬 실행한다.
- 패키지 파일 하나에 TOML frontmatter(`name/target/version/contract/main/wire`)와 빌드 스크립트가 함께 들어 있다.
- `adsmt-emit.toml`(매니페스트)과 `adsmt-emit.lock`(lockfile)을 쓰고, 패키지는 내용 해시(sha256) 기반 저장소에 들어간다.
- 지금의 역할은 하나뿐이다: 인증서(CBOR, 평탄화된 hash-cons 풀) → ITP 소스(Isabelle/Rocq/Lean).
- `Theorem`은 역직렬화할 수 없다. 커널만 만드는 신뢰 토큰이고, 인증서에는 `Sequent`가 담긴다.

inline 증명에 대응시키면:

| 단계 | 담당 | TCB 여부 |
|---|---|---|
| 진술 번역 (Verus → lu-kb) | Verus 경계 번역기 = emit-lukb (poly 이전 SST, `verifier.rs:2078` 삽입 지점) | **TCB** |
| 본문 번역 (ASP/MaxSMT 지시/Isar/... → lu-kb) | **front 역할** 패키지 (wasm, 샌드박스) | TCB 아님 |
| 풀이 | adsmt 본체 (native) | 결과는 커널이 검사 |
| 1차 검사 | adsmt-core 커널 (HOL+LCF) | TCB (커널) |
| 진술 대조 | Verus (§5) | TCB (작은 비교기) |
| 2차 독립 검사 (선택) | emitter 역할 패키지 → ITP 재생 (Y4 cert-replay 트랙) | TCB 아님 (진술 대조가 따로 있으므로) |

- front는 본문(증명 *방법*)만 바꾼다. 진술은 Verus가 만든다. 그래서 front에 버그가 있으면 결과는 "증명 실패"이거나
  "다른 것을 증명함"이고, 후자는 §5의 대조가 거른다.
- 역할 추가는 하위 호환 확장으로 한다.
  - frontmatter `role`: 기본값은 `"emitter"`로 두어 기존 패키지를 그대로 쓰고, 새 값은 `"front"`.
  - front 입력: 진술, 본문, 바인딩을 담은 레코드(CBOR). front 출력: lu-kb 텍스트.
  - 계약 버전을 `0.1.0` → `0.2.0` 정도로 올린다. 런타임의 `emit(&[u8])`는 이미 바이트 일반적이라 런타임, 패키지 관리자,
    저장소는 그대로 쓴다.
- 합성 프로필(파이프라인), 예: `pipeline = ["asp-plan", "maxsmt-core", "adsmt"]`.
  - 중간 단계(계획, 최소화)는 탐색일 뿐이라 신뢰할 필요가 없다.
  - **최종적으로 받아들여지는 각 단계는 커널 검사와 §5 대조를 거쳐야 한다.**
  - (C)의 최적성 인증서는 필요 없다. "더 작은 문맥에서도 증명된다"가 검사되면 충분하고, 최적이 아니어도 성능 문제일 뿐이다.

## 5. 진술 대조 (Verus 쪽, 방식 (b)로 시작)

| 방식 | 비교 대상 | 추가 TCB |
|---|---|---|
| (a) Verus가 진술을 adsmt-core `Term`으로 직접 만든다 (크레이트 링크) | `Term` 대 `Term` 구조 비교 | 경계 번역기만 |
| **(b) Verus는 lu-kb 텍스트를 보내고, adsmt가 elaboration한다** | elaboration된 `Term` 대 인증서 결론 | 경계 번역기 + lu-kb elaborator |

- (b)를 택했다(2026-11-07). 일반 의무도 lu-kb elaborator를 거치므로 새로 늘어나는 신뢰가 아니다. 다만 lu-kb가 아직
  구현 중이라(refinement type, nested instantiation 등) elaborator는 당분간 움직이는 표적이다.
- Verus는 adsmt-cert를 serde로 디코드만 해서(가볍다) 다음을 대조한다.
  1. 인증서 결론이 기대 진술과 α-동치인가.
  2. 인증서 가설이 진술의 `requires`와 `uses(...)`로 선언한 것 안에 드는가.
  3. `Assumed` / `Theory` / 불투명 증인 단계(예: 위임 unsat의 `oxiz-delegation` 증인)가 있는가. 있으면 장부에서
     "CHECKED"와 구분해 단계 종류별로 센다.
- 나중에 (a)로 가면 Verus 프로세스 안에서 커널이 인증서를 재검사할 수도 있다. 그러면 "adsmt가 checked라고 말했다"를
  믿을 필요가 없어진다.
- 반드시 막아야 하는 것: **emitter와 front는 검사되지 않는 번역기다.** ITP 재생 성공은 *생성된 소스의 진술*이 증명됐다는
  뜻일 뿐이다. adsmt-contrib의 커밋 `faada24` "three silent mistranslations"가 이 위험이 실재함을 보여 준다. 진술을
  독립적으로 고정하는 §5가 이 구멍을 막는다.

## 6. 설정: `verus.toml` → adsmt-emit forward

- 매니페스트: `verus.toml`에 적힌 내용을 adsmt-emit에 forward한다(사용자 결정). `[adsmt.cas]` → `ADSMT_CAS_MANIFEST`
  연결과 같은 방식이다.
- lockfile: 없을 때만 adsmt 쪽이 생성한다(사용자 결정). 다만 이것만으로는 "첫 실행 시 신뢰"가 되므로 보완한다.
  1. **`--locked` 모드:** CI용. lockfile이 없거나 매니페스트와 맞지 않으면 생성하지 않고 오류를 낸다. 사용자 동의.
  2. 매니페스트가 바뀌었는데 lockfile이 낡았으면 바뀐 항목만 다시 해석한다(cargo식). `--locked`에서는 오류다.
  3. **lock 해시 기록:** 의무마다 장부에 lockfile 해시, 프로필 이름, 패키지 sha를 남긴다. 사용자 동의.
  4. 경로: adsmt-emit의 기본값은 `<cwd>/.adsmt-emitters/`와 cwd의 lockfile이다. Verus의 cwd는 호출 방식(`vargo`,
     `cargo verus`)에 따라 달라지므로, 저장소와 lockfile 경로를 `verus.toml` 위치 기준으로 명시해 forward한다.
     `ADSMT_EMIT_STORE`는 이미 있고, lockfile 경로 변수가 하나 더 필요하다(요청 항목).
  5. 우선순위: 원래의 `adsmt-emit.toml`도 있으면 CAS 연결과 같은 규칙("native가 이긴다" + 경고)으로 맞춘다. (미확정)
- 설정이 건전성을 바꾸지 못하게 한다.
  - 진술 번역기와 진술 대조기는 Verus 안에 있다.
  - 패키지는 내용 해시로 고정되고 샌드박스에서 돈다.
  - 설정으로 바꿀 수 있는 것은 성능과 탐색(어느 front, 어떤 옵션, 타임아웃)뿐이다.

## 7. lu-kb와의 관계 (사용자 제공, 2026-11-07)

- lu-kb는 adsmt 자체 입력 언어다. SMT-LIB v2.x의 문제들을 돌파하려는 설계 결정이다.
- 목표: FOL 스캐폴딩 없음 / theorem package 지원 / refinement type 지원 / 사람이 읽기 편한 문법 / nested
  instantiation 지원. **아직 구현이 완성되지 않았다.**
- 각 목표가 이 설계에서 하는 역할:
  - FOL 스캐폴딩 없음: "증명 ABI"가 Verus 내부 인코딩(Poly boxing, `has_type`, fuel, 이름 맹글링)에 묶이지 않는다.
    날 SMT-LIB를 inline으로 열 때의 가장 큰 위험이 사라진다.
  - refinement type: `nat`, 정수 범위, 타입 불변식을 가드 없이 옮긴다. 경계 번역의 fidelity 문제가 구조적으로 준다.
  - theorem package: inline 블록의 결과를 이름 있는 정리로 돌려받는 단위가 된다. 진술 인터페이스가 곧 패키지의 공개
    정리다.
  - nested instantiation: (C)의 최소 인스턴스화 집합을 남기는 형태로 쓴다.
- 정의와 공리: lu-kb는 이미 구분하고, 더 엄격하게 구분할 예정이다(사용자). **문법 수준**에서 구분되면 Verus가 "inline
  본문에는 공리 금지(쓰려면 `trusted`로 계상)"를 기계적으로 강제할 수 있다.

## 8. 기존 작업과의 의존

- emit-lukb (memory `emit-lukb-fidelity-and-match-proposal`, `native-lukb-retarget-plan`)가 진술 번역기다. 그래서 그
  작업의 현재 상태가 곧 inline 증명의 제약이다.
  - 209개 중 173개만 emittable이다. 범위 밖의 진술은 inline 블록에서 **컴파일 시점 오류**로 처리한다. 조용히 일부만
    번역하지 않는다.
  - D2("`Nat`/`WNat` 금지")가 ABI 규약이 된다.
  - if/match 표면 제안이 진술 표현 범위를 정한다.
  - native 경로가 `n + 0 = n`에 `sat`을 내는 문제가 해결되기 전에는 그 경로를 프로필에서 고를 수 없게 막는다.
- 장부: memory `adsmt-ledger-definition-question`의 "CHECKED unsat만 verified" 규칙을 inline 결과에도 그대로 적용한다.
- Y4 인증서 재생 트랙 (memory `adsmt-layers-and-isabelle-cert-track`): 2차 검사가 같은 기반을 쓴다. P0(Isabelle emitter가
  unsat 가정 집합을 공리화해 이론이 모순되는 문제)는 inline 경로에도 같은 함정이다.
- backend-pluggable 브랜치: 프로필의 백엔드 선택이 이 브랜치 위에 얹힌다.

## 9. 미결

1. `inline_proof!`가 붙는 자리와 정확한 문법(§3).
2. 본문 표기의 주 형태: raw string과 외부 파일 중 무엇인가.
3. 검사기 없는(`trusted`) 프로필을 허용할지. 허용한다면 `assume`급으로 표시하고 장부에서 따로 센다.
4. ITP embedding의 방향: Verus가 호스트인지(Isar 조각을 Verus 안에), Isabelle이 호스트인지(Verus 목표를 Isabelle이
   받음).
5. mode와 erasure: inline 블록은 proof 전용이고, tracked 자원을 소비하거나 만들지 못하게 한다(lifetime 검사 연동).
6. 진술이 allocator heap을 말할 때 숨은 heap 인자를 번역에 포함하는 방식(`closure_alloc_heap` 작업의 교훈).
7. 원래의 `adsmt-emit.toml`과 `verus.toml` forward가 함께 있을 때의 우선순위(§6.5).
8. adsmt-emit WIT 주석(wasip2 component, JSON)과 실제 경로(wasip1 command, CBOR 기본, path A)가 어긋난다. 역할을 추가하기
   전에 어느 쪽이 규범인지 정해야 한다(요청 항목).
