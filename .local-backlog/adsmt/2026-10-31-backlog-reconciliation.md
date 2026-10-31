<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# adsmt 백로그 대조표 — 2026-10-31 기준 (내부, 미발신)

정리 범위: 미회신 인바운드 **2026-08-02 → 2026-09-08 (9건)**.
마지막 발신 재핀 확인은 `2026-07-21-b191c71-CONFIRMED-159…` (원장 159).
그 뒤 발신한 두 건(`2026-09-01` P0, `2026-09-06` URGENT)은 재핀/원장을
다루지 않았으므로 **재핀·원장 축은 07-21 이후 끊겨 있습니다.**

## 0. 한 줄 요지

재핀 요청 6건은 전부 **단일 핀으로 흡수 완료**(09-06 발신 §6에서 선언).
남아 있는 진짜 미결은 **질문 3건(08-30 §3.4)** + **확인 2건(09-08 §1)** +
**원장 173 미검증**뿐이다. 그리고 **우리를 막고 있던 블로커 ①이 닫혔다.**

## 1. 재핀 체인 — 6건 전부 중첩, 단일 핀으로 붕괴

| 날짜 | 원장 | oxiz | AD1 | 상태 |
|---|---|---|---|---|
| 08-02 | 162 | `88c2679` | `149c9b3` | 중첩 |
| 08-02 ADD | **169** (정정) | `26d8d8a` | `d205fc8` | 중첩 |
| 08-17 | **171** | `5cbff16` | `4bc5d7a` | 중첩 |
| 08-23 ADD | 171 (행-동일) | `246657d` | `f3a0b7b` | 중첩 |
| 08-30 | 171 (행-동일 4연속) | `fd2ea4a` | `67e8e9f` | 중첩 |
| 08-31 | **173** (+5 / −3) | `f73d234` | `375050b` | 중첩 |
| 08-31 | 173 불변 | — | `d4c4acc` | 중첩 |
| 09-06 | — | `808d7f5` | **`0eaa7e2`** | ← **우리가 빌드한 핀** |
| 09-08 | 173 회귀 0 | — | `0db3a24`..`4d0d55e` | **미확인 재핀 요청** |

- 우리 기록: `tools/common/consts.rs:19` `EXPECTED_ADSMT_VERSION = "1.0.0-rc.42.1"`.
- **6건 흡수는 이미 선언했음** — `2026-09-06-URGENT-reply…` §6
  ("밀린 재핀 5건은 이 하나로 흡수하겠습니다"). 실제로는 5가 아니라 **6건**이었다.
- **원장 173은 우리가 한 번도 재스윕하지 않았다.** 07-21의 159가 우리 쪽 마지막
  독립 검증값이다. 159 → 173은 **전부 adsmt 단독 측정치**다.

## 2. 핀이 이미 낡았다 — AD1은 46커밋 앞서 있다

측정값(2026-10-31, `~/AD1`):

- `main` HEAD = **`d0731217`** (2026-10-02)
- `0eaa7e2..HEAD` = **46 커밋**
- `5fe25c3`(09-06 ①의 수정, 당시 "푸시 전")은 **HEAD의 조상 → 푸시 완료**
- AD1 `Cargo.toml` 버전은 여전히 **`1.0.0-rc.42.1`** (09-08 §4: 번호는 우리 결정사항)

즉 **09-08의 재핀 요청(`4d0d55e`)조차 이미 30커밋 뒤쳐진 상태**이고,
AD1 최종 커밋으로부터 **약 4주**가 지났다. 다음 재핀은 `4d0d55e`가 아니라
**HEAD 기준으로 요청을 다시 받는 편이 맞다.**

HEAD까지 들어온 것 중 우리 미결과 직접 겹치는 커밋:

| 커밋 | 우리 쪽 대응 미결 |
|---|---|
| `0e9efdb1` lower: Nat/WNat 결과가 positivity를 나른다 | **② 결함 A — 랜딩된 것으로 보임** |
| `3efcc89d` `decreases`가 본문 없는 함수 admit 거부 | ③ `rec` 표면 |
| `612cf4a7` 상호 `fn` 그룹 = 검사된 guarded admitter | ③ |
| `81e0f08e` docs §11: `decreases` route 1 결정 | 09-06 발신 §5 제안의 답으로 보임 |
| `a3f3241a` value-match lowering / lambda lifting 잔차 해소 | 리타겟 asks **A2** |
| `47783420` 엔진이 EMPTY로 증명한 refinement는 프로그램 결함 | ruling D3 주변 |

→ 전부 **미확인**. 09-08 이후의 30커밋에 대한 통지는 받지 않았다.

## 3. ① 블로커 — **닫혔다** (09-06 인바운드)

`2026-09-06-arith-canonicalisation-landed-false-sat-closed.md`:

- AD1 **`5fe25c3`** — `adsmt-engine/src/solver.rs`(정규화 훅) +
  `adsmt-theory/src/arith.rs`(`canonical_linear`)
- 우리가 보낸 리프로 12파일 **전수 기대대로**: FALSESAT-01..05 `sat` → **`unsat`**,
  closes/ctrl 6건 `unsat` 유지, `unknown-01` 유지
- 원인: disequality는 arith가 `Ignored`로 넘겨 **UF가 받고, UF는 구문 비교** →
  `n + 0`이 `n`과 같은 항이 아니었다. 우리 진단("정규화가 필요한 순간 해석 안 함")은
  맞았고 한 층 아래였다
- 방식: 항등식 테이블이 아니라 **정규형 `Σ cᵢ·xᵢ + c`** — `x+0`/`0+x`/`x*1`/`x-x`와
  **임의 중첩**이 한 규칙. 부분항까지 내려가므로 `f(n+0) = f(n)`도 합동으로 닫힘
- 덤: 우리 프로브 `B-def-linear-mult`(`dbl(k) = k + k`)도 함께 닫힘
- 회귀: false-unsat 0, corpus-triage 29 변경 0, lu-kb 120 중 11 변경 **전부 `sat`→`unsat`**,
  테스트 606 green. LIA 부하 47→2ms, EUF +12%
- 남은 것: **부등식(`n+1 > n`)은 여전히 `unknown`** — 불완전이지 오판 아님.
  adsmt가 우선순위를 물었음(§4)

**결론: 네이티브 리타겟 emit을 막고 있던 유일한 사유가 사라졌다.**
(단, 핀은 재빌드 필요 — §2 + 빌드 캐시 전삭제 완료)

## 4. 우리가 갚아야 할 것 (미발신)

| # | 항목 | 출처 | 비고 |
|---|---|---|---|
| **R1** | 원장 정의 변경 질문 **3건** | 08-30 §3.4 | **진짜 미결.** 08-31 ×2에서 "계속 열려 있음"으로 재확인 |
| **R2** | `--aot-bake` rc 검사 확인 (a) / 변환실패 verdict (b) | 09-08 §1 | **아래 §6에서 실측 완료** |
| R3 | 16커밋 묶음의 버전 번호 결정 | 09-08 §4 | 우리 결정사항. AD1은 rc.42.1 유지 중 |
| R4 | 원장 173 독립 재스윕 + 잃은 3행 확인 | 08-31 | 우리 마지막 검증값은 159 |
| R5 | `#430`(기본-ON false-UNSAT) 코퍼스 노출 판단 | 08-02 ADD / 08-30 §2 | **검증 도장 방향**. 가장 값어치 높은 미결 |
| R6 | ① 종결 ACK + 부등식 우선순위 답 | 09-06 §4 | |
| R7 | ③ `decreases` route 1 결정에 대한 수용 여부 | `81e0f08e` | 통지 미수신, 커밋으로만 확인 |

### 잃은 3행 (08-31, 우리 미검증)

```
fuel-recursion-2/ob13   unsat  5s → unknown 32s   ← 우리가 추적하던 행
seq-vstd-2/ob07         unsat 13s → unknown 25s
seq-vstd-3/ob05         unsat 39s → timeout
```

세 건 다 `OXIZ_NO_ACKERMANN=1`로 기준선 시간에 `unsat` 복귀 →
**손실 전액이 `#434` Ackermann 렘마 귀속**, 타이밍 노이즈 아님.
게이트의 `REGRESSIONS vs PINNED: 0`은 **143-era manifest** 기준이라 이 3건을 못 본다.

## 5. 그들이 갚아야 할 것

- **`2026-09-01` P0 — Isabelle emit이 비일관 이론을 만든다 + cert-replay 구현 스펙.
  회신 없음 (약 8주).** `~/adsmt-contrib/adsmt-emit-isabelle/src/lib.rs:175-182`
- 09-08 이후 30커밋에 대한 통지
- `#430` 랜딩 (08-30 시점 미랜딩, 기본값 노출)
- 데이터타입 case-split false `sat` 잔차 4000쿼리당 7건 (`dt-case-split-false-sat-*-OPEN.smt2`)

## 6. 09-08 §1 확인 — 실측 완료

### (a) `scripts/aot-bake-prelude.sh`는 rc를 검사한다 — **YES**

`scripts/aot-bake-prelude.sh:147-149`:

```bash
if ! "$lu_smt" --aot-bake --aot-include-cdcl --aot-output "$out" "$tmp_bake" 2>/dev/null; then
    echo "error: lu-smt --aot-bake failed" >&2; rm -f "$out"; exit 1
fi
```

→ `rc 11` 거부는 포착되고, 부분 산출물은 `rm -f "$out"`으로 제거되며,
스크립트는 `exit 1`로 **크게 실패**한다. adsmt가 원한 계약 그대로다.

**다만 한 가지 흠**: `2>/dev/null`이 lu-smt의 진단을 삼키므로, 운영자는
"degraded 세션 거부(rc 11)"와 그 밖의 실패를 **구별할 수 없다**.
→ 우리 쪽 개선 항목: 실패 경로에서 stderr를 살리고 rc를 출력할 것. (미착수)

참고로 `:179`의 JIT 트레이스 단계는 **의도적으로 종료코드를 보지 않는다**
(`|| true` + `-s` 게이트). 주석에 이유가 적혀 있다 — lu-smt 종료코드는 verdict를
따르므로(`sat=0 unsat=1 unknown=2`) 유용한 `unsat` 워밍업이 1을 낸다.
(b)의 변경과 충돌하지 않는다.

### (b) 변환 실패가 `unknown` + rc 2를 찍고 세션이 계속된다 — 우리에게 순이득

이전 동작(빈 stdout + rc 11)은 우리 쪽에서 **잘린 transcript**로 보였다.
`unknown` + rc 2는 air의 일반 경로가 그대로 처리한다. 파이프라인 변경 불필요.
`--strict-commands`를 쓰지 않으므로 치명 경로에도 걸리지 않는다.

## 7. 다음 행동 (지시 대기)

1. **회신 보류 중** — 초안: `DRAFT-reply-backlog-closeout.md` (이 디렉터리, 미발신)
2. 재핀은 `4d0d55e`가 아니라 **HEAD(`d0731217`) 기준으로 다시 받는 것**을 권고
3. 빌드 캐시 전삭제 완료 → verus 전체 재빌드 필요
   (`source/target` 17G, `source/target-verus` 712M, `tools/vargo/target` 325M 삭제)
4. ① 종결로 **네이티브 리타겟 emit의 블로커가 해제됨** — 착수 가능
