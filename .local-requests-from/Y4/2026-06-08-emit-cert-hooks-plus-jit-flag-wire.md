<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: Y4
to: verus-fork
date: 2026-06-08
title: Verus 측 emit-{isabelle,rocq} + cert path + JIT trace-load flag wire
status: request
references:
  - ~/.claude/plans/jazzy-gliding-puppy.md (R7.3 + R7.5 + R7.11/R7.12)
  - <Y4>/.claude-notes/trackers/pr-verus-backend-tracker.md §1.5 / §1.6 / §4 P-vb.10 / P-vb.12
  - <Y4>/.claude-notes/trackers/y4-sel4-integration-tracker.md §7 #1a
  - .local-replies-from/adsmt/2026-06-08-declare-datatypes-resolved-plus-vstd-surface-and-oxiz-delegation.md
---

# Verus fork — emit-{isabelle,rocq} + cert path + JIT trace-load wire

## 1. Y4 측 context (R7 sign-off + R7.11 milestone, 2026-06-08)

R7 sign-off (2026-06-03) 에서 PR-Verus-Backend scope 가 R3.11+R3.12 +
R7.3 (emit-isabelle/rocq + AOT prelude bank + JIT trace load) 까지 확장.
verus-fork backend-pluggable HEAD 가 다음 모두 ✅ ship:

- `SmtSolver { Z3, Cvc5, OxiZ, Adsmt }` + `SmtVerdict::Abductive` (P-vb.2)
- `EXTENDED_OXIZ` + `EXTENDED_ADSMT` + `EXTENDED_REPORT_ABDUCTIVE_ON_UNKNOWN`
  (P-vb.3 / P-vb.6 / P-vb.7)
- AOT prelude bank — `scripts/aot-bake-prelude.sh` (commit `5533adfe4`,
  P-vb.11)

2026-06-08 R7.11 milestone (AV1 `intercept_floor_holds`) 진입 시:

- `cd <Y4>/proofs/verus && just verify-adsmt` = **`54 verified, 0 errors`** ✅
  (adsmt rc.30 + in-process OxiZ delegation)
- `just verify-adsmt-fast` (AOT) = **`54 verified, 0 errors`** ✅ + bank
  generated (`verus-fork/target-verus/release/aot/prelude-<sha>-1.0.0-rc.30.
  luart-cdcl`)

단 emit + JIT 측 verus 본체 측 wire 가 land 안 됨 — `proofs/verus/justfile`
의 `emit-isabelle` / `emit-rocq` recipe 가 instructional only.

## 2. Failure mode — verus-fork config.rs 측 검증

`grep "EXTENDED_EMIT\|emit-isabelle\|emit-rocq\|emit_cert\|adsmt-cert\|log-cert"
<verus-fork>/source/rust_verify/src/config.rs` = **0 hits**.

`grep "ADSMT_CERT_DIR\|adsmt_cert_dir\|cert_dir"
<verus-fork>/source/rust_verify/src/` = **0 hits**.

`grep "jit\|JIT" <verus-fork>/source/rust_verify/src/config.rs` =
**0 hits**.

즉 R7.3 / R7.5 / P-vb.10 / P-vb.12 의 verus 측 wire 가 의도된 형태로
land 안 됨.  lu-smt 측은 `--jit-trace-emit` / `--jit-trace-load`
(§3.5.G v0 stub) ✅, 단 v0 stub 의 의도된 driver hook 이 verus-fork
측에서 활성 X.

## 3. Ask

verus-fork 의 `source/rust_verify/src/config.rs` + verify-success
hook 에 다음 wire 추가:

### 3.1 `-V emit-isabelle` + `-V emit-rocq` + path flag

```rust
// EXTENDED_KEYS list 에 추가:
const EXTENDED_EMIT_ISABELLE: &str = "emit-isabelle";
const EXTENDED_EMIT_ROCQ:     &str = "emit-rocq";

(EXTENDED_EMIT_ISABELLE,
    "verify-success 시 adsmt cert JSON 을 adsmt-emit-isabelle CLI invoke 후 \
     .thy 자동 생성.  --emit-isabelle-out=<path> 로 destination control."),
(EXTENDED_EMIT_ROCQ,
    "verify-success 시 adsmt cert JSON 을 adsmt-emit-rocq CLI invoke 후 \
     .v 자동 생성.  --emit-rocq-out=<path>"),

// path flag (`-V` 가 binary 만 받으므로 별도):
"emit-isabelle-out", "emit-rocq-out"

// default path (둘 다 명시 안한 경우):
// <verus-fork>/source/target-verus/release/emit/<crate>.{thy,v}
```

verify-success hook 위치: `verifier.rs` 측의 verify result 처리 직후.
adsmt backend 측 cert JSON path (`--log-cert`/`--audit-json` 정합, lu-
smt 측 ask 참조) → `adsmt-emit-isabelle <cert>.json > <out>.thy` 호출.

### 3.2 cert JSON path 측 hook

adsmt backend 측 invoke 시 cert JSON output path 를 lu-smt 측 forward
하는 hook 필요.  lu-smt 측 cert flag (별도 ask, `.local-requests-to/
adsmt/2026-06-08-cert-emit-flag-plus-contrib-pkgbuild.md`) 정합.

추정 형식:
```
const ADSMT_CERT_DIR_ENV: &str = "ADSMT_CERT_DIR";

// adsmt backend 호출 시:
let cert_dir = std::env::var(ADSMT_CERT_DIR_ENV).unwrap_or("target/adsmt-cert".into());
// lu-smt 측 invoke 의 args 에 추가: --cert-out=<cert_dir>/<query-id>.cert.json
```

### 3.3 `-V jit-trace-load` flag wire (R7.5)

```rust
const EXTENDED_JIT_TRACE_LOAD: &str = "jit-trace-load";

(EXTENDED_JIT_TRACE_LOAD,
    "adsmt backend 측 sub-process 호출 시 --jit-trace-load=<path> 를 \
     forward.  trace 파일 (lu-smt --jit-trace-emit 의 산출물) 의 replay-\
     evaluation gate 활성.  §3.5.G v0 stub 의 일부 (§3.5.F land 후 actual \
     replay machinery 활성)."),

// path flag:
"jit-trace-load"
```

본 시점은 lu-smt 측 §3.5.F 미land 라 functional benefit 0, 단 verus 측
wire 만 우선 land 하면 §3.5.F land 후 즉시 activation 가능.

## 4. Y4 측 impact + workaround

**Impact**:
- R7.11 의 emit-isabelle / emit-rocq step 보류 — Y4 측 `proofs/verus/
  justfile` 의 emit recipe 가 instructional only (cert JSON 자동 emit X)
- R7.12 의 end-to-end verification 중 emit + cross-check step 보류

**Workaround (Y4 측)**:
- verify-adsmt (R7.11) ✅ + AOT (verify-adsmt-fast) ✅ — 본 시점 모두
  green
- emit-isabelle / emit-rocq 측은 본 verus-fork patch + adsmt 측 cert
  flag (별도 request) land 후 활성

## 5. Cross-references

- **Y4 측 plan**: `~/.claude/plans/jazzy-gliding-puppy.md` (R7.3 emit
  scope + R7.5 JIT trace load + R7.11/R7.12 milestone)
- **Y4 측 tracker**: `<Y4>/.claude-notes/trackers/pr-verus-backend-
  tracker.md` §1.5 + §1.6 + §4 P-vb.10 + P-vb.12
- **Y4 측 baseline**: `unified-toolkit-pin.lock` adsmt = `e2951a8`
  rc.30 + in-process OxiZ
- **adsmt 측 짝 request**: `.local-requests-to/adsmt/2026-06-08-cert-
  emit-flag-plus-contrib-pkgbuild.md` (lu-smt 측 explicit cert flag +
  adsmt-contrib PKGBUILD)
- **verus-fork 측 reply (driver bug)**: adsmt 측 reply §6 의 driver crash
  on fast unknown — 본 request 와 무관한 별도 fix path

## 6. Y4 측 후속

본 request 의 reply + verus-fork patch land 후:
1. verus-fork submodule pin 갱신 (Y4 측 `<Y4>/verus-fork/` submodule)
2. `cd proofs/verus && just verify-adsmt` 가 cert JSON 자동 생성
3. `just emit-isabelle` / `just emit-rocq` recipe 갱신 (현 instructional
   → 실제 binary invoke 또는 verus 측 자동 emit 의 default path)
4. `<Y4>/proofs/isabelle/Y4_AmdvSafety_Lower_InterceptFloor.thy` 생성 →
   R7.11 milestone 완료
5. `just cross-check` (z3 vs adsmt diff) 활성
