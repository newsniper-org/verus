<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# ⚠ DRAFT — 미발신. 사용자 승인 전까지 `.local-replies-to/`로 옮기지 않는다.

- 근거 설계 메모: `../inline-proof/0001-inline-proof-design.md`. 이 메모는 아직 **논의 단계**다.
- 그래서 이 초안의 항목들은 "구현해 달라"가 아니라 **"이 방향이 adsmt 설계와 맞는지, 그리고 비용이 어떤지"를 묻는
  질의**로 보내는 것이 맞다. 발신 시점과 어조는 사용자가 정한다.

---

```
from: verus-fork
to: adsmt
date: <발신일>
re: adsmt-emit (rc.31~) / lu-kb
title: "inline 증명 구상 — adsmt-emit 계약에 `role` 추가, lockfile 경로 forward, lu-kb 정의/공리 구분에 대한 질의"
status: 질의 (구현 요청 아님)
```

## 배경 (한 단락)

verus-fork가 "inline 증명"을 구상하고 있습니다. Verus 증명 안에 adsmt로 가는 조각을 끼워 넣는 구조입니다.
- 진술은 Verus가 VIR을 거쳐 lu-kb로 만들고(emit-lukb), 본문(증명 방법)만 VIR을 건너뜁니다.
- 본문은 sandbox wasm 패키지("front")가 lu-kb로 바꿉니다.
- adsmt가 풀고 커널이 검사한 인증서를, Verus가 디코드해 결론과 가설을 기대 진술과 대조합니다.
- 새 계약을 만들지 않고 adsmt-emit을 재사용하려 합니다.

## 질의·요청 항목

### R1. adsmt-emit 패키지에 `role` 필드 (하위 호환 확장)

- frontmatter에 `role`을 추가합니다. 기본값 `"emitter"`는 현재 의미 그대로입니다. 새 값 `"front"`는 진술, 본문, 바인딩
  레코드(CBOR)를 입력으로 받아 lu-kb 텍스트를 출력합니다.
- 런타임(`emit(&[u8])`, stdin/stdout, 종료 코드 0/2/3)은 이미 바이트 일반적이라 그대로 쓸 수 있을 것으로 봅니다.
  맞는지 확인을 부탁드립니다.
- 계약 버전 올림(`0.1.0` → `0.2.0`?)의 범위와, front 입력 레코드의 스키마를 어디에 둘지(`adsmt-emit-contract`?)를 묻습니다.

### R2. 계약 문서의 규범 정리

- `wit/emitter.wit` 주석은 *wasm32-wasip2 component, cert-json 문자열*을 말합니다.
- 실제 런타임은 *wasip1 command, CBOR 기본(path A)*입니다.
- 역할을 추가하기 전에 어느 쪽이 규범인지 정리되면 좋겠습니다.

### R3. lockfile 경로 forward와 `--locked`

- verus-fork는 `verus.toml`의 매니페스트 내용을 adsmt-emit에 forward하려 합니다(`[adsmt.cas]` → `ADSMT_CAS_MANIFEST`와
  같은 방식).
- 저장소 경로는 `ADSMT_EMIT_STORE`가 이미 있습니다. **lockfile 경로를 지정하는 변수**도 필요합니다. Verus의 cwd는 호출
  방식에 따라 달라지기 때문입니다.
- lockfile이 없으면 adsmt 쪽이 생성하는 동작은 그대로 좋습니다. 여기에 더해, CI용으로 **lockfile이 없거나 매니페스트와
  맞지 않으면 생성하지 않고 실패하는 모드**(cargo `--locked`와 같은 것)를 요청합니다.
- 원래의 `adsmt-emit.toml`과 forward된 매니페스트가 함께 있을 때의 우선순위를, CAS 쪽 규칙("native가 이긴다" + 경고)과
  맞추는 데 이견이 있는지 묻습니다.

### R4. lu-kb의 정의/공리 구분을 문법 수준에서

- inline 본문(front 출력)에는 공리를 허용하지 않거나, 허용하더라도 `trusted`로 따로 세려 합니다.
- 이를 Verus가 기계적으로 강제하려면 lu-kb에서 정의적 확장과 공리의 구분이 **문법 수준에서** 드러나야 합니다.
- 더 엄격하게 구분할 예정이라고 들었습니다. 그 결과가 문법 수준이 될지 묻습니다.

### R5. 인증서의 결론과 가설을 외부에서 대조할 수 있는지

- Verus는 adsmt-cert를 serde로 디코드해 다음을 대조하려 합니다.
  1. 결론이 기대 진술과 α-동치인가.
  2. 가설이 선언한 것 안에 드는가.
  3. `Assumed` / `Theory` / 불투명 증인(예: `oxiz-delegation`) 단계가 있는가.
- 기대 진술은 Verus가 보낸 lu-kb를 adsmt가 elaboration한 `Term`입니다. 그래서 **Verus가 보낸 진술의 elaboration 결과를
  인증서와 함께(또는 인증서 안에) 돌려받을 수 있는지** 묻습니다.
- 그리고 위 3의 단계 종류를 안정적으로 식별할 수 있는 필드가 있는지 묻습니다. 계약 동결(v0.23 phase 1) 범위 안인지도
  궁금합니다.
