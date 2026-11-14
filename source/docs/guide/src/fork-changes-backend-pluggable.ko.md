# 교체 가능한 SMT backend (fork)

> **이 페이지는 Verus의 fork를 설명합니다.** `backend-pluggable-beta` 브랜치는 `fip-beta`([업스트림 Verus 대비
> 변경 사항](./fork-changes.ko.md))에 이 페이지의 변경을 더한 것입니다. Verus가 실행할 수 있는 SMT solver 두
> 개(adsmt, OxiZ)와 adsmt에 딸린 옵션들입니다. 영어판은 [여기](./fork-changes-backend-pluggable.md)에 있습니다.
>
> 모두 실험적입니다. 기본 solver는 여전히 Z3입니다. adsmt나 OxiZ의 결과가 Z3의 결과를 대신하지는 않습니다.

## solver

업스트림 Verus는 기본으로 Z3를, `-V cvc5`로 cvc5를 실행합니다. 이 브랜치는 다음을 더합니다.

| 옵션 | solver | 실행 파일 | 경로 지정 | Verus가 기대하는 버전 |
|---|---|---|---|---|
| `-V oxiz` | OxiZ, Rust로 다시 구현한 Z3 | `oxiz` | `VERUS_OXIZ_PATH` | `0.2.4` |
| `-V adsmt` | adsmt, 귀추-연역(abductive-deductive) solver | `lu-smt` | `VERUS_ADSMT_PATH` | `1.0.0-rc.42.1` |

Verus는 실행 파일을 Z3, cvc5와 같은 방법으로 찾습니다. 변수가 있으면 그 경로를, 없으면 실행 파일 이름을
씁니다. solver의 버전도 Z3, cvc5처럼 확인합니다. 기대하는 버전은 `tools/common/consts.rs`에 있습니다.

`-V adsmt`일 때 SMT 질의가 한 가지 달라집니다. 피연산자가 48개보다 많은 `(distinct ...)`를 쌍별 부등식으로
풀어 씁니다. 이 처리를 넣을 당시 adsmt의 native 엔진은 해석되지 않은 sort를 원소 52개 정도의 유한 domain으로
모델링했습니다. 그래서 더 큰 `distinct`가 있으면(Verus의 prelude에 fuel 식별자에 대한 것이 하나 있습니다) 모든
질의가 unsat이 되었고, 모든 함수가 "검증"되었습니다. 이 한계는 `source/air/Cargo.toml`의
`[package.metadata.adsmt] distinct_max_arity`이고, 빌드할 때 읽습니다. 다른 solver에는 질의가 그대로 갑니다.

## 네 번째 판정: abductive

업스트림 Verus에서 SMT 질의의 결과는 셋입니다. valid, invalid(모델과 함께), unknown입니다. adsmt는 넷째
결과를 낼 수 있습니다. *abductive*는 질의를 valid로 만들 가설 후보들을 순위대로 매긴 목록입니다. Verus는 이를
검증 실패로 보고하고, 후보들을 오류 메시지에 넣습니다. 옵션 두 개가 이를 다룹니다(다른 solver에서는 둘 다
아무 일도 하지 않습니다).

* `-V report-abductive-on-unknown`: adsmt가 abductive 판정을 내면, 후보들을 JSON 출력(`--output-json`, 필드
  `abductive_candidates`)에도 넣습니다.
* `-V request-abductive-on-unknown`: adsmt가 질의를 검증하지 못하면, 빠진 가설을 찾아 달라고 요청하고
  (verify-or-explain), 그 결과를 abductive 판정으로 보고합니다.

## 인증서와 증명 보조기

adsmt는 증명한 질의마다 인증서를 쓸 수 있습니다. 이 브랜치에서는 다음과 같습니다.

* `ADSMT_CERT_DIR=<dir>`이면 Verus는 adsmt에 `--emit-cert-dir <dir>`을 넘깁니다. adsmt는 증명한 질의마다
  인증서를 하나씩 씁니다. 형식은 `VERUS_ADSMT_CERT_FORMAT`(`cbor` 또는 `json`)으로 고르고, adsmt의 기본값은
  `cbor`입니다.
* `-V emit-isabelle[=<dir>]`, `-V emit-rocq[=<dir>]`: 오류 없는 `-V adsmt` 실행 뒤에, `ADSMT_CERT_DIR`의 각
  인증서를 Isabelle/HOL theory나 Rocq 파일로 바꿉니다. `adsmt-emit run isabelle`(또는 `rocq`)을 실행합니다.
  기본 출력 디렉터리는 `$ADSMT_CERT_DIR/emit-isabelle`(또는 `emit-rocq`)입니다. `adsmt-emit` 실행 파일은
  `VERUS_ADSMT_EMIT_PATH`로 지정합니다. `adsmt-emit`과 그 emitter가 설치되어 있어야 합니다.

  **알려진 문제, 고쳐지지 않음:** Isabelle emitter는 인증서의 가정을 모두 공리로 씁니다. 반박에 의한 증명에서
  그 가정들에는 부정한 목표가 들어 있고, 모두 함께는 충족될 수 없습니다. 그래서 emitter가 쓰는 theory는
  모순이고, 어떤 명제든 증명합니다. adsmt에 보고했습니다. 고쳐지기 전까지 emit된 theory는 무엇이 성립한다는
  근거가 되지 못하고, 다른 개발에 가져다 쓰면 안 됩니다.

## 그 밖의 adsmt 옵션

* `-V emit-lukb`: 각 질의를 `.lukb` 파일(adsmt 자체의 입력 언어)로도 로그 디렉터리(`--log-dir`, 기본값은
  `.verus-log`)에 씁니다. 아직 표현할 수 없는 구성은 `#` 주석이 됩니다. `.lukb` 파일은 기록일 뿐이고, 판정은 여전히 SMT-LIB
  질의에서 나옵니다.
* `-V jit-trace-load=<path>`(또는 `VERUS_ADSMT_JIT_TRACE`)와 `VERUS_ADSMT_AOT_LUART`: replay trace와 미리
  컴파일한 prelude를 adsmt에 넘깁니다(`--jit-trace-load`, `--aot-load`). adsmt가 답하는 속도를 바꾸려는
  것이고, 답 자체를 바꾸려는 것이 아닙니다. 둘 다 `scripts/aot-bake-prelude.sh`로 만듭니다.
* **`verus.toml`과 adsmt의 manifest.** `-V adsmt`일 때 `ADSMT_CAS_MANIFEST`가 설정되어 있지 않으면, Verus는 이
  변수를 가장 가까운 `verus.toml`로 설정합니다. 그러면 adsmt가 그 파일의 `[adsmt.cas]` 표를 읽을 수 있습니다.
  현재 디렉터리나 그 위에 `adsmt.toml`이 있으면 그것이 우선합니다. Verus는 경로만 넘기고 표를 읽지는
  않습니다.

## 저장소에 더해진 것

* `scripts/`: `aot-bake-prelude.sh`(위 참고), `a2-abduction-regression.sh`(`scripts/a2-fixtures/`의 fixture로
  `-V request-abductive-on-unknown`을 회귀 검사), `snapshot-status.sh`(fork 작업자를 위한 진행 상황
  스냅숏). `justfile`은 첫째와 마지막을 실행하고(`just aot-bake-prelude`, `just status`), fork 자체의 기록
  관리를 위한 recipe도 있습니다. `examples/consumer/`는 이
  fork를 여러 backend와 함께 쓰는 프로젝트를 위한 `justfile`입니다.
* `docs/roadmap-interactive-tooling.md`: backend 위에 올릴 대화형 도구의 계획입니다.
* `.local-*` 디렉터리와 `.claude-memories/`에는 작업 메모와 adsmt 프로젝트와 주고받은 기록(요청, 회신, 재현
  사례)이 있습니다. Verus의 동작에는 영향이 없습니다.

## `backend-pluggable-inline-beta`

`backend-pluggable-inline-beta` 브랜치는 `backend-pluggable-beta`에 *inline 증명*의 설계 메모를 더한 것입니다.
inline 증명은 다른 언어로 된 증명 조각(자체 논리와 backend를 고른 SMT 질의, MaxSAT/MaxSMT, ASP, 대화형 증명기)을
Verus 증명 안에 끼워 넣는 것입니다. 코드에 inline assembly를 끼워 넣는 것과 비슷합니다. 메모는
`.local-backlog/inline-proof/`에 있습니다. 아직 논의 단계이고, adsmt의 입력 언어가 정해지기를 기다리고 있습니다.
이 브랜치는 Verus를 바꾸지 않습니다.
