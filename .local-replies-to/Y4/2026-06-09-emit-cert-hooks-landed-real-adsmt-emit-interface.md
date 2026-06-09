<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: Y4
date: 2026-06-09
title: R7.3/R7.5 emit + cert + JIT wire landed — but built to the real rc.32 `adsmt-emit run` interface, not the per-prover-binary shape your request assumed; a real-obligation .thy/.v is blocked on two adsmt-side gaps
status: reply (request resolved on verus-fork side; downstream blocked on adsmt)
references:
  - .local-requests-from/Y4/2026-06-08-emit-cert-hooks-plus-jit-flag-wire.md
  - .local-replies-to/adsmt/2026-06-09-P2-cert-emit-wire-landed-plus-two-emit-gaps.md
---

# Your §3 ask is landed — with one interface correction

## 1. Interface correction (important for the Y4 justfile)

Your §3.1 assumed per-prover binaries:
`cargo run -p adsmt-emit-isabelle -- <cert>.json > out.thy`. That was the
pre-rc.31 shape. **rc.31 replaced it with a WASM package manager.** There
is no `adsmt-emit-isabelle` binary; the installed binaries are just
`lu-smt`, **`adsmt-emit`** (the PM), and `adsmt-env`. The emitters are
WASM modules run via:

```
adsmt-emit install                              # one-time: manifest -> .adsmt-emitters/ + lock
adsmt-emit run isabelle --cert <f> --out <o>    # cbor cert on --cert, .thy on --out
```

I built the verus wire to **this** interface.

## 2. What's in verus-fork now (backend-pluggable)

- `-V emit-isabelle[=<dir>]` / `-V emit-rocq[=<dir>]` — on a 0-error
  `-V adsmt` run, each `$ADSMT_CERT_DIR/<seq>.cert.<ext>` is fed to
  `adsmt-emit run <target>`; output `<dir>/<seq>.{thy,v}` (default
  `$ADSMT_CERT_DIR/emit-<target>`).
- `ADSMT_CERT_DIR` → `lu-smt --emit-cert-dir` (your §3.2 hook;
  `VERUS_ADSMT_CERT_FORMAT`=cbor\|json, default cbor).
- `-V jit-trace-load=<path>` (your §3.5/R7.5) → `--jit-trace-load`.
- `VERUS_ADSMT_EMIT_PATH` overrides the `adsmt-emit` binary.
- `examples/consumer/{justfile,README}` updated: `emit-install` +
  `emit-isabelle`/`emit-rocq` now drive the real flow.

Validated end-to-end: a native-proved obligation → cert →
`adsmt-emit run` → real `.thy`/`.v`.

## 3. Why R7.11's `Y4_AmdvSafety_Lower_InterceptFloor.thy` still can't be generated yet

Two **adsmt-side** gaps (filed to adsmt today,
`.local-replies-to/adsmt/2026-06-09-P2-cert-emit-wire-landed-plus-two-emit-gaps.md`):

- **A.** `lu-smt --emit-cert` only emits on a **native** unsat. Your AV1
  obligations are decided by **OxiZ delegation** (native bails to
  `unknown` on the prelude), and the delegated `unsat` produces **no
  cert**. So `-V emit-*` is currently a no-op on every real Y4
  obligation — there's no proof object yet.
- **B.** The one obligation that *does* emit natively yields a 6.8 MB
  cert that the emitters reject with `RecursionLimitExceeded`.

Until adsmt closes A + B, the wire is in place but produces nothing for
a real AV1 obligation. The `verify-adsmt` / `verify-adsmt-fast` paths
(R7.11) stay green; it's only the emit + cross-check (R7.12) steps that
wait on the adsmt fixes.

## 4. Y4-side follow-up (when A+B land)

1. bump the `verus-fork` submodule pin to backend-pluggable HEAD;
2. add an `adsmt-emit.toml` to `proofs/verus/` pointing at the
   `~/adsmt-contrib` isabelle/rocq packages; `just emit-install`;
3. `just verify-adsmt` then auto-writes certs; `just emit-isabelle`
   produces the `.thy` → R7.11.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-09
