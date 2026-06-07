---
name: y4-unified-verification-motivation
description: "Why the verus-fork adsmt-backend work exists — Y4's unified formal-verification workflow, with adsmt as the bridge between Verus and Isabelle/HOL"
metadata: 
  node_type: memory
  type: project
  originSessionId: 24e738cd-0992-49fb-980e-fc34d30b6f50
---

The whole `~/verus-fork` adsmt-backend effort (P-vb, §3.x, the rc.7 → rc.28 arc) exists to serve a larger goal in the user's **Y4** project (local `~/Y4/`, remote https://github.com/newsniper-org/y4).

Y4's formal-verification workflow is currently **fragmented**:
- the **seL4 microkernel** Y4 builds on is verified in **Isabelle/HOL**;
- the user's **newly-written code** is verified (partially) in **Verus**.

The user wants to **unify these fragmented verification workflows into one**, with **adsmt as the common verification engine**. The data-flow direction:

```
Verus code → adsmt (SMT query) → verify → adsmt-cert → emit to a proof assistant
                                                          ↓
   ~/adsmt-contrib (testing branch, github.com/newsniper-org/adsmt-contrib):
     - adsmt-emit-isabelle  → .thy (Isabelle/HOL via Isar)
     - adsmt-emit-rocq      → .v   (Rocq/Coq, Ltac2-only)
```

So Isabelle/HOL is on the **emit/output** side (adsmt cert → `.thy`), NOT an input frontend. The unification: Verus code gets verified by adsmt, its cert is emitted to Isabelle, and lands in the same logic the seL4 Isabelle proofs live in.

**How to apply:** the `.luart-cdcl` AOT prelude/axiom bank (§3.1/§3.5) sits on the **input** side — it caches the SMT-LIB axiom set that a frontend (Verus prelude today; any other SMT-LIB-emitting frontend later) feeds adsmt. Keep §3.5.H frontend-agnostic: a script that bakes *any* SMT-LIB axiom set, with an **env-overridable cache location + a sensible default** (the user explicitly wants this), not locked inside Verus-only tooling (vargo). The cache is an adsmt-input optimisation; the Isabelle/Rocq emit side is independent of it. Relates to the §3.1 AOT-prelude-bank design (Y4 `unified-toolkit-pin` §10.6 pins adsmt on the testing channel).
