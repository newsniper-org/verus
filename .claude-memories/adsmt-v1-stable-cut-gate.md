---
name: adsmt-v1-stable-cut-gate
description: "Gate conditions for the adsmt 1.0.0 stable cut — (S.2) Tseitin first, then a full completeness/soundness audit"
metadata: 
  node_type: memory
  type: project
  originSessionId: 24e738cd-0992-49fb-980e-fc34d30b6f50
---

The adsmt **1.0.0 stable** cut (off the current `testing` channel, rc.NN) is gated by the user on two sequential conditions:

1. **(S.2) Tseitin OR-of-AND CNF transform must land.** This is the adsmt-side completeness follow-up to the rc.26→28 soundness arc: `flatten_to_clauses` currently returns `None` on nested OR-of-AND (`(or X (and Y Z))` / `(=> X (and Y Z))`), which the rc.27 (S.1) fix makes *sound* (a contradiction buried inside the opaque structure with no companion flattenable `false` returns `Unknown`, never a false-positive `sat`) but **incomplete** (z3 returns `unsat`). (S.2) introduces Tseitin auxiliary variables (`aux ⟺ (and Y Z)`, then `(or X aux)` is a clean clause) so OR-of-AND flattens cleanly and those contradictions resolve to `unsat`. The cnf.rs comment has anticipated this since "v0.5+".

2. **A full completeness + soundness audit must pass** after (S.2). Not just the existing 951-test suite — an explicit end-to-end check that no verdict path (baseline / `--aot-load` / `--jit-trace-load`, every theory, the opaque/Tseitin boundary) returns `sat` for an unsat set or `unsat` for a sat set, and that the previously-`Unknown` OR-of-AND-buried contradictions now resolve.

**How to apply:** do NOT treat the v1.0 cut as imminent just because the verus backend verifies (that was the §3.5.J finish line, rc.27/28 — functional success on the baseline/AOT/JIT paths, all sound). The stable cut is a *separate, later* milestone gated on (S.2) + the audit + the user's explicit sign-off. Relates to [[y4-unified-verification-motivation]] (adsmt as the common engine bridging Verus + Isabelle/HOL).
