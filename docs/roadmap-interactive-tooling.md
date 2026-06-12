<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Roadmap — interactive tooling for verus-fork (LSP analyzer · extension · workbench template)

> Status: **roadmap / design** (no implementation yet). Captures the
> decisions from the 2026-06-12 discussion. Sequenced *after* the core
> backend work converges (adsmt hardening, A2 theory-aware abduction,
> P2 cert-emit); placed here so the interface contracts are fixed early.

## 0. Framing — this is the delivery layer, not a side quest

The features that distinguish `verus-fork` from upstream Verus are almost
all ones that **only pay off interactively**:

- **verify-or-explain / abductive code-actions (A2c)** — "this obligation
  isn't proven; it would hold if you added `requires x > 0` (line 42)",
  surfaced as a quick-fix. On the CLI it's a stderr line; in an editor
  it's the headline UX. The abductive work (A2a/A2b/A2c) *is* an editor
  feature; this roadmap is its home.
- **pluggable backend selection** (`-V z3|cvc5|oxiz|adsmt`) — a status-bar
  toggle / per-project setting.
- **differential cross-check** (z3 vs adsmt) — "verify with both, flag any
  verdict divergence inline" = a soundness audit surfaced in the gutter.
- **cert-emit** (P2) — "export this proof to Isabelle/HOL or Rocq" command,
  the Y4-unification bridge made one click.

So interactive tooling is where the backend investment becomes visible.
The data plumbing partly exists already: the `--output-json` / jsonl
reporter (P-vb.6/7) is the structured feed a language server consumes.

## 1. Architecture — three layers, one heavy investment

```
Verus analyzer (LSP server)              ← the heavy, once-only investment
  fork of verus-analyzer; dual-target (verus-fork AND upstream verus)
        │
        ├─ Open VSX extension (thin client)     ← portable CAPABILITY
        │     runs in any VSCode-API host: VSCode, Theia, Cursor, …
        │
        └─ Workbench template (Theia product shell)  ← custom PRODUCTS
              bundles the extension + cross-tool panels; Y4's internal
              dev workbench is an instance of this template
```

**Rule that keeps "all three" ≈ 1.x× cost, not 3×:** all Verus/verus-fork
logic lives **once** in the analyzer (LSP). The extension is a thin
client; the workbench is a product shell. Neither re-implements solver
logic.

## 2. Component A — the Verus analyzer (LSP server)

**Decision: fork directly from upstream `verus-analyzer`** (the existing
rust-analyzer-based Verus LSP), rather than build from scratch or
maintain a thin separate layer. Rationale: it already provides the
general IDE features (parse, goto, hover, completion) that we should not
re-implement; we add the verus-fork-specific surface on top.

**Hard requirement: dual-target — support BOTH verus-fork and upstream
Verus.** The analyzer must detect which `verus` binary the workspace
points at and **degrade gracefully**:

- a *capability probe* at startup (e.g. parse `verus --help` for the
  `-V adsmt` / `emit-isabelle` / `request-abductive-on-unknown` extended
  keys, or a dedicated `verus --capabilities` we may add) → a
  `BackendCapabilities` record;
- features gate on capabilities: against **upstream verus** the analyzer
  is a normal Verus LSP (verify, diagnostics); against **verus-fork** it
  additionally lights up backend selection, cross-check, cert-emit, and
  the abductive code-actions. No hard dependency on fork-only features —
  they're feature-detected, never assumed.
- this also future-proofs the fork merging upstream: the same analyzer
  serves both, so users don't pick an editor tool by which Verus they run.

**Fork-specific LSP surface (feature-gated):**

| capability | LSP feature |
|---|---|
| `-V adsmt/cvc5/oxiz/z3` | backend selection (workspace/file setting + a command) threaded into the verify invocation |
| `--output-json` jsonl | structured diagnostics (the verdict + spans feed; already emitted) |
| cross-check | a "verify with z3 **and** adsmt, diff verdicts" command → divergence diagnostic (soundness signal) |
| cert-emit (P2) | "emit Isabelle/Rocq cert" code-action / command per discharged obligation (drives `adsmt-emit run`) |
| abductive (A2) | **code-action** on a not-proven obligation: show the ranked abducts as quick-fixes that insert `requires`/`invariant`/lemma (this is A2c; blocked on the theory-aware abduction request) |
| AOT bank / JIT | mostly transparent; optionally a "warm the AOT bank" command (`scripts/aot-bake-prelude.sh`) |

**Sync risk (call it out):** a verus-analyzer fork inherits the
rust-analyzer-fork maintenance burden (tracking upstream). Mitigation:
keep the verus-fork delta **small and isolated** (a `backend`/capabilities
module + the gated features), so rebases against upstream verus-analyzer
stay mechanical.

## 3. Component B — the Open VSX extension (thin client)

A single extension, published to **Open VSX**, that:

- speaks to the Component-A LSP;
- contributes the commands/settings/views for the fork features (backend
  toggle, cross-check, cert-emit, abductive quick-fixes);
- since Theia implements the VSCode extension API, **the same artifact
  runs in VSCode, Theia, Cursor, etc.** — no per-host build. (This is the
  decision that collapses "VSCode vs Theia" at the extension layer.)

Single-tool *views* that make sense inside a host editor (e.g. a
cert-preview webview) ship **here**, so plain-VSCode users get them too.
**Cross-tool** panels do **not** live here (a host-embedded extension
can't own the window layout) — they're the workbench's job (§4).

## 4. Component C — the workbench template (Theia product shell)

A **reusable Theia-based scaffold** for building custom, branded
verified-systems workbenches. Not a single product — a *template* that:

- bundles the Component-B extension (so it inherits every Verus feature
  for free);
- provides **cross-tool panel slots** the plain extension can't: a layout
  showing the Verus proof, the `adsmt-cert`, and the Isabelle/HOL · Rocq
  emit side-by-side — i.e. the Y4-unification thesis made *visible*
  (`Verus → adsmt-cert → ITP`, merging into the same logic as the seL4
  Isabelle proofs);
- exposes extension points for product-specific views, branding, and
  packaging (desktop via Electron / web).

**Decision: Y4's internal development workbench is built *from* this
template** (an instance), not as a bespoke app — so the template is
dog-fooded and stays general. Other consumers (a published "Verus
verified-systems IDE", a course/lab environment) instantiate the same
template with their own panels/branding.

**Why the workbench specifically matters for Y4:** the project's whole
claim is "unify seL4 (Isabelle) + new Verus code through adsmt." The plain
extension lives *inside* someone else's editor and can't compose
cross-tool views; the workbench is where that integration becomes a
single, demonstrable product — the embodiment of the thesis, and the
natural demo for "why this project."

## 5. Decisions captured (2026-06-12 discussion)

1. **Three layers, not alternatives**: analyzer (capability) → extension
   (portable client) + workbench (product), with logic only in the
   analyzer.
2. **Analyzer = fork of `verus-analyzer`**, **dual-target verus-fork +
   upstream verus** (feature-detected, graceful degradation). Not a
   from-scratch LS, not a thin non-fork layer.
3. **One extension, Open VSX** — runs in VSCode and Theia directly (Theia
   supports VSCode extensions), so no exclusive editor choice.
4. **A workbench *template*** (Theia) for custom workbenches; **Y4's
   internal workbench instantiates it**.
5. **Cross-tool panels = workbench-only**; single-tool views (e.g. cert
   preview) may also ship as extension webviews. (Keeps the workbench's
   "integrated product" value while keeping the extension useful.)

## 6. Dependencies & sequencing

- **Prereqs mostly met**: stable `-V` backend surface, `--output-json`
  jsonl reporter, cert-emit pipeline (P2), AOT bake script. The interface
  contracts the LSP consumes already exist.
- **A2c (abductive code-actions) is blocked** on the theory-aware
  abduction request (`.local-requests-to/adsmt/2026-06-12-request-theory-aware-abduction-search.md`).
  So phase the LSP "A2c-last": ship the non-abductive features first.
- **ROI scales with core stability** — every interactive feature sits on
  the backend work; build the tooling track as the core (adsmt hardening,
  A2, P2) converges, not before.

Suggested phasing:

```
Phase 1  analyzer fork + capability probe + dual-target skeleton
         → verify-on-save, jsonl diagnostics, backend toggle
Phase 2  cross-check command + cert-emit code-action (extension + LSP)
Phase 3  Open VSX packaging (VSCode + Theia validated)
Phase 4  workbench template (Theia shell + cross-tool panel slots)
         → Y4 internal workbench as the first instance
Phase 5  A2c abductive quick-fixes  (gated on theory-aware abduction)
```

## 7. Open questions

1. **Capability probe shape** — parse `--help`, or add a first-class
   `verus --capabilities` (machine-readable) to verus-fork? The latter is
   cleaner and is a small verus-fork addition we control.
2. **verus-analyzer upstream relationship** — track their branch and
   rebase, or vendor a pinned snapshot + periodic merges? (Affects the
   sync-burden mitigation in §2.)
3. **Workbench packaging target** — desktop (Electron) first, web first,
   or both? Tied to who the Y4 internal workbench's users are.
4. **A2c surface** — quick-fix that inserts text the user reviews
   (sound, the §3 soundness boundary), with the abduct re-checked +
   marked `assume`-class until proved. Confirm the insertion UX before
   building (no silent proof-state mutation).

— drafted by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
