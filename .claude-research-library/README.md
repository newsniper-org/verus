# Finite Axiomatization for Higher-Order Logic — A Research Library

*Assembled for the Verus + seL4 unification effort ("Y4"). Verus's spec language models a set of element-type `A` as a predicate: `'a set ≡ (A ⇒ bool)`, i.e. `ISet<A> { set: spec_fn(A)->bool }` — the Isabelle/HOL model. This library maps the surrounding metamathematical and theorem-proving landscape.*

---

## 1. The Central Thesis

**Finite axiomatization of set theory is, in its classical form, a FIRST-ORDER device whose only job is to eliminate comprehension SCHEMAS.**

First-order ZFC is not finitely axiomatizable (assuming consistency): its Separation and Replacement axioms are each an *infinite schema* — one axiom instance per defining formula — and the Lévy–Montague reflection theorem shows no finite subtheory can recover the whole (a finite fragment would have a set model, hence prove `Con(ZFC)`, contradicting Gödel's second incompleteness theorem).

The famous **finite axiomatization of NBG** (von Neumann–Bernays–Gödel) is precisely a trick to *fold that infinite first-order schema into finitely many axioms*. It quantifies over **classes** and supplies a fixed, short list of class-construction (class-existence) axioms — roughly eight, one per logical connective/quantifier/atomic case — out of which every instance of class comprehension is built by induction on formula structure. NBG "yes, finitely axiomatizable"; ZF "no"; Kelley–Morse (MK, with *impredicative* class comprehension) "no" again.

**In higher-order / second-order logic there is no comprehension schema to eliminate in the first place.** Comprehension is a *single second-order axiom* quantifying over predicates. In typed higher-order logic (Church's simple type theory, the basis of HOL / Isabelle/HOL), it is delivered even more cheaply: by *typed lambda-abstraction* itself. A "set of `A`" simply *is* a term of type `A → bool`; the binding mechanism that forms it is the lambda, and the conversion rules are the comprehension principle. So the schema "collapses" to one construct for free — there is nothing to axiomatize away.

This library collects the systems and literature where finite axiomatization "works for HOL": the metamathematics that makes NBG finite and ZF not (§1), the genuinely second-order/HOL set theories where the schema collapses and quasi-categoricity appears (§2), the practical engineering of set theory inside HOL theorem provers (§3), simple type theory and why one typed comprehension suffices (§4), and the finitely-presented structural/categorical alternatives — ETCS, topos theory, Tarski–Grothendieck, Egal (§5).

---

## 2. The Thematic Sections

| File | Question it answers |
|---|---|
| **01-finite-axiomatizability-metamath.md** | *Which set theories are finitely axiomatizable in FOL, which are not, and exactly why?* The NBG mechanism (von Neumann → Bernays → Gödel → Mendelson), the reflection theorem (Lévy, Montague, Kreisel) proving ZF and MK are NOT finitely axiomatizable, conservativity, and the parallel NF-collapse (Hailperin). This is the FOL baseline the rest contrasts against. |
| **02-second-order-set-theory.md** | *When you move to genuine second-order/HOL semantics, what happens to the schema and what do you gain?* Zermelo's quasi-categoricity, second-order ZFC and the Separation/Replacement schema collapse (Shapiro, Väänänen), the GBC → KM second-order comprehension-strength hierarchy (Gitman, Hamkins, Williams), and internal categoricity in Henkin semantics. |
| **03-hol-and-set-theory-in-theorem-proving.md** | *How is set theory actually built inside (or alongside) a typed-HOL prover?* HOL-ST / HOLZF / ZFC_in_HOL (Gordon, Obua, Paulson), Isabelle/ZF, the HOL↔set-theory translations (Krauss–Schropp, Guilloud et al.), HOTG/Egal interoperability, the consistency of Isabelle/HOL's definitional core, and Metamath as the schema-keeping foil. The direct precedent layer for Y4. |
| **04-simple-type-theory-and-typed-comprehension.md** | *Why does ONE typed comprehension principle suffice, model-theoretically?* Church's STT, the Ramsey/Russell prehistory, Henkin general models and completeness, Andrews's Q0, and HOL's set-theoretic standard semantics (Pitts). This is the "why there is nothing to finitely-axiomatize-away" core. |
| **05-categorical-and-structural-alternatives.md** | *What do finitely-presented, schema-free structural foundations look like?* Lawvere's ETCS, topos theory as typed HOL (Bell, Mac Lane–Moerdijk, Lambek–Scott), the material/structural dictionary (Shulman, Osius), and first-order Tarski–Grothendieck. The structural counterpart of the HOL "one axiom" move. |
| **06-typed-second-order-class-theories.md** | *Which foundations are simultaneously typed, second-order/impredicative, AND class theories — the three-axis intersection?* The key calibration that plain MK/GBC/KM is second-order + class but UNTYPED (one global ∈), versus the genuine FULL hits: type-theoretic universe hierarchies as class theory (Rocq `Ensemble A = A → Prop` with impredicative Prop — the Y4 emit target; Werner/Barras Coq↔ZF; Lean/CIC universes; HoTT resizing — Voevodsky, Uemura), categorical algebraic set theory / categories of classes (Joyal–Moerdijk, Awodey–Butz–Simpson–Streicher, Streicher universes), MK-in-Coq (Chen–Yu), the sorted-MK relatives (urelements: Hamkins–Yao, Yao; hyperclasses: Antos–Friedman), and the "class = higher type" philosophy (Linnebo–Rayo, Florio–Shapiro). *(Added as an extension; answers a follow-up question rather than the core finite-axiomatization thesis.)* |

---

## 3. CORE CANON — Curated Reading List

The seminal / must-have works, in a suggested reading order, each with a one-line why.

1. **von Neumann, *Eine Axiomatisierung der Mengenlehre* (1925)** — ground zero: the first finite axiomatization, folding the Replacement schema into class/function axioms via limitation-of-size. *(§1)*
2. **Bernays, *A System of Axiomatic Set Theory* I–VII (1937–1954)** — the working-out of HOW finitely many class-existence axioms generate all comprehension instances; the engineering of NBG. *(§1)*
3. **Gödel, *Consistency of AC and GCH* (1940)** — the canonical statement of NBG's finite class-existence axioms (the ~8 Gödel operations) in the service of L. *(§1)*
4. **Mendelson, *Introduction to Mathematical Logic*, Ch. 4 (1997)** — the precise modern textbook list of finite class-formation axioms + the class-existence metatheorem. *(§1)*
5. **Kunen, *Set Theory* (1980)** — the clean, citable reflection-theorem proof that ZF is NOT finitely axiomatizable. *(§1)*
6. **Lévy, *Axiom Schemata of Strong Infinity* (1960)** — the reflection schema that the ZF schemas reduce to; the structural reason finitization fails in FOL. *(§1)*
7. **Hailperin, *A Set of Axioms for Logic* (1944)** — a second, independent schema-collapse (Quine's NF finitely axiomatized); bridges NBG to typed comprehension. *(§1)*
8. **Zermelo, *Über Grenzzahlen und Mengenbereiche* (1930)** — origin of the whole "schema collapses in second-order logic" phenomenon; second-order Separation as one axiom buys quasi-categoricity. *(§2)*
9. **Shapiro, *Foundations without Foundationalism* (1991)** — the canonical case that second-order logic turns the ZFC schemas into single axioms; frames the research question directly. *(§2)*
10. **Väänänen, *Second Order Logic or Set Theory?* (2012)** — internal categoricity: the schema-collapse payoff survives in Henkin/typed semantics, the actual regime of a HOL prover. *(§2)*
11. **Williams, *The Structure of Models of Second-order Set Theories* (2018)** — the definitive map from finitely-axiomatizable GBC up to non-finitely-axiomatizable KM, stratified by comprehension strength. *(§2)*
12. **Church, *A Formulation of the Simple Theory of Types* (1940)** — THE basis of HOL: comprehension via a single typed lambda-abstraction, no schema. *(§4)*
13. **Henkin, *Completeness in the Theory of Types* (1950)** — general models: what "a set is a predicate" means model-theoretically; comprehension = frames closed under definability. *(§4)*
14. **Gordon, *Set Theory, Higher Order Logic or Both?* (1996)** + **Paulson, *ZFC_in_HOL* AFP (2019)** — the canonical design question and its state-of-the-art realization: a type `V` + ZF axioms inside typed HOL. *(§3)*
15. **Krauss & Schropp, *A Mechanized Translation from HOL to Set Theory* (2010)** — the most direct precedent for the Y4 bridge: machine-checked typed-HOL → first-order set theory. *(§3)*
16. **Brown, Kaliszyk & Pąk, *Higher-Order Tarski–Grothendieck as a Foundation* (2019)** — the cleanest realization of "put set theory inside HOL so the schemas collapse"; HOL and TG co-exist. *(§3/§5)*
17. **Lawvere, *An Elementary Theory of the Category of Sets* (1964)** — the prototype finitely-presented, schema-free set theory; structural analog of the HOL move. *(§5)*
18. **Shulman, *Comparing Material and Structural Set Theories* (2019)** — the modern dictionary of exactly which first-order schema each structural axiom replaces. *(§5)*

---

## 4. Relation to verus-fork / Y4

Verus's spec layer models sets as typed predicates — `ISet<A>` is literally `A → bool` — which is the Isabelle/HOL "set = predicate" model, a *typed* (Henkin-style) second-order setting. This library situates that choice: the metamathematics explains why Verus inherits comprehension "for free" (typed lambda-abstraction, §4) rather than carrying ZF's Separation/Replacement schemas; the second-order literature (§2) tells us what categoricity/determinacy the typed-comprehension regime does and does not buy; and the theorem-proving cluster (§3) — HOL-ST, ZFC_in_HOL, HOTG/Egal, and especially the **HOL↔set-theory translations** (Krauss–Schropp; Guilloud et al.; HOTG alignment) — is the direct engineering precedent for bridging a typed-HOL spec language to a set-theoretic / first-order SMT backend, which is the core of the adsmt-backend Y4 work.

---

## 5. Entry Format Legend

Each entry in the thematic files is formatted:

> **Title (bold)**
> Authors — Year — venue/kind
> **Link:** stable landing URL (arXiv abstract, DOI, publisher, author page, SEP, project page)
> **PDF:** direct open-access PDF (omitted when none is legitimately free)
> A 2–4 sentence summary.
> **Relevance:** 1–3 sentences tying the work to the finite-axiomatization-for-HOL question.

**★ CANON** marks genuinely seminal / must-have works. Entries are ordered seminal-first / roughly chronologically within each file. Each unique work has its full entry in exactly one file; cross-references appear as one-liners. Full BibTeX for every work is in `refs.bib`.
