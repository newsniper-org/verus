# 06 — Typed Second-Order Class Theories (the three-axis intersection)

*This file isolates a deliberately narrow target: foundations that are simultaneously (i) **class theories** — a primitive set-vs-class / small-vs-large distinction; (ii) **second-order / impredicative** — the class layer is governed by comprehension in which class quantifiers are permitted (what makes Morse–Kelley genuinely second-order and strictly stronger than predicative NBG); and (iii) **typed** — a type or sort discipline that REPLACES the single untyped global membership relation `∈`, whether as many-sortedness, a Church-STT-style typed predicate `A → o`, a universe ladder `Type₀ : Type₁ : …`, or a categorical small/large object. The intersection is what the Verus/Y4 model `ISet<A> = spec_fn(A) → bool` actually needs: a typed predicate that nonetheless carries an impredicative-class layer above it.*

---

## The subtlety: plain MK is second-order + class but UNTYPED

The single most important calibration in this file: **plain Morse–Kelley (and GBC/KM as studied in the modern second-order set theory program) is second-order and a class theory, but it is NOT typed.** A model of KM is `(M, ∈, C)` with a set sort `M` and a class sort `C ⊆ P(M)`, but there is **one global, untyped membership relation `∈`**: classes contain sets through the same `∈` that relates sets to sets. Two-sorted quantifiers (set-variables vs class-variables) are a *quantifier* split, not a *typing of `∈`*. The task's "typed" axis demands a type/sort discipline that stands in for the untyped global `∈` — a typed predicate `A → o`, a universe level, or a categorical classifier. So the whole Williams / Gitman–Hamkins / Antos–Friedman / Yao / Marek–Mostowski cluster, however genuinely *second-order* and *class-theoretic*, lands at **typed = 0** (`2nd-order-class-but-untyped`). They are included because they are the canonical *sorted* presentations — the closest the untyped tradition gets — and because the Verus class layer is a sorted, second-order analogue of exactly these systems. But the honest verdict is recorded.

The genuinely **FULL** intersection hits are instead the type-theoretic and categorical realizations: an impredicative-`Prop` predicate `A → Prop` in Rocq/Coq (R2), a univalent universe with resizing (R2/HoTT), a categorical universe object / category of classes (R3), and Church-STT-flavored typed comprehension lifted to a class layer.

**Axes legend.** Each entry ends with `Axes: typed=· / 2nd-order=· / class=· → verdict`. Verdicts: **full** (all three), `2nd-order-class-but-untyped` (T0), `typed-class-not-2nd-order` (O0), `typed-2nd-order-not-class` (C0), `background`.

### Already in this library (cross-references — not re-entered here)

- **MK / GBC / KM second-order set theory** (Williams 2018 thesis; Gitman–Hamkins open determinacy & class Fodor; Antos–Barton–Friedman universism; the nLab MK entry) → **§02-second-order-set-theory.md**. These are the *untyped* two-sorted systems; §06 adds only the genuinely *typed* relatives and re-grades the borderline ones.
- **Algebraic set theory / topos / structural set theory** (Lawvere ETCS; Lambek–Scott; Bell; Mac Lane–Moerdijk; Shulman material/structural; Osius; Tarski–Grothendieck) → **§05-categorical-and-structural-alternatives.md**. §06 adds the *categories-of-classes* line (Joyal–Moerdijk, Awodey–Butz–Simpson–Streicher, Simpson, Awodey–Warren, van den Berg) that specifically axiomatizes the small/large *class* layer.
- **NF / TST stratified comprehension and the Hailperin schema-collapse** → **§01-finite-axiomatizability-metamath.md**. §06 adds Holmes's typed-set-theory-with-a-universal-set works as the typed-but-predicative contrast case.

---

## R1 — Sorted / many-sorted presentations of second-order set/class theory

*The two-sorted (sets + classes) and multi-sorted (urelements / sets / classes / hyperclasses) presentations. Per the calibration above, these are **second-order + class but untyped** unless a real type discipline replaces `∈`. The urelement and hyperclass works push hardest toward a genuine sort hierarchy but keep one global `∈`, so they are recorded honestly as T0. None is a FULL hit; they anchor the "sorted, not typed" baseline against which the R2/R3 FULL hits are judged.*

**Reflection in second-order set theory with abundant urelements bi-interprets a supercompact cardinal**
Joel David Hamkins, Bokai Yao — 2024 — *Journal of Symbolic Logic* 89(3), pp. 1007–1043; arXiv:2204.09766 — paper
**Link:** https://arxiv.org/abs/2204.09766
**PDF:** https://arxiv.org/pdf/2204.09766
A genuinely multi-sorted second-order class theory: the language carries distinct sorts for urelements (atoms), pure sets, and classes, with the class layer governed by second-order (Π¹₁ / full) reflection and comprehension. Under the abundant-atom axiom (urelements vastly outnumber pure sets), the second-order reflection principle is shown bi-interpretable and equiconsistent with a supercompact cardinal, via a Π¹₁ reflection characterization of supercompactness. The added urelement sort makes the sort discipline richer than plain two-sorted MK — but membership is still one global untyped `∈`, and urelements are atoms, not a typing of `∈`.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. New to the library.
**Verus/Rocq:** The closest the untyped tradition comes to the Verus picture of a base sort `A` (urelement-like atoms) sitting below a set sort below a class/predicate layer — but precisely because `∈` stays global, it shows what "many-sorted" buys *without* a true type discipline, sharpening why the R2 typed entries are the real intersection.

**Set Theory with Urelements**
Bokai Yao — 2023 — Ph.D. dissertation, University of Notre Dame; arXiv:2303.14274 — thesis
**Link:** https://arxiv.org/abs/2303.14274
**PDF:** https://arxiv.org/pdf/2303.14274
Systematic development of set theory and class theory over a base sort of urelements, with an axiomatization hierarchy and forcing techniques that preserve or destroy the urelement axioms. Chapter 4 develops class theory with urelements: a multi-sorted (urelements / sets / classes) second-order theory in which, assuming large cardinals, a model of second-order reflection is built where limitation-of-size fails. Establishes the metatheory of the sorted urelement–set–class framework underlying the Hamkins–Yao result — but with a single global `∈`, not a typed membership.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. New to the library.
**Verus/Rocq:** The standalone monograph on stratifying *quantification* (atoms / sets / classes) with impredicative class comprehension — the sorted-foundations template nearest a typed `ISet` hierarchy, useful as the "untyped ceiling" the Rocq emit improves upon by replacing `∈` with `A → Prop`.

**Hyperclass Forcing in Morse–Kelley Class Theory**
Carolin Antos, Sy-David Friedman — 2017 — *Journal of Symbolic Logic* 82(2), pp. 549–575; arXiv:1510.04082 — paper
**Link:** https://doi.org/10.1017/jsl.2016.74
**PDF:** https://arxiv.org/pdf/1510.04082
Introduces hyperclass-forcing — forcing whose conditions are themselves classes — inside MK**, an extension of MK whose ontology is explicitly stratified into THREE orders: sets (order 1), classes (order 2, collections of sets), and hyperclasses (order 3, collections of classes). A coding symmetry between β-models of MK** and transitive models of ZFC⁻ + an inaccessible (SetMK**) lets results transfer between the third-order class theory and a first-order set theory with a large cardinal. The class layer uses full impredicative MK comprehension, and the hyperclass layer adds a genuine third *order* — the closest this tradition gets to a real order/sort hierarchy — yet the base `∈` is still the single untyped global relation.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped** (honest reading: untyped but genuinely higher-*order*). New to the library.
**Verus/Rocq:** The set-theoretic mirror of stacking `ISet<ISet<A>>` and of universe levels `Type_i`: sets : classes : hyperclasses, each level a "large predicate" over the one below. Models how a typed prover could stratify a small/large/very-large universe while keeping impredicative (HOL-like) comprehension at each step — but shows order-stratification alone is not yet a *typing* of membership.

**On extendability of models of ZF set theory to the models of Kelley–Morse theory of classes**
Wiktor Marek, Andrzej Mostowski — 1975 — *ISILC Logic Conference* (Kiel 1974), Lecture Notes in Mathematics vol. 499, Springer, pp. 460–542 — chapter
**Link:** https://doi.org/10.1007/BFb0079429
Studies the ladder ZFC, ZFKM, KM, KMC and asks when a model of the set-part (ZF) can be EXTENDED, by adding a class sort, to a model of the full second-order Kelley–Morse theory. KM is presented as a two-sorted theory (sets and classes) with ten axioms including the full impredicative class-existence scheme; the paper introduces β-extendability and proves both positive results and that some models of ZF are not extendable to any model of KM. The historical root of the modern "second-order set theory = two-sorted theory" program — but two sorts of *quantifier* over one global `∈`, not a type discipline.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. (Year corrected to **1975**.) New to the library.
**Verus/Rocq:** The β-extendability analysis tells you exactly which set models admit a coherent impredicative class layer on top — directly relevant to how Y4 would layer a "large" class sort over a "small" set sort, while being the canonical demonstration that doing so by *sorting* (not typing) leaves `∈` untyped.

**Non-tightness in class theory and second-order arithmetic**
Alfredo Roque Freire, Kameryn J. Williams — 2023 — arXiv:2212.04445 [math.LO] — preprint
**Link:** https://arxiv.org/abs/2212.04445
**PDF:** https://arxiv.org/pdf/2212.04445
Makes the "second-order set theory = sorted analogue of second-order arithmetic" parallel fully explicit: Gödel–Bernays GB is treated as the two-sorted (sets + classes) class theory whose comprehension stratifies by Σ¹_k exactly as ACA₀ ⊆ Π¹_k-CA ⊆ Z2 do in the arithmetic case. Restricting the Comprehension schema of Z2 and of KM yields non-tight theories (admitting distinct bi-interpretable extensions), and likewise for GB and ACA₀ and their Σ¹_k extensions. Calibrates how the class sort's comprehension complexity controls the metatheory — over a single untyped `∈`.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. New to the library.
**Verus/Rocq:** The cleanest articulation of class theory (GB/KM) as the two-sorted higher analogue of second-order arithmetic, with class comprehension indexed by Σ¹_k — the precise "how impredicative is the single second-order comprehension axiom" dial a typed-HOL `ISet` model must choose, even though the underlying `∈` is untyped.

**The exact strength of the class forcing theorem**
Victoria Gitman, Joel David Hamkins, Peter Holy, Philipp Schlicht, Kameryn J. Williams — 2020 — *Journal of Symbolic Logic* 85(3), pp. 869–905; arXiv:1707.03700 — paper
**Link:** https://arxiv.org/abs/1707.03700
**PDF:** https://arxiv.org/pdf/1707.03700
Works inside the two-sorted (sets + classes) hierarchy of second-order set theories, proving the class forcing theorem equivalent over GBC to elementary transfinite recursion ETR_Ord along class well-orders of length Ord, and to existence of Ord-iterated truth predicates and Boolean completions of class partial orders. The result sits strictly between GBC and GBC + Π¹₁-comprehension, locating a natural principle precisely on the impredicative-comprehension scale — with the set/class split a quantifier-sort split over one global `∈`.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. New to the library.
**Verus/Rocq:** Extends the GBC→Π¹₁-CA→KM comprehension calibration in §02 with a flagship five-author result, showing exactly which fragment of class-sort comprehension a class-theoretic principle needs — the strength dial, set within the untyped baseline.

**Varieties of class-theoretic potentialism**
Neil Barton, Kameryn J. Williams — 2024 — *The Review of Symbolic Logic* 17(1), pp. 272–304; arXiv:2108.01543 — paper
**Link:** https://arxiv.org/abs/2108.01543
**PDF:** https://arxiv.org/pdf/2108.01543
Studies the modal logic of extending the class layer of a two-sorted second-order set theory: one fixes the sets and "individuates more classes" over a fixed set-universe, with the class sort governed by GBC/KM-style comprehension. Proves which potentialist systems validate the .2 and .3 modal axioms, characterizing how the second sort can grow — a philosophically explicit treatment of the class sort as the locus of variation, still over a single untyped `∈`.
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. New to the library.
**Verus/Rocq:** Foregrounds the class sort as a distinct, extensible second layer over a fixed set sort — useful for thinking about how a typed class/predicate layer relates modally to a fixed set base, while underscoring that "extensible class sort" is not yet "typed membership."

**Class choice and the surprising weakness of Kelley–Morse set theory**
Victoria Gitman, Joel David Hamkins, Thomas A. Johnstone — 2026 — arXiv:2601.23165 [math.LO]; cf. *Fundamenta Mathematicae* — preprint
**Link:** https://arxiv.org/abs/2601.23165
**PDF:** https://arxiv.org/pdf/2601.23165
Analyzes the two-sorted theory KM (GBC plus the full impredicative second-order class-comprehension schema over the class sort) and shows it is weaker than commonly assumed: KM does not prove the class choice scheme, the Łoś theorem for internal ultrapowers, nor certain complexity invariances, and the more robust theory is KM⁺ = KM + class choice. The class sort, its comprehension complexity, and the choice schemes are treated as first-class parameters of the formal two-sorted system. (Authors corrected to Gitman–Hamkins–**Johnstone**; the Karagila coauthorship belongs to the distinct *class Fodor* 2020 paper already in §02.)
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. Companion to the class-choice/Fodor results in §02; this is the updated standalone arXiv version.
**Verus/Rocq:** Sharpens exactly what a maximal impredicative class-comprehension axiom yields when choosing the strength of a typed-HOL class layer — and warns that "one big impredicative comprehension axiom" is subtler than intuition suggests, over an `∈` that remains untyped.

---

## R2 — Type-theoretic universe hierarchies as class theory (impredicative Prop / universe levels / HoTT resizing)

*The reading that matters most for Y4: a set lives in a small universe, a **class is a large typed predicate one universe up**, and impredicative comprehension is supplied by impredicative `Prop` or by propositional resizing. These are the genuine **FULL** intersection hits — and the Rocq `Ensemble A = A → Prop` entry is the literal emit target. FULL hits first, then the predicative typed-class baselines (universes-as-classes but without impredicative comprehension), then the philosophical "class = higher type" articulations.*

### FULL intersection (typed + impredicative second-order + class)

**The Rocq/Coq Standard Library: `Sets.Ensembles` (`Ensemble := U → Prop`)** ★ FULL — the literal Y4 emit target
Coq/Rocq Development Team (orig. contributors incl. INRIA) — 2024 — Rocq standard library (`Coq.Sets.Ensembles`) — documentation
**Link:** https://rocq-prover.org/doc/V8.18.0/stdlib/Coq.Sets.Ensembles.html
The `Ensembles` module defines a "set of `U`" as a typed predicate: `Definition Ensemble := U -> Prop`, with `In A x := A x`, `Included`, `Union`, `Intersection`, `Complement`, `Full_set`, `Empty_set`, and `Extensionality_Ensembles`. Because the codomain `Prop` is impredicative in CIC, an `Ensemble` may be formed by quantifying over arbitrary propositions (including over all subsets of `U`), giving an *impredicative comprehension* over the typed power-object `U → Prop`. The type discipline of `U`/`Prop`/`Type_i` replaces a global `∈`.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** THIS IS THE Y4 ROCQ EMIT TARGET'S SET MODEL: `ISet<A> = spec_fn(A) → bool` emits to Rocq exactly as `Ensemble A = A → Prop`. The full subset-lattice over a type is a large typed predicate (a class of `A`), and impredicative `Prop` supplies impredicative comprehension over it — the single most load-bearing entry in the library.

**The Calculus of Inductive Constructions / Sorts and universes (Rocq Reference Manual, CIC chapter)** ★ FULL — primary R2 source
The Rocq (Coq) Development Team — 2024 — Rocq Prover Reference Manual (CIC), Inria — documentation
**Link:** https://rocq-prover.org/doc/master/refman/language/cic.html
The normative description of Rocq's type system: CIC with an impredicative sort `Prop`, a predicative `SProp`, and an infinite cumulative predicative hierarchy `Type_0 : Type_1 : …` with `Prop, Set : Type_1`. `Prop` is impredicative — a universally quantified proposition stays in `Prop` regardless of the domain's size — so a predicate `A → Prop` (the `Ensemble A` construction) is a typed "set of `A`" whose comprehension layer is genuinely impredicative, living one universe below the large `Type_i` hierarchy.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** THE primary R2 source: the typed axis (`Type_i` ladder), the second-order axis (impredicative `Prop`), and the class axis (small `Type_i` vs large `Type_{i+1}`) all in one normative document — the concrete system in which Verus's `ISet<A>` is re-expressed.

**Universe Polymorphism in Coq** ★ FULL
Matthieu Sozeau, Nicolas Tabareau — 2014 — ITP 2014, LNCS 8558, Springer, pp. 499–514 — paper
**Link:** https://link.springer.com/chapter/10.1007/978-3-319-08970-6_32
**PDF:** https://sozeau.gitlabpages.inria.fr/www/research/publications/drafts/univpoly.pdf
The definitive account of Coq's universe hierarchy: an impredicative `Prop` at the bottom and an infinite cumulative tower of predicative `Type_0 : Type_1 : …`, with universe levels, constraints, and "typical ambiguity" made explicit and polymorphic. Formalizes how a definition can be reused at many universe levels with checked constraints — the mechanism that keeps the small-vs-large (set-vs-class) distinction consistent.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The engineering core of "a set lives in `Type_i`, a class is a large type in `Type_{i+1}`" — the primary source for the `Type_i` levels that realize R2 and the universe-bookkeeping a Rocq emit must manage when `ISet`-of-classes crosses the small/large boundary.

**Mathlib `SetTheory.ZFC.Class` (`Class := Set ZFSet = ZFSet → Prop`)** ★ FULL
Mario Carneiro and the Mathlib Community — 2024 — Mathlib4 (leanprover-community), `Mathlib.SetTheory.ZFC.Class` — documentation
**Link:** https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Class.html
Building on `ZFSet` (PSet quotiented by extensional equivalence at a fixed universe level), Mathlib defines `Class := Set ZFSet`, i.e. a class is a typed predicate `ZFSet → Prop`, with `Class.ofSet` embedding each small set as the class of its members. It proves the genuine set-vs-proper-class distinction: the universal class is not a set (`Class.univ_notMem_univ`) and the ordinals form a proper class (Burali-Forti) — collections too large to be `ZFSet` live as classes one type level up, with impredicative `Prop` supplying comprehension.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** A working type-theoretic class theory in a proof assistant: a proper class is literally a large typed predicate over the type of small sets — the Lean mirror of the Rocq `Ensemble` picture and a template for a proper-class layer above the spec-set type in a typed CIC emit target.

**Sets in Types, Types in Sets** ★ FULL — the canonical Coq↔ZF bridge
Benjamin Werner — 1997 — TACS '97, LNCS 1281, Springer, pp. 530–546 — paper
**Link:** https://link.springer.com/chapter/10.1007/BFb0014566
**PDF:** https://www.researchgate.net/profile/Benjamin-Werner-4/publication/225243273_Sets_in_types_types_in_sets/links/542936720cf238c6ea7d1848/Sets-in-types-types-in-sets.pdf
Two mutual interpretations relating the Calculus of Inductive Constructions (Coq's type theory) and ZF. Type theory is interpreted in set theory via a generalization of Coquand's proof-irrelevance interpretation; set theory is encoded in type theory via a variant of Aczel's iterative-sets (well-founded-tree) encoding, checked in Coq. The key calibration: the number of type-theoretic universes interleaves with the number of inaccessible cardinals, so the two hierarchies are essentially equivalent in strength.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The canonical licence for treating a Rocq predicate `A → Prop` as a set and a universe step up as the move to a proper-class layer — proving Coq's typed universe hierarchy + impredicative `Prop` model genuine impredicative set theory and that universes correspond to large-cardinal/class strength.

**Sets in Coq, Coq in Sets** ★ FULL — most engineering-concrete
Bruno Barras — 2010 — *Journal of Formalized Reasoning* 3(1), pp. 29–48 — article
**Link:** https://jfr.unibo.it/article/view/1695
**PDF:** https://jfr.unibo.it/article/view/1695/1316
Formalizes a set-theoretic model of CIC inside Coq and, dually, builds a model of Intuitionistic ZF (IZF) in Coq using the "set as pointed well-founded graph" / Aczel encoding. Axiomatizes ZF and HF as Coq module interfaces, develops functions and ordinals, proves soundness of several models, and notes that full Replacement appears to need a type-theoretic axiom of choice. Extends Werner's encoding and grounds the relative-consistency analysis of Coq via strong normalization with inaccessibles.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The most engineering-concrete instance of building an impredicative set theory inside Coq/Rocq's typed universe-plus-`Prop` discipline: sets are typed iterative-set trees, classes are the large predicates one universe up — a direct architectural precedent for emitting a verified set model into Rocq.

**A Formal System of Axiomatic Set Theory in Coq** ★ FULL — MK-in-Coq, the R1↔R2 bridge
Tianyu Sun, Wensheng Yu — 2020 — *IEEE Access* 8, pp. 21510–21523; DOI 10.1109/ACCESS.2020.2969486 — article
**Link:** https://ieeexplore.ieee.org/document/8970457/
Formalizes Morse–Kelley set theory in Coq, taking classes as the fundamental objects (every object is a class; sets are exactly classes that are members of some class), with MK's axioms, the impredicative class-comprehension schema, and 181 definitions/theorems machine-checked, including functions, ordinals, cardinals, the naturals, and Peano's postulates as theorems. The set-vs-class distinction is realized through Coq's typed term language rather than a single untyped `∈`.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library; the most R1↔R2 bridging entry.
**Verus/Rocq:** Directly on target: an impredicative-comprehension MK class theory hosted inside Coq/Rocq's type discipline — a concrete template for representing a primitive set-vs-class distinction with impredicative class comprehension in the exact type theory Verus emits to.

**A Comparative Review of ZFC, NBG, and MK Axiom Systems: Theoretical Foundations and Formalization in Coq** ★ FULL — current, formalization-oriented
Si Chen, Wensheng Yu — 2026 — *Journal of Systems Science and Complexity* (Springer); DOI 10.1007/s11424-026-5318-1; preprint Preprints.org 202504.0684 — article
**Link:** https://link.springer.com/article/10.1007/s11424-026-5318-1
**PDF:** https://www.preprints.org/manuscript/202504.0684/v1/download
Compares ZFC, the finitely-axiomatizable predicative class theory NBG, and the impredicative second-order class theory MK across expressive power and metamathematical properties, then formalizes and contrasts all three inside Coq. Makes explicit how NBG's class comprehension is restricted to set quantifiers (predicative) while MK permits class quantifiers (impredicative second-order), and how the set-vs-class distinction is encoded in Coq.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The most recent work placing NBG and MK side-by-side and formalizing the set/class distinction and the predicative-vs-impredicative boundary in Coq/Rocq — directly informs whether a Rocq-emitting verifier should pick a finitely-axiomatized predicative class layer (NBG) or a genuinely second-order one (MK).

**Resizing Rules — their use and semantic justification** ★ FULL — the impredicative-class move in HoTT
Vladimir Voevodsky — 2011 — invited talk, TYPES 2011, Bergen; slides hosted at IAS — slides
**Link:** https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf
**PDF:** https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/2011_Bergen.pdf
Voevodsky's original proposal of resizing rules: an introduction rule (RR1, RR2) that lets a type a priori in a larger universe `U2` be placed into a smaller `U1` once a size-property (e.g. `isaprop`) holds. The motivation is the *defined* type `hProp` of subsingletons used in place of a primitive impredicative `Prop`; resizing recovers an impredicative-flavored small layer without a primitive impredicative sort.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The cleanest realization of the typed + second-order/impredicative + class intersection in HoTT: collapse a LARGE typed predicate (`hProp` in `U2`) into a SMALL universe (`U1`) — an impredicative comprehension principle layered on a typed small/large stratification, informing how far a Rocq-emitted `ISet`/`hProp` layer can be pushed toward impredicativity.

**Cubical Assemblies, a Univalent and Impredicative Universe and a Failure of Propositional Resizing** ★ FULL — impredicative typed universe + univalence
Taichi Uemura — 2019 — TYPES 2018, LIPIcs vol. 130, Schloss Dagstuhl — paper
**Link:** https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2018.7
**PDF:** https://arxiv.org/pdf/1803.06649
Constructs a model of cubical type theory in cubical assemblies carrying a universe that is simultaneously univalent AND impredicative (closed under dependent products with arbitrary, possibly large, domain), then shows propositional resizing FAILS for this universe — separating impredicativity from resizing. One of the few semantic constructions combining a genuinely impredicative typed universe with univalence.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** Demonstrates that impredicative-`Prop`-style comprehension (the Rocq emit target's mechanism) is model-theoretically coherent with univalence, while resizing is an independent, separable extra — the flagship HoTT case of the full intersection without resizing.

### Philosophical articulation: "a proper class is the next TYPE above sets" (FULL by the type-as-class reading)

**Hierarchies Ontological and Ideological** ★ FULL — locus classicus for class = higher type
Øystein Linnebo, Agustín Rayo — 2012 — *Mind* 121(482), pp. 269–308 (OUP) — article
**Link:** https://academic.oup.com/mind/article-abstract/121/482/269/1044515
**PDF:** https://web.mit.edu/arayo/www/tt-g.pdf
Develops Gödel's remark that ZF is "what becomes of the theory of types when certain superfluous restrictions are removed," giving the precise correspondence between the ONTOLOGICAL hierarchy (sets / proper classes / hyperclasses) and the IDEOLOGICAL hierarchy of (infinitary) type theory. Builds cumulative type theories whose successive type levels mirror the move from sets to proper classes to hyperclasses; going up a type level is the typed analogue of admitting larger collections.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** Directly articulates R1/R2 for the project: the cumulative TYPE hierarchy (`Type_i` in Rocq/Lean) is identified level-for-level with the set / proper-class / hyperclass hierarchy — the foundational justification for "`ISet<A>` small, a class is a large typed predicate one level up."

**Set Theory, Type Theory, and Absolute Generality** ★ FULL — the calibrating reply
Salvatore Florio, Stewart Shapiro — 2014 — *Mind* 123(489), pp. 157–174 (OUP) — article
**Link:** https://academic.oup.com/mind/article/123/489/157/1285242
**PDF:** https://pure-oai.bham.ac.uk/ws/files/31912743/ST_TT_AG_Final.pdf
A response to Linnebo–Rayo arguing the ontological hierarchy of set theory (sets, proper classes, …) and the ideological hierarchy of type theory (individuals, predicates, predicates-of-predicates, …) are so tightly connected that any philosophical verdict about one transfers to the other. Makes explicit the level-by-level dictionary between a TYPED higher-order hierarchy and the set/proper-class layering, sharpening when a "class" is just a higher TYPE — and where the analogy breaks.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** Pins down precisely the typed (HOL/type-theoretic) reading of proper classes the project relies on, and warns where it breaks — essential calibration for treating a Verus/Isabelle-HOL typed predicate `A → bool` as a "class" rather than a set.

### Predicative typed-class baselines (universes-as-classes, but no impredicative comprehension)

**The Type Theoretic Interpretation of Constructive Set Theory** — the origin of "sets in type theory"
Peter Aczel — 1978 — Logic Colloquium '77, Studies in Logic 96, North-Holland, pp. 55–66 — chapter
**Link:** https://philpapers.org/rec/ACZTTT
Introduces the type-theoretic interpretation of Constructive ZF (CZF) inside Martin-Löf type theory: sets are well-founded trees built by the W-type over the universe `U` of small types, `V := (W X : U) X`, an element being a small index type with a family of elements of `V`. Membership and the CZF axioms (Restricted Separation, Collection) are validated by the type-theoretic constructions, with `U` separating small (set-sized) from large data. CZF comprehension is predicative (Restricted Separation), so no second-order/impredicative class layer.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The template Werner and Barras mechanize: the `V`-type over `U` establishes the small-type/large-type (set vs class) split via universes that the Rocq emit inherits — the typed-class baseline that impredicative `Prop` later upgrades to FULL.

**On Relating Type Theories and Set Theories**
Peter Aczel — 1999 — TYPES '98, LNCS 1657, Springer, pp. 1–18 — chapter
**Link:** https://link.springer.com/chapter/10.1007/3-540-48167-2_1
Studies the correspondence between Martin-Löf type theories with a hierarchy of universes and constructive set theories, interpreting extensional type theory with universes inside an extension of CZF with a hierarchy of inaccessible sets — calibrating how each type-theoretic universe corresponds to a set-theoretic inaccessible / regular set. Sharpens the universes-as-large-cardinals dictionary underlying the Werner/Barras encodings. Predicative CZF flavor, no second-order comprehension.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** Makes explicit the universe ↔ inaccessible-set / proper-class correspondence justifying reading a type-theoretic universe step as "going one level up to the class of all small sets" — the conceptual backbone for why Rocq's `Type_i` ladder is a legitimate small-vs-large stratification.

**The Type Theory of Lean** — Lean's `Type_i` + impredicative `Prop`, ZFC model
Mario Carneiro — 2019 — M.Sc. thesis, Carnegie Mellon University — thesis
**Link:** https://github.com/digama0/lean-type-theory/releases
**PDF:** https://github.com/digama0/lean-type-theory/releases/download/v1.0/main.pdf
Specifies and analyzes Lean's dependent type theory: inductive types, a non-cumulative predicative universe hierarchy `Type 0 : Type 1 : …`, an impredicative and proof-irrelevant `Prop`, quotient types, extensionality, and choice; proves metatheoretic properties and constructs the set-theoretic model, deriving consistency of Lean relative to ZFC (with inaccessibles for the universes). The universe-to-inaccessible model is the small/large (set/class) backbone; impredicative `Prop` is present but proper classes appear at the Mathlib level (above).
Axes: typed=1 / 2nd-order=1 / class=0 → **typed-2nd-order-not-class** (the *language* itself has no proper-class layer; Mathlib's `Class` does). New to the library.
**Verus/Rocq:** The authoritative statement of Lean's universe ladder + impredicative `Prop` and its ZFC model — the Lean analogue of Rocq's CIC manual, showing the same typed-second-order-comprehension layer an emit target relies on.

**Core Language: Sorts and the Impredicative Sort `Prop` (CIC)** — pins down `A → Prop` second-orderness
Coq/Rocq Development Team — 2024 — Rocq Prover Reference Manual — Core language / CIC — manual
**Link:** https://rocq-prover.org/doc/V8.18.0/refman/language/core/sorts.html
Specifies Rocq's sort discipline: a predicative cumulative `Set/Type_0 : Type_1 : …` together with a single impredicative `Prop`. Impredicativity of `Prop` means `forall (A : Type_i), P : Prop` is itself in `Prop` even though it quantifies over the larger sort — propositions may be built by quantifying over any sort, including `Prop` itself; to preserve consistency, large elimination from `Prop` into `Type` is restricted to singleton elimination.
Axes: typed=1 / 2nd-order=1 / class=0 → **typed-2nd-order-not-class** (this page is about the comprehension mechanism; the class layer is the `Ensembles`/`Type_i` entries). New to the library.
**Verus/Rocq:** The primary source for the two mechanisms that make a Rocq `A → Prop` a typed second-order class — the predicative `Type_i` ladder (small/large) and impredicative `Prop` (genuine second-order comprehension) — confirming `ISet<A> = A → Prop` really enjoys second-order comprehension.

**Homotopy Type Theory: Univalent Foundations of Mathematics** — the universe-level small/large discipline
The Univalent Foundations Program (IAS) — 2013 — IAS, Princeton; self-published; arXiv:1308.0729 — book
**Link:** https://homotopytypetheory.org/book/
**PDF:** https://hott.github.io/book/hott-online.pdf
The canonical reference for univalent foundations: Martin-Löf intensional type theory + univalence + higher inductive types, with a cumulative `U_0 : U_1 : U_2 : …` of univalent universes. Chapter 3 isolates the h-sets / mere propositions; Chapter 9 develops the small-vs-large distinction through universe levels; resizing is discussed as the (non-assumed) principle that would place a large proposition in a smaller universe. Predicative by default — no impredicative comprehension over the class layer.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The foundational text for the universe-level small/large discipline underlying Rocq's `Type_i` ladder (R2), establishing "set = h-set" and "the type of sets is a large type" — the typed+class baseline against which the resizing/impredicative entries are measured.

**Sets in homotopy type theory** — "h-sets are the sets, the universe of sets is large"
Egbert Rijke, Bas Spitters — 2015 — *Mathematical Structures in Computer Science* 25(5), pp. 1172–1202; arXiv:1305.3835 — paper
**Link:** https://arxiv.org/abs/1305.3835
**PDF:** https://arxiv.org/pdf/1305.3835
Identifies the h-sets (0-truncated types) as the sets of HoTT and proves they form a ΠW-pretopos (a predicative analog of a topos) in a univalent universe, recovering much of structural set theory internally. Univalence makes the type `Set` of all h-sets a 1-type, forcing it one universe up — making precise that "the type of sets is large" while each individual set is small. Predicative; schema-free comprehension via the pretopos structure.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The univalent counterpart of the HOL "set = predicate" picture, with the small/large (set/class) split carried by universe level rather than `∈`; the ΠW-pretopos is the predicative comprehension layer most analogous to a Rocq `Ensemble`/`ISet` model.

**On Small Types in Univalent Foundations** — exactly when "large" needs resizing
Tom de Jong, Martín Hötzel Escardó — 2023 — *Logical Methods in Computer Science* 19(2); arXiv:2111.00482 — article
**Link:** https://arxiv.org/abs/2111.00482
**PDF:** https://arxiv.org/pdf/2111.00482
A predicative study (no resizing, no excluded middle) of when a type is "small" — equivalent to a type in a fixed lower universe — in univalent foundations. Shows many natural large structures (nontrivial directed/bounded-complete posets, the type of ordinals) cannot be small without forcing propositional resizing (Voevodsky's impredicativity axiom), which the authors deliberately avoid, precisely delimiting what the universe hierarchy alone can and cannot do about largeness.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. (De-duplicated: the pool listed this twice.) New to the library.
**Verus/Rocq:** The sharpest modern analysis of the small-vs-large (set-vs-class) line drawn by universe levels, proving impredicative resizing is exactly what moves large objects down — directly relevant to judging whether a Verus/Rocq `ISet` layer can stay predicative (small) or must accept a class/large universe with optional resizing.

**Experimental library of univalent formalization of mathematics** — `hProp`/`hSet` in Coq
Vladimir Voevodsky — 2014 — *Mathematical Structures in Computer Science* (later); arXiv:1401.0053 — paper
**Link:** https://arxiv.org/abs/1401.0053
**PDF:** https://arxiv.org/pdf/1401.0053
Voevodsky's account of the Coq library (ancestor of UniMath/Foundations): the defined universe `hProp` of subsingletons and `hSet` of sets as typed sub-collections one universe up, the h-level/truncation hierarchy, and where resizing rules would be needed to make `hProp` behave like a small impredicative `Prop`. The concrete proof-assistant realization of the typed small/large discipline of univalent foundations; predicative without resizing.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** A worked Coq/Rocq library where "a set is a typed predicate at a given h-level" and "the universe of sets is large" are formal — the closest precedent for a Rocq emit target distinguishing small sets from the large universe of sets, showing which constructions force a universe bump.

**The Category of Iterative Sets in Homotopy Type Theory and Univalent Foundations** — material `V` below a univalent universe
Daniel Gratzer, Håkon Robbestad Gylterud, Anders Mörtberg, Elisabeth Stenholm — 2024 — *Mathematical Structures in Computer Science* 34, pp. 945–970; arXiv:2402.04893 — paper
**Link:** https://arxiv.org/abs/2402.04893
**PDF:** https://arxiv.org/pdf/2402.04893
Builds the type `V` of iterative (Aczel-style) sets inside a minimal univalent type theory, equipping it with a Tarski universe and a category-with-families modeling extensional type theory. Because univalence makes the type of h-sets a 1-groupoid rather than a strict set, `V` provides a stricter, non-univalent universe of sets sitting below the large univalent universe — a clean small (material sets) vs large (univalent universe) stratification. Predicative.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** Realizes a material/iterative set universe `V` (the "small sets") built by W-types over `U`, with `U` the large/class layer — Aczel's CZF-in-type-theory picture rendered univalently and formalized in agda-unimath, a template for emitting an `∈`-based small layer on top of a typed universe.

**Univalent Categories and the Rezk Completion** — small/large categories as universe levels
Benedikt Ahrens, Krzysztof Kapulkin, Michael Shulman — 2015 — *Mathematical Structures in Computer Science* 25(5), pp. 1010–1039; arXiv:1303.0584 — paper
**Link:** https://arxiv.org/abs/1303.0584
**PDF:** https://arxiv.org/pdf/1303.0584
Defines the correct notion of category in univalent foundations (univalent/saturated categories, isomorphism = identity) and constructs the Rezk completion, careful about universe levels: the object-type may be a large type, and one Rezk-completion route raises the universe (large) while another preserves it (small) — making the small-vs-large category distinction a matter of typed universe stratification. Predicative.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** Shows the small/large (set/proper-class) distinction surfacing as universe levels for categories — the same bookkeeping a Rocq emit target must manage when an `ISet`-of-`ISet`s or category-of-sets crosses the small/large boundary.

---

## R3 — Categorical / higher-type typed class theory (algebraic set theory, categories of classes, nth-order)

*The structural reading: a category of classes with a distinguished class of **small maps** (set-valued vs class-valued morphisms), a universal object `V`, and powerclasses. "Small map" literally TYPES a morphism as set- or class-valued — a typed categorical realization of the small/large distinction. The impredicative members (full powerclass → IZF/MK-strength) are **FULL** hits; the predicative members (no full power object → CZF-strength) are the typed-class baselines. The Joyal–Moerdijk / Awodey–Butz–Simpson–Streicher core extends the topos material already in §05 with the specifically class-layer axiomatics.*

### FULL intersection (impredicative categories of classes)

**Algebraic Set Theory** ★ FULL — founding monograph of AST
André Joyal, Ieke Moerdijk — 1995 — London Mathematical Society Lecture Note Series 220, Cambridge University Press — book
**Link:** https://www.cambridge.org/core/books/algebraic-set-theory/31FB231402C980AAEBAC0A02CB5F6DD9
The founding monograph of Algebraic Set Theory: models of set theory are exhibited as ALGEBRAS (Zermelo–Fraenkel algebras) for a presented algebraic theory, with set-theoretic conditions (well-foundedness) recast algebraically (freeness). The central apparatus is a CATEGORY WITH CLASS STRUCTURE: a category of classes with a distinguished class of SMALL MAPS (fibres are sets), powerclasses, and a universal object `V` — a structural, sorted account of the set-vs-class distinction, uniformly covering intuitionistic set theory and topos theory.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The canonical typed (categorical) treatment of the proper-class layer: "small map" types a morphism as set- vs class-valued, the structural analogue of `ISet<A> = A → bool` being a small/large typed predicate; the free-ZF-algebra view collapses comprehension into one universal property rather than a first-order schema.

**Relating first-order set theories, toposes and categories of classes** ★ FULL — the definitive class-category paper
Steve Awodey, Carsten Butz, Alex Simpson, Thomas Streicher — 2014 — *Annals of Pure and Applied Logic* 165(2), pp. 428–502 (online 2013) — paper
**Link:** https://doi.org/10.1016/j.apal.2013.06.004
**PDF:** https://www.phil.cmu.edu/projects/ast/Papers/Awodey-Butz-Simpson-Streicher-APAL-2013.pdf
Introduces Basic Intuitionistic Set Theory (BIST) extending the internal logic of elementary toposes; given a topos with a directed structural system of inclusions, a forcing-style interpretation conservatively extends the internal logic, and BIST+Coll is sound and complete relative to such toposes with nno. A large part develops, following Joyal–Moerdijk, a CLASS-CATEGORY semantics: it axiomatizes categories of classes compatible with BIST and proves soundness/completeness for BIST relative to it, with completeness of BIST+Coll via categories of ideals over toposes.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The most precise bridge between an impredicative first-order set theory and a TYPED categorical class layer: classes are class-category objects, sets are the small/topos part, `∈` is interpreted by forcing — directly relevant to emitting a sets-as-typed-predicates model whose proper-class extension is conservative over the typed (topos) core.

**Relating first-order set theories and elementary toposes (BIST / categories with class structure)** ★ FULL — primary BSL version
Steve Awodey, Carsten Butz, Alex Simpson, Thomas Streicher — 2007 — *The Bulletin of Symbolic Logic* 13(3), pp. 340–358 — paper
**Link:** https://www.cambridge.org/core/journals/bulletin-of-symbolic-logic/article/abs/relating-firstorder-set-theories-and-elementary-toposes/
**PDF:** https://www.andrew.cmu.edu/user/awodey/preprints/bistBSL.pdf
The BSL announcement/companion: BIST is interpreted soundly and completely in any elementary topos with a "category with class structure" (a system of small maps singling out the SET-like, i.e. small, objects inside the larger universe of class-like objects). The small/large distinction is carried by a typed categorical structure rather than an untyped global `∈`, and a directed-colimit ideal completion turns a topos of sets into a category of classes.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** Reading R3 in its sharpest form: small maps give the set-vs-class boundary as TYPED categorical structure (objects = classes, small subobjects = sets), the structural mirror of "`ISet<A> = A → bool` small, class = large predicate"; anchors the §05 categories-of-classes material with its BIST soundness/completeness source.

**Elementary axioms for categories of classes** ★ FULL — most economical axiom list
Alex K. Simpson — 1999 — LICS 1999, pp. 77–85 — paper
**Link:** https://doi.org/10.1109/LICS.1999.782592
Axiomatizes a notion of "class structure" on a regular category, isolating the essential properties of the CATEGORY OF CLASSES with its full subcategory of SETS. As with the axioms for a topos, the axiomatization is very simple yet powerful: the resulting categories are sound and complete models for intuitionistic ZF (IZF), streamlining and generalizing the Joyal–Moerdijk axioms.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The cleanest, most economical axiom list for a TYPED class theory — a regular category of classes with a full subcategory of sets, complete for impredicative IZF; the "small list of axioms, topos-strength consequences" shape is exactly the finite-axiomatization-of-a-typed-class-theory target, with sets/classes as distinct categorical sorts.

**A brief introduction to algebraic set theory** ★ FULL — best on-ramp
Steve Awodey — 2008 — *The Bulletin of Symbolic Logic* 14(3), pp. 281–298 — survey
**Link:** https://www.cambridge.org/core/journals/bulletin-of-symbolic-logic/article/abs/brief-introduction-to-algebraic-set-theory/4BD5763B1DCEED817B7C68AB7107483A
**PDF:** https://www.andrew.cmu.edu/user/awodey/preprints/astIntroFinal.pdf
A short, accessible introduction in which models of set theory are determined ALGEBRAICALLY as algebras for a presented theory. The method is robust (classical, intuitionistic, bounded, predicative): set-theoretic properties (well-foundedness) correspond to algebraic ones (freeness), and elementary set theories are complete w.r.t. algebraic models arising topologically, type-theoretically, and through variation. Lays out categories of classes, small maps, powerclasses, and the universal object.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** The best on-ramp to the categories-of-classes / small-maps machinery, explicitly listing the type-theoretic models among the algebraic ones — the clearest single statement that the small/large distinction is a structural/typed datum and that elementary set theories are COMPLETE w.r.t. these typed-class models.

**A unified approach to algebraic set theory** ★ FULL — the impredicative/predicative knob
Benno van den Berg, Ieke Moerdijk — 2007 — Logic Colloquium 2006 tutorial; arXiv:0710.3066 [math.LO] — survey
**Link:** https://arxiv.org/abs/0710.3066
**PDF:** https://arxiv.org/pdf/0710.3066
An introduction to and synthesis of AST as a flexible CATEGORICAL framework for studying many set theories at once — classical/constructive, predicative/impredicative — emphasizing IZF and CZF. Presents the axiomatic core (categories with class structure, small maps and their stability/collection axioms, powerclass functor, W-types) uniformly and surveys the soundness/completeness and model-construction results; the connective tissue between Joyal–Moerdijk, the Awodey–Butz–Simpson–Streicher line, and the predicative developments.
Axes: typed=1 / 2nd-order=1 / class=1 → **full** (covers both knobs; the impredicative-powerclass setting is the FULL one). New to the library.
**Verus/Rocq:** The single best map of the whole landscape and the IMPREDICATIVE-vs-PREDICATIVE knob: impredicative powerclasses give IZF/MK strength, predicative axioms give CZF — showing precisely which axiom toggles the second-order strength of the typed class layer.

**Algebraic models of sets and classes in categories of ideals** ★ FULL — conservativity over type theories
Steve Awodey, Henrik Forssell, Michael A. Warren — 2006 — CMU AST project preprint — preprint
**Link:** https://kilthub.cmu.edu/articles/journal_contribution/Algebraic_Models_of_Sets_and_Classes_in_Categories_of_Ideals/6490853
**PDF:** https://www.phil.cmu.edu/projects/ast/Papers/AlgebraicModels.pdf
Introduces the IDEAL COMPLETION of a small category and shows the ideal completion of a suitable base satisfies the axioms for a CATEGORY OF CLASSES (Joyal–Moerdijk), so AST tools produce models of various elementary set theories. These models prove CONSERVATIVITY of several material set theories over various classical and constructive TYPE THEORIES, tightening the typed-foundations ↔ set/class-layer correspondence.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. New to the library.
**Verus/Rocq:** Directly proves CONSERVATIVITY of set-and-class theories over TYPE THEORIES via ideal completion — the technical bridge most aligned with re-presenting a class layer on top of a typed (HOL/Rocq) core without adding strength; the typed base and its class extension agree on the typed fragment.

### Categorical universe-object hits (R3a ↔ R2 hinge)

**Universes in toposes** ★ FULL — a topos universe IS the categorical set-vs-class distinction
Thomas Streicher — 2005 — in *From Sets and Types to Topology and Analysis* (Crosilla & Schuster, eds.), Oxford Logic Guides 48, OUP, pp. 78–90 — chapter
**Link:** https://academic.oup.com/book/5354/chapter/148144921
**PDF:** https://www2.mathematik.tu-darmstadt.de/~streicher/NOTES/UniTop.pdf
Develops a notion of UNIVERSE internal to an elementary topos, axiomatizing a class of "small" maps closed under the dependent-type constructors so one can form families by structural recursion and quantify over them. Logically it extends Higher-order Heyting Arithmetic and corresponds, in `Set`, to a strongly inaccessible cardinal; the axioms draw on the semantics of the Calculus of Constructions. A Grothendieck-style universe object `U` of small objects inside the larger topos IS precisely the categorical small-vs-large (set-vs-class) distinction: objects in `U` are small/sets, ambient topos objects are large/classes.
Axes: typed=1 / 2nd-order=1 / class=1 → **full**. (Re-graded from C0: a topos universe object *is* the categorical class distinction.) New to the library.
**Verus/Rocq:** The hinge between R3a (categories of classes) and R2 (universe hierarchies): a topos universe is a small/large typing exactly like Coq/Rocq's `Type_i : Type_{i+1}`, small maps = the universe's classifier — the cleanest statement of why a universe of small objects inside a larger ambient is a typed proper-class distinction, directly transferable to the Rocq universe story.

### Predicative typed-class baselines (categorical, no impredicative power object)

**Type theories, toposes and constructive set theory: predicative aspects of AST**
Ieke Moerdijk, Erik Palmgren — 2002 — *Annals of Pure and Applied Logic* 114(1–3), pp. 155–201, Elsevier — paper
**Link:** https://www.sciencedirect.com/science/article/pii/S0168007201000793
Develops a predicative version of algebraic set theory: a stratified pseudotopos / ΠW-pretopos built on a class of "small maps" whose fibres are set-sized, with the ambient category playing the role of classes. Models of Aczel–Myhill CZF are constructed; the standard model is the setoids of Martin-Löf type theory with a hierarchy of universes, where the universe encodes the small/large (set/class) distinction. Predicative — no impredicative class comprehension.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The categorical-AST reading (R3) of the universe-driven small/large discipline with Martin-Löf universes as the typed witness of smallness — the predicative counterpoint showing what a typed set/class theory looks like WITHOUT the second-order/impredicative axis.

**Predicative algebraic set theory**
Steve Awodey, Michael A. Warren — 2005 — *Theory and Applications of Categories* 15(1), pp. 1–39 — paper
**Link:** http://www.tac.mta.ca/tac/volumes/15/1/15-01abs.html
**PDF:** http://www.tac.mta.ca/tac/volumes/15/1/15-01.pdf
Extends the AST machinery to PREDICATIVE and constructive set theories: introduces BCST and CST and proves them sound and complete w.r.t. models in categories with an appropriate (predicative) class structure, isolating exactly which categorical axioms correspond to predicative vs impredicative comprehension, using ideal completions and pretopos structure rather than full power objects.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The deliberately PREDICATIVE corner — a typed class layer WITHOUT impredicative comprehension (no full powerclass); the precise contrast case showing what the second-order axis buys, i.e. the axiom you drop to get a predicative typed class theory, clarifying where Rocq's impredicative `Prop` sits versus a predicative universe tower.

**Predicative topos theory and models for constructive set theory**
Benno van den Berg — 2006 — PhD thesis, Universiteit Utrecht (supervisor: Moerdijk) — thesis
**Link:** https://dspace.library.uu.nl/handle/1874/8850
**PDF:** https://staff.science.uva.nl/b.vandenberg3/papers/predtop.pdf
A categorical analysis of predicative/constructive systems centred on CZF: observing an ordinary topos is too impredicative for CZF, it develops "predicativised" ambient categories — Π-W-pretoposes — and combines them with small maps and categories of classes to build models of CZF, calibrating how much powerclass/comprehension structure can be dropped while keeping a class layer.
Axes: typed=1 / 2nd-order=0 / class=1 → **typed-class-not-2nd-order**. New to the library.
**Verus/Rocq:** The most explicit study of a TYPED ambient (Π-W-pretopos, the categorical form of a dependent type theory with W-types) carrying a category-of-classes structure WITHOUT impredicative power objects — the predicative-typed-class reference point opposite to the impredicative-`Prop` (IZF/MK-strength) corner.

### Roundtrip / nth-order framing

**From sets to types to categories to sets**
Steve Awodey — 2009 — in *Foundational Theories of Classical and Constructive Mathematics* (Sommaruga, ed.), Western Ontario Series 76, Springer, pp. 113–125 — chapter
**Link:** https://link.springer.com/chapter/10.1007/978-94-007-0431-2_5
**PDF:** https://www.andrew.cmu.edu/user/awodey/preprints/stcsFinal.pdf
Compares set theory, type theory, and category theory by constructing explicit interpretations among them and tracking preservation/loss: sets-to-types is set-theoretic semantics, types-to-categories is the syntactic-category construction, categories-to-sets is the AST-style recovery of a membership set theory from a category of classes (resting on recent AST work). Captures precisely the intuition that a material `∈`-hierarchy can be reconstructed structurally.
Axes: typed=1 / 2nd-order=1 / class=1 → **typed-2nd-order-not-class** (a methodology paper; the class layer appears via AST but is not itself axiomatized here). New to the library.
**Verus/Rocq:** The conceptual roundtrip most relevant to the emit pipeline: TYPE THEORY → categorical (class-category) → material set theory, exactly the chain a typed verifier traverses to expose a set/class layer, stating where structure is preserved vs lost — the design rationale for a typed-core-with-class-extension emit.

---

## Related / background (anchors the typed axis or the class axis, but not the full intersection)

**Set Theory with Type Restrictions** — the typed-membership ancestor (promoted from background)
N. G. de Bruijn — 1975 — *Infinite and Finite Sets* (To Paul Erdős on his 60th birthday), Colloquia Mathematica Societatis János Bolyai vol. 10, North-Holland, pp. 205–214 (AUTOMATH archive aut032) — chapter
**Link:** https://www.win.tue.nl/automath/
**PDF:** https://automath.win.tue.nl/archive/pdf/aut032.pdf
De Bruijn argues ordinary mathematics is implicitly TYPED — that "everything is a set" licenses meaningless operations (intersecting a rational with a set of points) — and proposes a set theory in which every object carries a type and `x∈y` is well-formed only under type restrictions. The system grew out of and motivates AUTOMATH's dependent type theory: types/sorts REPLACE the single untyped `∈` with a typed membership discipline.
Axes: typed=1 / 2nd-order=0 / class=0 (weak class layer) → **typed-class-not-2nd-order** (promoted from background: this is squarely a TYPED reading, more than mere background for the typed axis). New to the library.
**Verus/Rocq:** A primary source for the Verus stance: "reject everything-is-a-set, type your membership" is exactly `ISet<A> = spec_fn(A) → bool`, and AUTOMATH is the type-theoretic ancestor of Rocq/Coq — the cleanest pin on the TYPED axis, showing what a class layer would have to be added on top.

**A language and axioms for explicit mathematics** — typed + impredicative, but "named classifications" not proper classes
Solomon Feferman — 1975 — *Algebra and Logic* (1974, Monash), LNM 450, Springer, pp. 87–139 — chapter
**Link:** https://doi.org/10.1007/BFb0062852
Introduces "explicit mathematics" — a theory of TYPES (classifications) AND NAMES, with classes as intensionally NAMED, finitely-presented objects: a separate sort of types alongside operations, and a naming/representation relation, with self-application permitted. The system (later T0) supports an inductive-generation/join apparatus and an impredicative least-fixed-point principle, giving genuine strength while keeping classes as explicitly-presented entities.
Axes: typed=1 / 2nd-order=1 / class=1(named, not small-vs-large) → **typed-2nd-order-not-class** (verdict and C-boolean reconciled: the typed + impredicative-class machinery is real, but the "class" layer is named classifications, not a genuine set-vs-proper-class split). New to the library.
**Verus/Rocq:** A typed two-sorted (operations + classifications) framework whose CLASS objects are NAMED and finitely-presented, with an impredicative (inductive least-fixed-point) layer — resonant with a typed verifier that wants classes-as-typed-predicates with explicit representations, a key R3b reference for typed finitely-presented class theories.

**Subsystems of Second Order Arithmetic** — the canonical sorted second-order template (no class layer)
Stephen G. Simpson — 2009 — Perspectives in Logic (2nd ed.), Cambridge University Press / ASL — book
**Link:** https://www.cambridge.org/core/books/subsystems-of-second-order-arithmetic/EA2E2A0F4F5A2C2B5C3C2D0E5C2B8A3E
**PDF:** https://www.personal.psu.edu/t20/sosoa/chapter1.pdf
The standard reference on `Z_2` and its subsystems (RCA₀, WKL₀, ACA₀, ATR₀, Π¹₁-CA₀), presented as a genuinely TWO-SORTED first-order theory with a number sort and a sets-of-numbers sort governed by an (impredicative at the top) comprehension schema. The set sort is the arithmetic analogue of the class sort, and Π¹₁/full comprehension is the analogue of impredicative class comprehension in KM.
Axes: typed=1 / 2nd-order=1 / class=0 → **typed-2nd-order-not-class**. New to the library.
**Verus/Rocq:** The rigorous SORTED two-sorted second-order template (number sort + set sort + comprehension) that the project's "typed second-order" axis instantiates; the Freire–Williams class-theory/second-order-arithmetic comparison (R1) presupposes exactly this as the arithmetic mirror of class theory.

**Elementary Set Theory with a Universal Set** — typed stratified comprehension, universal set, but predicative-flavored
M. Randall Holmes — 1998 — Cahiers du Centre de logique vol. 10, Academia, Louvain-la-Neuve, 241 pp. — book
**Link:** https://randall-holmes.github.io/head.pdf
**PDF:** https://randall-holmes.github.io/head.pdf
A textbook development of set theory in NFU (Quine's New Foundations with urelements), whose set-existence principle is STRATIFIED comprehension — a typed/type-respecting (TST-style) criterion. With stratification the only restriction, NFU has a universal set `V`, is closed under complementation, and the universe is a Boolean algebra with `V` at the top; non-set "big" collections (the Russell collection) are excluded by failure of stratification. Builds relations, functions, naturals, reals, ordinals, cardinals entirely within this typed-comprehension, universal-set framework.
Axes: typed=1 / 2nd-order=0(stratified, not impredicative) / class=1 → **typed-class-not-2nd-order**. (NF/TST tradition; cross-refs §01.) New to the library.
**Verus/Rocq:** The flagship TYPED class theory in the NF/TST tradition: comprehension governed by a TYPE (stratification) discipline rather than untyped `∈`, with the universal-set/Boolean-algebra structure and non-set "big" collections giving a small-vs-large flavor — but comprehension is stratified (predicative-flavored), the contrast case for what "second-order" buys.

**The equivalence of NF-style set theories with "tangled" type theories** — pure Russell-TST, no class layer
M. Randall Holmes — 1995 — *The Journal of Symbolic Logic* 60(1), pp. 178–190 — paper
**Link:** https://doi.org/10.2307/2275515
**PDF:** https://randall-holmes.github.io/Papers/tangled.pdf
Works directly with TST (Russell's theory of types: variables carry natural-number type indices, `x∈y` well-formed only when `type(x)+1 = type(y)`) and its generalization tangled type theory (TTT, well-formed when `type(x) < type(y)`), proving NF-style untyped set theories equiconsistent with corresponding tangled type theories and constructing ω-models of predicative NF. The TTT route was later used in Holmes's consistency proof of NF.
Axes: typed=1 / 2nd-order=0 / class=0 → **background** (anchors the typed axis in its purest Russell-TST form; cross-refs §01). New to the library.
**Verus/Rocq:** Pins the TYPED axis in its purest Russell-TST form (explicit integer-indexed type hierarchy with typed membership) and its exact relation to untyped stratified set theory — clarifying the precise sense in which "stratified/typed comprehension" is a TYPE discipline.

**Set-theoretical foundations of category theory (with an appendix by G. Kreisel)** — reflective universe, untyped
Solomon Feferman (appendix by Georg Kreisel) — 1969 — Reports of the Midwest Category Seminar III, LNM 106, Springer, pp. 201–247 — chapter
**Link:** https://doi.org/10.1007/BFb0059148
Feferman addresses "large" categories by adjoining to ZFC a constant `U` denoting a REFLECTIVE universe: `U` is an elementary substructure of the universe (a reflection principle), so small objects in `U` behave exactly as large ones outside it — a small-vs-large distinction for category theory within a first-order ZFC framework, an explicit alternative to Grothendieck universes.
Axes: typed=0 / 2nd-order=0 / class=1 → **background** (marks the class axis; untyped single `∈` + a universe constant, first-order). New to the library.
**Verus/Rocq:** The canonical "reflective universe" approach to small-vs-large — the same tension Rocq/Lean resolve with `Type_i` levels — but untyped and first-order, the foil that motivates a typed universe-level treatment.

**Ackermann's Set Theory Equals ZF** — primitive set/class discriminator, but untyped single universe
William N. Reinhardt — 1970 — *Annals of Mathematical Logic* 2(2), pp. 189–249 (North-Holland) — paper
**Link:** https://doi.org/10.1016/0003-4843(70)90011-2
Reinhardt analyzes Ackermann's set theory — a class/set foundation with a primitive predicate distinguishing SETS from proper classes via a reflection-like "definable below V" condition — and proves it equivalent in strength to ZF. The set-vs-class boundary is governed by a typed-discriminator/reflection principle rather than a size axiom, and the class layer admits impredicative class formation, but over a single universe with one `∈`.
Axes: typed=0(single sort predicate, not a hierarchy) / 2nd-order=1 / class=1 → **typed-2nd-order-not-class** (the "typing" is one is-a-set predicate over a class layer, not a full type discipline). New to the library.
**Verus/Rocq:** A class theory whose set/proper-class split is a primitive sort-like discriminator (the `V`-membership predicate) rather than untyped `∈` size-limitation — a contrast for how a typed prover could mark "is-a-set" as a typing predicate, with impredicative class comprehension but no hierarchy.

**Set theory with types (Machine Logic blog)** — contemporary Isabelle/HOL "set = predicate" statement
Lawrence C. Paulson — 2025 — Machine Logic (lawrencecpaulson.github.io), 21 Nov 2025 — blog post
**Link:** https://lawrencecpaulson.github.io/2025/11/21/Typed_Set_Theory.html
Paulson surveys TYPED set theory as the practical alternative to untyped ZF, from de Bruijn's "Set Theory with Type Restrictions" through AUTOMATH to Isabelle/HOL, where sets carry types and operations combine only same-typed sets, eliminating ZF coding tricks while still permitting full ZF via ZFC_in_HOL (bridging typed and material worlds through type classes). He stresses the set-vs-PREDICATE distinction (rather than set-vs-class), noting their logical equivalence in HOL.
Axes: typed=1 / 2nd-order=1 / class=0 → **background** (typed + HOL, but framed around set-vs-predicate, not a proper-class layer; anchors the Isabelle emit path). New to the library.
**Verus/Rocq:** Maximally on-point for Y4: the contemporary statement of exactly the Verus design ("a set is a typed predicate"; set vs predicate in HOL) by the Isabelle/HOL principal, surveying how Isabelle/HOL hosts both typed sets and full ZF (ZFC_in_HOL) — the bridge an emit-to-Isabelle/HOL target must traverse.

**Morse–Kelley set theory (nLab)** — the untyped baseline contrast
nLab contributors — 2024 — nLab (ncatlab.org) — encyclopedia
**Link:** https://ncatlab.org/nlab/show/Morse-Kelley+set+theory
A concise reference presentation of MK as a theory of sets-and-classes whose defining feature, versus NBG, is that arbitrary formulas — including those with quantifiers over classes — may appear in class-comprehension (i.e. impredicative / genuinely second-order). Notes MK is a non-conservative, non-finitely-axiomatizable proper extension of ZFC, originating in Wang (1949), Kelley's *General Topology* (1955) appendix, and Morse (1965).
Axes: typed=0 / 2nd-order=1 / class=1 → **2nd-order-class-but-untyped**. The explicit non-typed contrast anchor; cross-refs §02. New to the library.
**Verus/Rocq:** Baseline reference: plain MK is second-order + class but UNTYPED (a single global `∈` over an informal sets-and-classes universe) — the exact non-typed contrast point against which every sorted/Coq-formalized entry above is judged.

---

*Cross-references:* the untyped two-sorted GBC/KM program (Williams, Gitman–Hamkins, Antos–Barton–Friedman) is in **§02**; the topos / ETCS / material-structural and Tarski–Grothendieck material that the categories-of-classes line extends is in **§05**; the NF/TST stratified-comprehension and Hailperin schema-collapse are in **§01**; the Church-STT typed-comprehension core (why one typed comprehension suffices) is in **§04**; HOL-hosted set theory in provers (ZFC_in_HOL, HOTG/Egal, Kirst–Smolka second-order ZF in Coq) is in **§02/§03**.
