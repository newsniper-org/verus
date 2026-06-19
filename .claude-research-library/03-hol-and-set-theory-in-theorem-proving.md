# 03 — HOL + Set Theory in Theorem Provers (the Y4 precedent layer)

*The practical engineering. This is where a typed-HOL kernel actually hosts set theory: add a type `V` of all sets plus the ZF axioms (HOL-ST / HOLZF / ZFC_in_HOL), or translate between typed HOL and first-order set theory (Krauss–Schropp; Guilloud et al.), or build a foundation where classical extensional HOL and set theory literally coincide (HOTG / Egal). Because a HOL prover supplies comprehension via typed lambda-abstraction, embedding ZF is "add one type and a finite list of axioms" — no comprehension schema needed. This is the most direct precedent for bridging Verus's typed `ISet<A>` spec layer to a set-theoretic / SMT backend.*

---

**★ CANON — Set Theory for Verification: I. From Foundations to Functions**
Lawrence C. Paulson — 1993 — *Journal of Automated Reasoning* 11(3), pp. 353–389 — article
**Link:** https://link.springer.com/article/10.1007/BF00881873
**PDF:** https://www.cl.cam.ac.uk/~lp15/papers/Sets/set-I.pdf
Paulson derives a logic for specification and verification from the axioms of ZF, mechanized in Isabelle to produce Isabelle/ZF. The paper develops rules for descriptions, ordered pairs, relations and functions from the bare ZF axioms, and demonstrates interactive proofs of Cantor's theorem, the composition-of-homomorphisms challenge, and Ramsey's theorem. It establishes how first-order ZF is built into a usable verification framework inside an LCF-style prover.
**Relevance:** The foundational engineering reference for Isabelle/ZF, the first-order set-theory counterpart that the HOL-to-set-theory translation literature (Krauss/Schropp) targets, and a baseline for what set-theoretic reasoning inside a prover requires.

---

**Set Theory for Verification: II. Induction and Recursion**
Lawrence C. Paulson — 1995 — *Journal of Automated Reasoning* 15(2), pp. 167–215 (preprint arXiv:cs/9511102) — article
**Link:** https://link.springer.com/article/10.1007/BF00881916
**PDF:** https://arxiv.org/pdf/cs/9511102
The sequel develops recursive definitions inside Isabelle/ZF. Paulson mechanizes the Knaster–Tarski fixedpoint theorem and uses it to justify inductive and coinductive definitions, well-founded recursion, and datatype/codatatype constructions, all reduced to the ZF axioms.
**Relevance:** Shows how induction/recursion — the practically hardest part of set theory in a prover — is derived from the ZF axioms; essential background for any HOL-vs-set-theory translation and for understanding what a set-theory backend must support.

---

**Merging HOL with Set Theory: Preliminary Experiments**
Michael J. C. Gordon — 1994 — University of Cambridge Computer Laboratory, Technical Report 353 — tech report
**Link:** https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-353.html
**PDF:** https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-353.pdf
The original technical-report presentation of HOL-ST. Gordon extends the HOL logic with a new type V of all sets and a membership relation in V × V → bool, then asserts the ZF axioms directly in HOL. He reports preliminary experiments using the resulting system, whose proof-theoretic strength sits between ZF and ZF plus one inaccessible cardinal, and discusses how set-theoretic constructions interact with HOL's native type system.
**Relevance:** The primary source for HOL-ST: it shows concretely that you embed full ZF inside a typed-HOL kernel by adding one type and the (finite list of) ZF axioms — the essential engineering pattern behind set theory inside HOL provers.

---

**★ CANON — Experiments with ZF Set Theory in HOL and Isabelle**
Sten Agerholm, Michael J. C. Gordon — 1995 — TPHOLs 1995, LNCS 971, Springer, pp. 32–45 (also BRICS RS-95-37) — paper
**Link:** https://link.springer.com/chapter/10.1007/3-540-60275-5_55
**PDF:** https://www.brics.dk/RS/95/37/BRICS-RS-95-37.pdf
A comparative case study of representing and using ZF set theory in two systems: HOL (via HOL-ST, ZF embedded in typed higher-order logic) and Isabelle (via Isabelle/ZF, untyped first-order set theory). The central worked example is the construction of the Dana Scott domain D∞. The paper experimentally explores the advantages and disadvantages of higher-order vs first-order set theory for actual mechanized developments.
**Relevance:** A direct empirical comparison of set-theory-inside-HOL against standalone first-order set theory — exactly the trade-off relevant to deciding how verus-fork's typed-HOL spec layer should interact with set-theoretic constructions.

---

**★ CANON — Set Theory, Higher Order Logic or Both?**
Michael J. C. Gordon — 1996 — TPHOLs'96, LNCS 1125, Springer, pp. 191–201 — paper
**Link:** https://link.springer.com/chapter/10.1007/BFb0105405
Gordon weighs two foundational styles for mechanized mathematics: classical typed higher-order logic as used in HOL, and untyped first-order ZF as used in Isabelle/ZF. He proposes HOL-ST, a hybrid that lives inside HOL by introducing a single type V of all sets together with a membership relation and the ZF axioms asserted as ordinary HOL axioms. The paper argues this gives HOL's type discipline and automation alongside set theory's expressive power, and discusses the trade-offs.
**Relevance:** The canonical statement of the design question this cluster addresses: how a finitely-specified typed HOL core can host full ZF set theory simply by asserting the ZF axioms over a type V. It directly models the choice verus-fork faces in reconciling a typed-HOL spec language with set-theoretic reasoning.

---

**Mechanizing Set Theory: Cardinal Arithmetic and the Axiom of Choice**
Lawrence C. Paulson, Krzysztof Grabczewski — 1996 — *Journal of Automated Reasoning* 17(3), pp. 291–323 (preprint arXiv:cs/9612104) — article
**Link:** https://link.springer.com/article/10.1007/BF00283132
**PDF:** https://arxiv.org/pdf/cs/9612104
A deep development of ZF in Isabelle/ZF covering cardinal arithmetic and AC. The headline result is κ ⊗ κ = κ for infinite cardinals, requiring theories of orders, order-isomorphisms, order types, ordinal and cardinal arithmetic. The authors also mechanize the equivalence of 7 formulations of the Well-Ordering Theorem and 20 formulations of AC, covering the first two chapters of Rubin and Rubin.
**Relevance:** Demonstrates that genuinely deep set theory (cardinals, AC, well-ordering) is fully mechanizable in a first-order set-theory prover — the depth target any set-theory-in-HOL backend must eventually reach to be useful for Y4-style unification.

---

**★ CANON — Partizan Games in Isabelle/HOLZF**
Steven Obua — 2006 — ICTAC 2006, LNCS 4281, Springer, pp. 272–286 — paper
**Link:** https://link.springer.com/chapter/10.1007/11921240_19
**PDF:** https://mediatum.ub.tum.de/doc/1094432/1094432.pdf
Obua formalizes Conway's partizan games in HOLZF, an extension of Isabelle/HOL with the ZF axioms (a type ZF of sets plus membership). Partizan games are defined as the unique fixpoint of a function from Conway's definition; operations are defined on an abstract game type that hides its set-theoretic origins, supported by a polymorphic type of sets no larger than ZF sets. The paper relates well-foundedness in HOL and ZF, formalizes Conway's induction principle, and instances games as partially ordered abelian groups.
**Relevance:** The introduction and a substantial application of HOLZF (ZF embedded in HOL), illustrating how a typed-HOL prover hosts genuine set-theoretic recursion/induction while exposing a clean typed interface — directly the integration pattern verus-fork needs.

---

**★ CANON — A Mechanized Translation from Higher-Order Logic to Set Theory**
Alexander Krauss, Andreas Schropp — 2010 — ITP 2010, LNCS 6172, Springer, pp. 323–338 — paper
**Link:** https://link.springer.com/chapter/10.1007/978-3-642-14052-5_23
**PDF:** https://www21.in.tum.de/~krauss/papers/holzf.pdf
The authors specify and implement a proof-term-level translation from Isabelle/HOL to Isabelle/ZF: each HOL theorem is re-proved as a set-theoretic theorem, with HOL types interpreted as ZF sets and HOL's higher-order constructs (function spaces, polymorphism) mapped into the set-theoretic universe. The translation is checked by replaying full Isabelle/HOL proof terms in the ZF object logic, giving a verified bridge between the two foundations rather than a trusted axiomatic claim.
**Relevance:** The most direct precedent for verus-fork's goal of bridging a typed-HOL spec language with set theory: a concrete, machine-checked translation from typed HOL into untyped first-order set theory, showing exactly where typed comprehension lands in the set universe.

---

**Type Inference for ZFH**
Steven Obua, Jacques Fleuriot, Phil Scott, David Aspinall — 2015 — CICM 2015, LNCS 9150, Springer, pp. 87–101 — paper
**Link:** https://link.springer.com/chapter/10.1007/978-3-319-20615-8_6
**PDF:** https://www.research.ed.ac.uk/files/22933495/cicm2015.pdf
ZFH (Zermelo–Fraenkel set theory implemented in Higher-order logic) is a descendant of Agerholm and Gordon's HOL-ST that drops type variables and new-type definitions. The paper presents the type-inference algorithm for ZFH used in the ProofPeer prover: because function application (juxtaposition) is overloaded to be either set-theoretic or higher-order, the authors extend Hindley–Milner inference to handle this overloading, prove it correct, and explain why prior coercion/overloading approaches do not cover this case.
**Relevance:** A modern, minimalist HOL-ST descendant and its concrete type-inference engineering, showing how a single overloaded application connects the typed-HOL and set-theoretic worlds — the kind of surface design relevant to a typed `set = predicate` spec language.

---

**★ CANON — A Consistent Foundation for Isabelle/HOL**
Ondřej Kunčar, Andrei Popescu — 2019 — *Journal of Automated Reasoning* 62(4), pp. 531–555 (conf. ITP 2015) — article
**Link:** https://link.springer.com/article/10.1007/s10817-018-9454-8
**PDF:** https://eprints.whiterose.ac.uk/id/eprint/191505/1/Consistent_Foundation_IsabelleHOL_JAR_2019.pdf
Isabelle/HOL extends pure higher-order logic with overloaded constant definitions and type definitions whose combination had previously caused inconsistencies. The authors give a criterion — non-overlapping definitions plus termination of the definition-dependency relation tracked through both constants and types — guaranteeing relative consistency. The proof proceeds proof-theoretically, treating definitions as abbreviations and realized in HOLC, a logic augmenting HOL with comprehension types.
**Relevance:** Establishes rigorously why the typed-HOL core (with its single comprehension/typedef mechanism) stays consistent — i.e. why typed comprehension is safe to add as one device rather than a schema — underpinning the HOL side of the finite-axiomatization-for-HOL question.

---

**★ CANON — Zermelo Fraenkel Set Theory in Higher-Order Logic (ZFC_in_HOL)**
Lawrence C. Paulson — 2019 — Archive of Formal Proofs (AFP), entry ZFC_in_HOL — formalization
**Link:** https://www.isa-afp.org/entries/ZFC_in_HOL.html
**PDF:** https://www.isa-afp.org/browser_info/current/AFP/ZFC_in_HOL/outline.pdf
A modern formalisation of ZFC inside Isabelle/HOL, logically equivalent to Obua's HOLZF but engineered for the closest possible integration with the rest of Isabelle/HOL. It introduces a type V of sets with a function elts :: V ⇒ V set, and uses type classes (orders, lattices) to reuse subset/union/intersection notation. Two type classes (embeddable types injectable into V, and small types corresponding to a ZF set) ease combining V with other HOL types; the development covers products, sums, naturals, functions, transfinite induction, ordinals, cardinals, and transitive closure.
**Relevance:** The state-of-the-art realization of ZFC living inside a typed-HOL prover with seamless type-class integration — the most polished example of the exact architecture (a type V plus ZF axioms in HOL) that verus-fork's typed-set spec layer would emulate.

---

**Isabelle/HOL/GST: A Formal Proof Environment for Generalized Set Theories**
Ciaran Dunne, J. B. Wells — 2022 — CICM 2022, LNCS 13467, Springer, pp. 38–53; arXiv:2207.12039 — paper
**Link:** https://arxiv.org/abs/2207.12039
**PDF:** https://arxiv.org/pdf/2207.12039
A generalized set theory (GST) extends standard set theory to include non-set structured objects that can contain other structured objects including sets. The authors provide Isabelle/HOL support for GSTs treated as type classes combining features (sets, ordinals, functions, etc.), with an exception feature for partial functions/undefinedness and extensive use of soft types. When assembling a GST, extra axioms are generated under a user-modifiable policy, and a model is built from feature contributions to a von-Neumann cumulative hierarchy via ordinal recursion.
**Relevance:** Shows how to engineer flexible, modular set-theoretic foundations inside typed HOL using type classes and soft types, and how axioms are assembled and models constructed — directly relevant to building a configurable set-theory layer on a typed-HOL spec core.

---

**Mechanized HOL Reasoning in Set Theory**
Simon Guilloud, Sankalp Gambhir, Andrea Gilot, Viktor Kunčak — 2024 — ITP 2024, LIPIcs 309, Schloss Dagstuhl, pp. 18:1–18:18; arXiv:2403.13403 — paper
**Link:** https://arxiv.org/abs/2403.13403
**PDF:** https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.18/LIPIcs.ITP.2024.18.pdf
The authors present a mechanized embedding of higher-order logic and algebraic data types into first-order logic with ZFC axioms, interpreting types as sets and arrow types as set-theoretic function spaces, with lambda-terms handled via an explicit context capturing abstractions. The embedding is implemented in the LISA proof assistant, which is built on schematic first-order logic with an axiomatic-set-theory library, providing HOL-style proof-producing tactics interoperable with the set-theory kernel.
**Relevance:** A recent, opposite-direction realization of the bridge — HOL constructs implemented on top of a first-order set-theory kernel (LISA), complementary to HOLZF/ZFC_in_HOL — making explicit how typed comprehension/function-spaces line up with the underlying set axioms; informative for choosing which layer is primitive in a HOL+set-theory verification stack atop an SMT/first-order backend.

---

**★ CANON — Higher-Order Tarski–Grothendieck as a Foundation for Formal Proof**
Chad E. Brown, Cezary Kaliszyk, Karol Pąk — 2019 — ITP 2019, LIPIcs 141, Schloss Dagstuhl, pp. 9:1–9:16 — paper
**Link:** https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.9
**PDF:** https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.9/LIPIcs.ITP.2019.9.pdf
The authors introduce a foundation based on higher-order Tarski–Grothendieck (HOTG) set theory — the foundation of Chad Brown's Egal — and prove it has a model assuming a 2-inaccessible cardinal (the same hypothesis as first-order TG). The foundation lets proofs based on the two major competing foundations, higher-order logic and TG set theory, co-exist; they prove Tarski's Axiom A inside the HOL setting, find first-order equivalents for higher-order terms, build a Grothendieck-universe operator in Mizar, and transfer theorems (e.g. Lagrange's four-square theorem) between HOL and TG set theory, aligning the Isabelle/HOL and Isabelle/Mizar libraries in one framework.
**Relevance:** The single most on-target prover paper: it constructs a higher-order set theory where classical extensional HOL coincides with the set theory and shows precisely how the first-order Mizar schemas translate into the HOL presentation — the formal-prover realization of "put set theory inside HOL so the schemas collapse," a direct architectural template for Y4.

---

**★ CANON — Combining Higher-Order Logic with Set Theory Formalizations**
Cezary Kaliszyk, Karol Pąk — 2023 — *Journal of Automated Reasoning* 67(2), article 20, Springer — article
**Link:** https://link.springer.com/article/10.1007/s10817-023-09663-5
**PDF:** https://pmc.ncbi.nlm.nih.gov/articles/PMC10209288/
Building on the Isabelle Higher-Order Tarski–Grothendieck object logic, whose foundation includes both higher-order logic and set theory, the authors import the libraries of Isabelle/HOL and Isabelle/Mizar. Because the two libraries define basic concepts (real numbers, algebraic structures) independently and disconnectedly, the paper constructs isomorphisms aligning significant parts of both, enabling theorems to be transported between foundations and results from both libraries used simultaneously.
**Relevance:** The mature, journal-length account of making typed-HOL and set-theory formalizations interoperate inside one prover, including transporting theorems across the typed/untyped boundary — exactly the cross-foundation interoperability Y4 aims for.

---

**Hammering Higher Order Set Theory**
Chad E. Brown, Cezary Kaliszyk, Martin Suda, Josef Urban — 2025 — CICM 2025, LNCS 16080, Springer; arXiv:2509.08264 — paper
**Link:** https://arxiv.org/abs/2509.08264
**PDF:** https://arxiv.org/pdf/2509.08264
The authors apply automated theorem provers to substantially shorten a formal development in higher-order set theory (including the fundamental theorem of arithmetic and the irrationality of √2). Higher-order ATPs are especially effective because the underlying framework of higher-order set theory coincides with the classical extensional higher-order logic of most HO ATPs, so no significant translation is required; many subgoals are also first-order. They benchmark provers on generated subgoals and explore proof reconstruction by deriving formal proof terms when an ATP closes a subgoal.
**Relevance:** Shows the practical payoff of the HOL/set-theory coincidence: because higher-order set theory IS classical extensional HOL, off-the-shelf HO ATPs apply with no encoding — directly relevant to verus-fork's SMT/ATP-backed verification of set-theoretic specs.

---

**Megalodon — Interactive Theorem Prover and Proof Checker (higher-order Tarski–Grothendieck / Egal)**
Chad E. Brown et al. (ai4reason / CIIRC–CTU) — 2023 — software repository (GitHub: ai4reason/Megalodon) — software
**Link:** https://github.com/ai4reason/Megalodon
Megalodon is an open-source interactive theorem prover and proof checker (a successor of Brown's Egal) whose default foundation is higher-order Tarski–Grothendieck set theory: Church-style simple type theory with a base type of sets plus the TG axioms. It supports four Proofgold theories (Egal HOTG, Mizar HOTG, hereditarily-finite sets, and HOAS) and is the authoring tool for the Proofgold formal-proof blockchain.
**Relevance:** A live, deployed proof assistant that literally is "Church's typed HOL + a set-theoretic universe" — the working engineering instance of building set theory inside HOL where comprehension is the typed lambda/description machinery rather than a first-order schema. Direct architectural precedent for a HOL-based set foundation.

---

**★ CANON — Metamath: A Computer Language for Mathematical Proofs**
Norman D. Megill, David A. Wheeler — 2019 — Lulu Press (2nd ed.); set.mm database, us.metamath.org — manual
**Link:** https://us.metamath.org/index.html
**PDF:** https://us.metamath.org/downloads/metamath.pdf
The reference manual for Metamath, a minimalist proof language built entirely on substitution of metavariables, together with set.mm, its flagship database formalizing tens of thousands of theorems on a first-order ZFC foundation (Tarski–Megill axiomatization of predicate logic plus the ZFC axioms, including the Replacement/Separation schemas as axiom-schema templates). It is the largest machine-checked development of mathematics over an explicitly first-order, schema-based ZFC.
**Relevance:** The practical-tooling counterpoint to the HOL-based provers above: set.mm shows what formalizing set theory looks like when you KEEP the first-order comprehension schemas (encoded as metavariable templates) rather than collapsing them via HOL typing — a concrete contrast case for the Verus/HOL design.

---

**Metamath Zero: From Logic, to Proof Assistant, to Verified Compiler**
Mario Carneiro — 2022 — PhD dissertation, Carnegie Mellon University — thesis
**Link:** https://digama0.github.io/mm0/
**PDF:** https://digama0.github.io/mm0/thesis.pdf
Carneiro designs Metamath Zero (MM0), a minimal multi-sorted first-order metalogic with a formally verified verifier, and uses it to bootstrap trust from logic down to a verified compiler. The work includes the metamathematics of giving set.mm/ZFC a model and a rigorous treatment of how schematic first-order theories are checked, plus translations among HOL Light, Coq, Isabelle, and Metamath.
**Relevance:** State-of-the-art on the engineering of a trustworthy first-order set-theory foundation and on cross-foundation translation (HOL ↔ set theory) — complementing the HOL-in-set-theory / set-theory-in-HOL papers and the project's own backend-translation concerns.

---

*Cross-references:* The first-order Tarski–Grothendieck axiom base (Mizar) and the detailed FOL-vs-HOL TG comparison (Brown–Pąk, *A Tale of Two Set Theories*) live in **§05**; the set-theoretic standard semantics of the HOL kernel (Pitts) and Church's STT basis are in **§04**.
