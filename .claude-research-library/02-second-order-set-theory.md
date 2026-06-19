# 02 — Second-Order / HOL Set Theory and the Schema Collapse

*The positive HOL analog of NBG. When Separation/Replacement are stated as SINGLE second-order axioms quantifying over predicates (rather than first-order schemas), the schema "collapses" for free — and you gain quasi-categoricity: second-order ZF pins the universe down to the V_κ for κ inaccessible (Zermelo). These works develop the second-order/HOL set theories where this happens, the GBC→KM comprehension-strength hierarchy, and the crucial result that the categoricity payoff survives in Henkin/typed semantics — the exact regime of a HOL prover and of Verus's `set = predicate` model.*

---

**★ CANON — Über Grenzzahlen und Mengenbereiche: Neue Untersuchungen über die Grundlagen der Mengenlehre**
Ernst Zermelo — 1930 — *Fundamenta Mathematicae* 16, pp. 29–47 — paper
**Link:** https://eudml.org/doc/212506
**PDF:** https://eudml.org/doc/212506
Zermelo's final axiomatization of set theory, given in essentially second-order form (Separation/Aussonderung quantifies over arbitrary subsets, i.e. predicates). The paper proves the quasi-categoricity ("Isomorphiesatz"): any two full models of the second-order ZF axioms are either isomorphic or one is isomorphic to a rank-initial segment (a Normalbereich V_κ for κ strongly inaccessible) of the other. It also introduces the cumulative-hierarchy picture and the procession of natural models cut off at inaccessible cardinals.
**Relevance:** The historical origin of the entire "schema collapses in second-order logic" phenomenon: second-order Separation is a single axiom (over predicates) rather than ZF's first-order schema, and this buys quasi-categoricity. The positive HOL analog of NBG and the direct ancestor of the Verus/Isabelle-HOL "a set is a predicate" model.

---

**★ CANON — Foundations without Foundationalism: A Case for Second-Order Logic**
Stewart Shapiro — 1991 — Oxford Logic Guides 17, Oxford University Press — book
**Link:** https://philpapers.org/rec/SHAFWF
A book-length philosophical and technical case that full-semantics second-order logic is the right vehicle for codifying mathematical practice. It develops second-order semantics in detail, contrasts it with Henkin/first-order semantics, and shows how genuinely second-order concepts (finitude, well-ordering, the natural- and real-number structures, set-theoretic notions) are categorically captured. It treats second-order ZFC, the collapse of the first-order Separation/Replacement schemas into single second-order axioms, Zermelo quasi-categoricity, and the relation of set-existence principles to inaccessible cardinals.
**Relevance:** The canonical modern statement of why moving to second-order/HOL turns ZFC's infinitely-many-instance Separation and Replacement schemas into single axioms over predicates — precisely the schema collapse that is the HOL counterpart of NBG's finite axiomatization. Directly frames the research question.

---

**How We Learn Mathematical Language**
Vann McGee — 1997 — *The Philosophical Review* 106(1), pp. 35–68 — article
**Link:** https://philpapers.org/rec/MCGHWL
Argues, using a categoricity theorem for open-ended/full second-order ZFC, that the language of set theory has determinate reference: every sentence has a determinate truth value because the second-order axioms — single comprehension/separation axioms in place of first-order schemas — pin the universe down up to isomorphism (quasi-categorically). Invokes what is now called internal/open-ended categoricity to defend mathematical realism.
**Relevance:** A widely cited philosophical anchor for the claim that second-order ZFC's schema-collapse yields a (quasi-)categorical, determinate universe — the foundational motivation for preferring the HOL/second-order rendering over the first-order schematic one.

---

**★ CANON — Models of Second-Order Zermelo Set Theory**
Gabriel Uzquiano — 1999 — *Bulletin of Symbolic Logic* 5(3), pp. 289–302 — paper
**Link:** https://philpapers.org/rec/UZQMOS
**PDF:** https://www.cambridge.org/core/services/aop-cambridge-core/content/view/168926643F0C8E4E9F3A07AECB242137/S1079898600006892a.pdf/models_of_secondorder_zermelo_set_theory.pdf
Investigates models of second-order Zermelo set theory (second-order Separation but without Replacement). Whereas Zermelo's theorem pins down the models of second-order ZF as exactly the V_κ for κ strongly inaccessible, Uzquiano shows that dropping Replacement and keeping only second-order Separation admits models not isomorphic to any V_κ for a limit ordinal κ. The paper isolates the precise role second-order Replacement plays in delivering full quasi-categoricity.
**Relevance:** Pinpoints which second-order axiom (Replacement) does the categoricity work once Separation is already a single second-order axiom — essential for understanding exactly how much "collapse" each schema-to-axiom move buys in the HOL setting.

---

**★ CANON — Second Order Logic or Set Theory?**
Jouko Väänänen — 2012 — *Bulletin of Symbolic Logic* 18(1), pp. 91–121 — paper
**Link:** https://projecteuclid.org/euclid.bsl/1327328440
**PDF:** https://users.ox.ac.uk/~reflect/Reflection_and_Incompleteness/Events_files/Vaananen.pdf
Compares the "second-order view" and the "set-theoretic view" as foundations, arguing the apparent conflict is largely illusory. The key technical contribution is internal categoricity, which extends second-order categoricity results to Henkin (general) models and shows set theory itself enjoys the same internal categoricity; conversely second-order logic admits non-standard Henkin models just as set theory does. The standard contrast "second-order logic is categorical, set theory has non-standard models" dissolves.
**Relevance:** Directly addresses whether the categoricity power usually attributed to second-order/HOL set theory requires full semantics, or survives in Henkin/typed-comprehension semantics — important for the Verus/Isabelle-HOL model, whose `set = predicate` types are effectively a Henkin-style typed second-order setting.

---

**★ CANON — Internal Categoricity in Arithmetic and Set Theory**
Jouko Väänänen, Tong Wang — 2015 — *Notre Dame Journal of Formal Logic* 56(1), pp. 121–134 — paper
**Link:** https://philpapers.org/rec/VNNICI
**PDF:** https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-56/issue-1/Internal-Categoricity-in-Arithmetic-and-Set-Theory/10.1215/00294527-2835038.pdf
Proves that categoricity of the second-order Peano axioms follows from the comprehension axioms alone, and likewise that categoricity of the second-order ZF axioms (given the order type of the ordinals) follows from comprehension — crucially without full second-order semantics: Henkin semantics suffices for these "internal" categoricity results. Shows non-standard models and categoricity can coherently coexist.
**Relevance:** Shows the schema-collapse-to-categoricity engine runs on the comprehension axiom even in Henkin/typed semantics — the precise semantic regime of a typed-HOL prover. Strong evidence that Verus/Isabelle typed comprehension is enough to get the categoricity payoff without committing to full second-order semantics.

---

**Second-Order Logic and Set Theory**
Jouko Väänänen — 2015 — *Philosophy Compass* 10(7), pp. 463–478 — survey
**Link:** https://compass.onlinelibrary.wiley.com/doi/abs/10.1111/phc3.12229
**PDF:** https://www.mv.helsinki.fi/home/jvaanane/Vaananen_Compass.pdf
A survey of how second-order logic and set theory relate as foundational frameworks: full vs Henkin semantics, categoricity and quasi-categoricity, the collapse of axiom schemas into single second-order axioms, internal categoricity, and how the cumulative hierarchy corresponds to iterated power-set/second-order quantification. Argues the two frameworks are closer than usually assumed.
**Relevance:** Accessible survey of exactly the comparison at issue — when Separation/Replacement schemas become single second-order axioms and what categoricity that delivers — by the leading author on second-order foundations.

---

**Model Theory of Second Order Logic**
Jouko Väänänen — 2025 — arXiv:2508.01788 [math.LO] — preprint
**Link:** https://arxiv.org/abs/2508.01788
**PDF:** https://arxiv.org/pdf/2508.01788
A recent systematic treatment of the model theory of (full and Henkin) second-order logic, covering categoricity and quasi-categoricity, the comprehension axiom, the relationship between second-order logic and set theory, internal categoricity, and how second-order axiomatizations of arithmetic and set theory behave under different semantics. Synthesizes Väänänen's program on second-order foundations.
**Relevance:** Up-to-date reference consolidating the model-theoretic machinery behind why second-order comprehension collapses first-order schemas and what categoricity that yields — useful background for the HOL-set-theory representation question.

---

**★ CANON — Open Determinacy for Class Games**
Victoria Gitman, Joel David Hamkins — 2017 — in *Foundations of Mathematics* (Contemporary Mathematics 690), AMS, pp. 121–143 — paper
**Link:** https://victoriagitman.github.io/publications/2015/09/10/open-determinacy-for-class-games.html
**PDF:** https://victoriagitman.github.io/files/Proper-class-games.pdf
Works inside the hierarchy of second-order (class) set theories between Gödel–Bernays GBC and Kelley–Morse KM. Proves clopen determinacy for class games is exactly equivalent to elementary transfinite recursion (ETR) along well-founded class relations, while open class determinacy sits strictly higher — provable in GBC + Π¹₁-comprehension and hence in KM, exceeding ZFC in consistency strength. Locates these determinacy principles precisely in the second-order comprehension hierarchy.
**Relevance:** A flagship paper of the modern revival of second-order set theory; it calibrates the strength of fragments of the second-order class-comprehension schema (GBC, ETR, Π¹₁-CA, KM), showing how much logical power each level of class comprehension adds beyond the finitely-axiomatized GBC base.

---

**★ CANON — The Structure of Models of Second-order Set Theories**
Kameryn J. Williams — 2018 — Ph.D. dissertation, CUNY Graduate Center; arXiv:1804.09526 — thesis
**Link:** https://arxiv.org/abs/1804.09526
**PDF:** https://arxiv.org/pdf/1804.09526
A contribution to the modern revival of second-order set theory studied via its models. Four main results: (1) the poset of T-realizations of a fixed countable ZFC model (T = GBC or KM) embeds every countable partial order; (2) T-realizability is preserved to submodels for many T; (3) a fine hierarchy of transfinite recursion principles from GBC up to KM, stratified by formula complexity and recursion height; (4) strong theories such as KM and Π¹₁-CA have no least transitive model, while weaker theories from GBC up to GBC + ETR_Ord do.
**Relevance:** The definitive single reference mapping the landscape from the finitely-axiomatizable base GBC up to non-finitely-axiomatizable KM, organized exactly by how much of the second-order comprehension schema each theory takes — the heart of where schemas collapse vs. remain genuinely schematic.

---

**Minimum Models of Second-Order Set Theories**
Kameryn J. Williams — 2019 — *Journal of Symbolic Logic* 84(2), pp. 589–620; arXiv:1709.03955 — paper
**Link:** https://arxiv.org/abs/1709.03955
**PDF:** https://arxiv.org/pdf/1709.03955
Studies which second-order set theories have minimum (least) transitive models. The comprehension strength matters sharply: theories at or above KM or Π¹₁-comprehension fail to have a least transitive model, whereas the finitely-axiomatized base GBC and intermediate theories up to GBC + ETR_Ord do possess least transitive models. Provides exact constructions distinguishing the levels of the second-order comprehension hierarchy.
**Relevance:** Concretely demonstrates the metamathematical gap between finitely-axiomatizable GBC (NBG-with-choice) and the genuinely schematic, non-finitely-axiomatizable KM — the boundary case for "does the second-order schema collapse?"

---

**Class Choice and the Surprising Weakness of Kelley–Morse Set Theory**
Victoria Gitman, Joel David Hamkins, Thomas A. Johnstone — 2016 (rev.) — preprint / arXiv — preprint
**Link:** https://victoriagitman.github.io/publications/2019/04/11/kelley-morse-theory-does-not-prove-the-class-fodor-principle.html
**PDF:** https://victoriagitman.github.io/files/kelleymorse2.pdf
Shows that Kelley–Morse KM — GBC plus the full impredicative second-order class-comprehension schema — is weaker than commonly assumed: it does not prove the class choice scheme and related principles. The authors argue KM augmented with class choice (KM⁺) is the more robust theory and propose it as the right foundation for second-order set theory, since KM alone fails to settle basic questions about classes.
**Relevance:** Clarifies what the full impredicative second-order comprehension schema of KM does and does not buy, and why even the maximal class theory is subtle — directly relevant to choosing how strong a typed-HOL comprehension principle to adopt for a Verus/Isabelle set model.

---

**Kelley–Morse Set Theory Does Not Prove the Class Fodor Principle**
Victoria Gitman, Joel David Hamkins, Asaf Karagila — 2020 — *Fundamenta Mathematicae* 254, pp. 285–306; arXiv:1904.04190 — paper
**Link:** https://arxiv.org/abs/1904.04190
**PDF:** https://arxiv.org/pdf/1904.04190
Proves that KM (with full impredicative second-order comprehension) does not prove the class Fodor principle — that every regressive class function on a stationary class of ordinals is constant on a stationary subclass — and is consistent with strong failures of it. Demonstrates further limitations of the maximal second-order class theory and the importance of supplementary class-choice/collection principles.
**Relevance:** Further evidence on the exact logical content of the impredicative second-order comprehension schema in the strongest standard class theory; shows "one big second-order axiom" is not automatically as strong as intuition suggests, sharpening the comparison with NBG/GBC's finite axiomatization.

---

**Categorical Large Cardinals and the Tension Between Categoricity and Set-Theoretic Reflection**
Joel David Hamkins, Hans Robin Solberg — 2020 — arXiv:2009.07164 [math.LO] — preprint
**Link:** https://arxiv.org/abs/2009.07164
**PDF:** https://arxiv.org/pdf/2009.07164
Building on Zermelo's quasi-categoricity characterization of the models of second-order ZFC (the V_κ for κ inaccessible), the paper studies when ZFC₂ becomes fully (not merely quasi-) categorical upon adding a first- or second-order sentence, defining the heights of these uniquely-determined models as the "categorical large cardinals." It analyzes the tension between categoricity (a determinate universe) and set-theoretic reflection (which pushes toward non-categoricity).
**Relevance:** A current deep dive into exactly what Zermelo's second-order quasi-categoricity delivers and its limits — the precise payoff of having Separation/Replacement as single second-order axioms — and the foundational trade-offs of leaning on that categoricity.

---

**Universism and Extensions of V**
Carolin Antos, Neil Barton, Sy-David Friedman — 2021 — *The Review of Symbolic Logic* 14(1), pp. 112–154; arXiv:1708.05751 — paper
**Link:** https://arxiv.org/abs/1708.05751
**PDF:** https://arxiv.org/pdf/1708.05751
Develops V-logic, a logic with built-in class/ideal-outer-model resources, to make sense of extending the set-theoretic universe V from a universist standpoint. The technique connects satisfaction in ideal outer models to impredicative class theories (Morse–Kelley and stronger), analyzing the class-theoretic machinery (hyperclasses, satisfaction predicates) needed.
**Relevance:** A modern entry into second-order/class-theoretic set theory and the strength hierarchy NBG < MK < hyperclass theories — the same comprehension-strength ladder that, in HOL, is governed by how impredicative the single second-order comprehension axiom is allowed to be.

---

**★ CANON — Categoricity Results and Large Model Constructions for Second-Order ZF in Dependent Type Theory**
Dominik Kirst, Gert Smolka — 2018 — *Journal of Automated Reasoning* 63, pp. 415–438 (orig. ITP 2017) — paper
**Link:** https://link.springer.com/article/10.1007/s10817-018-9480-6
**PDF:** https://ps.uni-saarland.de/Publications/documents/KirstSmolka_2017_Categoricity.pdf
Formalizes second-order ZF inside the constructive dependent type theory of Coq (assuming excluded middle) and machine-checks Zermelo's embedding theorem, categoricity in every cardinality (equipotent models are isomorphic), and the correspondence between inner models and Grothendieck universes. A central device is an inductive definition of the cumulative hierarchy that eliminates the need for ordinals and transfinite recursion.
**Relevance:** The closest existing work to the Verus/Isabelle-HOL goal: it represents second-order ZF inside a typed higher-order/dependent type theory of a proof assistant, with second-order Separation/Replacement realized via the type theory's predicate/comprehension structure rather than first-order schemas — a concrete template for `set = predicate` typed comprehension.

---

**Zermelo's Axiomatization of Set Theory (Stanford Encyclopedia of Philosophy)**
Michael Hallett — 2013 — Stanford Encyclopedia of Philosophy — encyclopedia
**Link:** https://plato.stanford.edu/entries/zermelo-set-theory/
A detailed scholarly account of Zermelo's 1908 axiomatization and its 1930 second-order recasting (Über Grenzzahlen und Mengenbereiche). It explains the original Separation axiom as a schema, the move to definite properties, and Zermelo's 1930 second-order viewpoint with the Grenzzahl (boundary-number) analysis of models V_κ, which underlies quasi-categoricity.
**Relevance:** Authoritative companion to the Zermelo 1930 primary text and the Uzquiano/Väänänen second-order-Zermelo papers: it frames why moving Separation from a first-order schema to a second-order axiom yields quasi-categoricity — the canonical case of a schema collapsing in second-order logic.

---

*Cross-references:* The finite-axiomatizability metamath underlying GBC vs KM (and "KM implies Con(ZFC)") is in **§01**; the Henkin-general-models foundation that makes typed second-order comprehension complete is in **§04**; concrete prover realizations of HOL-hosted set theory are in **§03**.
