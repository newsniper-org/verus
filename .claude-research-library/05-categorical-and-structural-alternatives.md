# 05 — Categorical and Structural Alternatives (finitely-presented, schema-free)

*The structural counterpart of the HOL "one axiom" move. Lawvere's ETCS replaces ZF's first-order Separation/Replacement schemas with a fixed list of categorical axioms; in a topos, comprehension becomes a single piece of universal structure — the power object / subobject classifier Ω — so "subset of A" is literally a map A → Ω, exactly the `set = predicate` picture, proven schema-free. This section also includes the material/structural dictionary (which first-order schema each structural axiom does and does not replace) and the first-order Tarski–Grothendieck set theory that the HOTG/Egal work re-presents in HOL.*

---

**★ CANON — An Elementary Theory of the Category of Sets**
F. William Lawvere — 1964 — *Proceedings of the National Academy of Sciences USA* 52, pp. 1506–1511 — paper
**Link:** https://www.pnas.org/doi/10.1073/pnas.52.6.1506
**PDF:** https://www.pnas.org/doi/epdf/10.1073/pnas.52.6.1506
Lawvere's founding paper of structural set theory. It adjoins eight elementary (first-order) axioms to the abstract theory of an Eilenberg–Mac Lane category to characterize the category of sets and mappings: finite roots (terminal/initial objects, products, equalizers), exponentiation (cartesian closure), a subobject classifier / well-pointedness via a two-element truth object, a natural-number object, and choice. Sets have no internal membership structure; everything is expressed through morphisms, so "elements" are maps out of the terminal object.
**Relevance:** The prototype of a structural, schema-free (finitely presented) set theory: ETCS replaces ZF's first-order Separation/Replacement schemas with a fixed list of categorical axioms — the structural analog of the HOL move where comprehension is a single typed axiom rather than infinitely many instances. The direct comparison point for a HOL-style ISet model.

---

**★ CANON — An Elementary Theory of the Category of Sets (long version) with commentary**
F. William Lawvere; commentary by Colin McLarty and the author — 2005 — *Reprints in Theory and Applications of Categories*, No. 11, pp. 1–35 — reprint
**Link:** http://www.tac.mta.ca/tac/reprints/articles/11/tr11.abs.html
**PDF:** http://www.tac.mta.ca/tac/reprints/articles/11/tr11.pdf
The expanded 1965 University of Chicago manuscript version of Lawvere's PNAS announcement, reprinted with a new author introduction and a commentary by Colin McLarty. It lays out the full elementary (first-order) axiomatization of the category of sets and explains how ordinary set-theoretic constructions (subsets, quotients, function sets, the natural numbers) are recovered structurally, with extended discussion of the intent to give an autonomous, membership-free foundation.
**Relevance:** The authoritative, freely available text of ETCS with modern commentary on exactly how its finite categorical axiom base substitutes for ZF's first-order schemas — the cleanest primary source for the "schema collapses to a fixed list of axioms" theme in a structural/elementary setting.

---

**★ CANON — Sets for Mathematics**
F. William Lawvere and Robert Rosebrugh — 2003 — Cambridge University Press — book
**Link:** https://www.cambridge.org/core/books/sets-for-mathematics/E0D6F26FE1A86F3CF5A55C75D40D5848
**PDF:** http://assets.cambridge.org/052180/4442/sample/0521804442ws.pdf (sample)
A textbook developing set theory as "the algebra of mappings," building a structural (categorical) foundation for algebra, geometry, and analysis from axioms expressing universal properties of sums, products, mapping sets (exponentials), power sets, and natural-number recursion. It is, in effect, a pedagogical full-length development of ETCS and its variable-set (topos) extensions.
**Relevance:** Book-length demonstration that a finitely axiomatized, universal-property-based (HOL-flavored, exponential/power-object) presentation of sets is self-sufficient — the constructive bridge between Lawvere's terse ETCS axioms and the typed-comprehension intuition underlying a HOL set model.

---

**★ CANON — Rethinking Set Theory**
Tom Leinster — 2014 — *The American Mathematical Monthly* 121(5), pp. 403–415 (preprint arXiv:1212.6543) — article
**Link:** https://arxiv.org/abs/1212.6543
**PDF:** https://arxiv.org/pdf/1212.6543
A Chauvenet-Prize-winning expository account of ETCS for working mathematicians, deliberately written without ever defining a category. Leinster recasts ETCS as ten "thoroughly mundane" statements about sets and functions — the everyday principles mathematicians use unconsciously — taken as axioms, and argues this is a fully adequate, more practice-aligned alternative to ZFC.
**Relevance:** The most accessible entry point showing that a finite, schema-free list of axioms about sets-and-functions (no Separation/Replacement schema) suffices for ordinary mathematics. Directly motivates treating a set as a typed object with function structure — the same stance as the Verus/HOL `ISet<A> = (A → bool)` model.

---

**★ CANON — Introduction to Higher-Order Categorical Logic**
Joachim Lambek and Philip J. Scott — 1986 — Cambridge Studies in Advanced Mathematics no. 7, Cambridge University Press — book
**Link:** https://www.cambridge.org/9780521356534
Lambek and Scott reconcile mathematical logic with category theory, establishing the trichotomy: typed lambda-calculi (a formulation of higher-order logic) correspond exactly to cartesian closed categories; intuitionistic higher-order type theory corresponds to topos theory (where comprehension is the subobject classifier / power object); and recursive functions are treated in Part III. The book builds the equivalence between the syntax of higher-order logic / type theory and the categorical semantics of toposes, with full treatment of the internal language.
**Relevance:** The reference proving that higher-order logic, typed lambda calculus, and topos structure are three faces of one thing — so the topos power-object axiom IS typed comprehension. This is the formal backbone for why, in a HOL/typed setting, comprehension is a single axiom and the first-order schema disappears; it connects the HOL "one axiom suffices" point to the topos alternatives.

---

**★ CANON — Toposes and Local Set Theories: An Introduction**
John L. Bell — 1988 — Oxford Logic Guides 14, Oxford University Press (repr. Dover 2008) — book
**Link:** https://global.oup.com/academic/product/toposes-and-local-set-theories-9780198532743
Bell presents toposes as exactly the models of "local set theories" — theories formulated in a typed, intuitionistic higher-order language. Each topos has an internal language that is a higher-order type theory, and conversely each local set theory generates a syntactic topos, giving a tight correspondence between topos structure and typed HOL.
**Relevance:** The clearest statement that a topos is the semantic incarnation of typed higher-order logic, where set-comprehension is governed by a single power-object adjunction rather than a schema. The structural/topos version of "one typed comprehension axiom suffices" — the deepest link between topos set theory and a HOL set model.

---

**★ CANON — Sheaves in Geometry and Logic: A First Introduction to Topos Theory**
Saunders Mac Lane and Ieke Moerdijk — 1992 — Universitext, Springer-Verlag — book
**Link:** https://link.springer.com/book/10.1007/978-1-4612-0927-0
The standard graduate introduction to topos theory, covering sheaves, Grothendieck topologies, elementary toposes, geometric morphisms, classifying toposes, and — centrally for foundations — the chapter "Topoi and Logic," which develops the Mitchell–Bénabou internal language and Kripke–Joyal semantics showing that every elementary topos models intuitionistic higher-order (typed) logic.
**Relevance:** The canonical technical account of the topos internal language: power objects give comprehension as a universal property (one axiom), and the subobject classifier Ω makes "subset of A" literally a map A → Ω — exactly the "a set is a predicate A → bool" picture of the HOL/ISet model, but proven schema-free.

---

**★ CANON — Comparing Material and Structural Set Theories**
Michael A. Shulman — 2019 — *Annals of Pure and Applied Logic* 170(4), pp. 465–504 (arXiv:1808.05204) — paper
**Link:** https://arxiv.org/abs/1808.05204
**PDF:** https://arxiv.org/pdf/1808.05204
Shulman studies elementary theories of well-pointed (pre)toposes as structural set theories and compares them precisely to material (membership-based) set theories such as ZF(C) and its bounded/predicative fragments. Using internal well-founded relations he constructs each kind of theory from the other, calibrating exactly which structural axioms correspond to Separation, Collection, Replacement, etc.
**Relevance:** The modern, definitive dictionary between structural (finite/categorical) and material (schema-based) set theories — it shows exactly which first-order schemas a structural axiom replaces or fails to replace, the precise technical heart of the finite-axiomatization-for-a-HOL-style-theory question.

---

**Stack Semantics and the Comparison of Material and Structural Set Theories**
Michael A. Shulman — 2010 — arXiv:1004.3802 [math.CT] — preprint
**Link:** https://arxiv.org/abs/1004.3802
**PDF:** https://arxiv.org/pdf/1004.3802
Shulman extends the internal logic of a (pre)topos to a "stack semantics" that interprets unbounded quantifiers ranging over the proper class of all objects. He shows Collection and Replacement are automatically valid in the stack semantics of any topos, and that adding a separation schema in this semantics yields a topos-theoretic axiom of full ZF strength — recovering material set theory from a topos via internal well-founded relations.
**Relevance:** Directly tackles how the unbounded first-order schemas (Replacement/Separation) reappear in a structural/HOL-style topos setting: some collapse for free (Replacement), while full Separation must be re-added as a genuine schema. A precise map of which schemas a typed/structural framework genuinely eliminates and which it does not.

---

**Categorical Set Theory: A Characterization of the Category of Sets**
Gerhard Osius — 1974 — *Journal of Pure and Applied Algebra* 4(1), pp. 79–119 — paper
**Link:** https://doi.org/10.1016/0022-4049(74)90032-2
Osius gives the original topos-theoretic reconstruction of membership-based set theory: using internal well-founded relations inside an elementary topos he defines "ZF-sets" as objects, shows ETCS-like axioms correspond to Zermelo strength, and produces an extension equiconsistent with ZF(C). This is the first rigorous bridge between structural/topos set theory and material ZF.
**Relevance:** The foundational source of the well-founded-relations technique later used by Shulman — it pioneered the method of recovering the schema-based material hierarchy from a finitely-axiomatized structural topos, the precise mechanism connecting a HOL/structural set theory to ordinary ZF.

---

**SEAR: Sets, Elements And Relations (structural set theory)**
Michael Shulman (nLab exposition) — 2010 — nLab encyclopedia entry / project page — encyclopedia
**Link:** https://ncatlab.org/nlab/show/SEAR
SEAR is a structural set theory designed to be ZF-strength yet usable without category-theoretic prerequisites. It takes sets, elements, and relations as three primitive sorts and is built from a small number of axioms plus a relational-comprehension schema (a property of elements yields a relation), with tabulations giving subsets and quotients; membership is a typing relation, not a global predicate.
**Relevance:** A deliberately accessible structural alternative to ETCS that makes explicit which parts can be axioms and which remain a (relational) comprehension schema — a useful contrast case for how far a typed/relational HOL-flavored set theory can be pushed toward finite axiomatization.

---

**Exploring Categorical Structuralism**
Colin McLarty — 2004 — *Philosophia Mathematica* 12(1), pp. 37–53 — article
**Link:** https://doi.org/10.1093/philmat/12.1.37
**PDF:** https://pages.jh.edu/rrynasi1/FoundationsOFMath/Literature/McLarty2004ExploringCategoricalStructuralsim.pdf
McLarty defends categorical (ETCS / well-pointed-topos) foundations against Geoffrey Hellman's objections, clarifying what the axioms assume, how existence is handled, and the sense in which a categorical theory of sets is autonomous rather than parasitic on ZF. It situates ETCS as a genuine, self-standing structural set theory.
**Relevance:** Establishes philosophically that the ETCS-style finite axiom base is a legitimate stand-alone foundation, not merely a reformulation of ZF — important framing for arguing that a HOL/structural set theory can replace a schema-laden first-order one.

---

**Learning from Questions on Categorical Foundations**
Colin McLarty — 2005 — *Philosophia Mathematica* 13(1), pp. 44–60 — article
**Link:** https://doi.org/10.1093/philmat/nki006
A response to questions raised by Hellman and Feferman about whether category theory can serve as an autonomous foundation. McLarty discusses the status of ETCS and related categorical theories, the role of schematic vs. fixed axioms, and how categorical foundations relate to mathematical practice.
**Relevance:** Engages directly with the metamathematical objections to using a categorical/structural (and thus schema-light) theory as a foundation, including the autonomy and circularity worries — useful for anticipating critiques of a HOL-based set foundation.

---

**Numbers Can Be Just What They Have to Be**
Colin McLarty — 1993 — *Noûs* 27(4), pp. 487–498 — article
**Link:** https://www.jstor.org/stable/2215789
McLarty argues that Benacerraf's structuralist insight about the natural numbers is best realized in categorical (ETCS-style) set theory rather than orthodox ZF: any two natural-number objects are provably isomorphic and "provably indiscernible," so numbers have exactly the properties their structural role requires and no spurious set-theoretic ones. This connects to ETCS's proof-theoretic strength (equiconsistent with bounded Zermelo with choice, BZC).
**Relevance:** Pins down ETCS's strength relative to ZF (weaker — bounded Zermelo, no Replacement schema) and shows the structural natural-number object behaves uniquely up to isomorphism — the structural counterpart of HOL categoricity arguments, and a concrete data point on what a finite/schema-light axiom base buys and costs.

---

**★ CANON — Tarski Grothendieck Set Theory**
Andrzej Trybulec — 1990 — *Formalized Mathematics* 1(1), Axiomatics (Mizar Mathematical Library) — article
**Link:** https://fm.mizar.org/1990-1/pdf1-1/tarski.pdf
**PDF:** https://fm.mizar.org/1990-1/pdf1-1/tarski.pdf
The official axiomatics file underlying the Mizar proof assistant: ZFC-style extensionality, pairing, union, power set, regularity, the Fraenkel (replacement) scheme, and Tarski's Axiom A (every set lies in a Grothendieck universe), which entails choice and the existence of arbitrarily large inaccessible cardinals. This is the first-order Tarski–Grothendieck (TG) set theory that Mizar (and Metamath) build mathematics on.
**Relevance:** The reference first-order TG axiom base used by a major prover — the material counterpart that the higher-order Egal/Megalodon systems re-present in HOL. Its replacement schema and Tarski's universe axiom are exactly the parts a HOL re-presentation must reconcile, making it the canonical comparison point for the HOL-TG work.

---

**A Tale of Two Set Theories**
Chad E. Brown, Karol Pąk — 2019 — CICM 2019, LNCS/LNAI 11617, Springer, pp. 44–60 (arXiv:1907.08368) — paper
**Link:** https://arxiv.org/abs/1907.08368
**PDF:** https://arxiv.org/pdf/1907.08368
Brown and Pąk describe the precise relationship between the first-order Tarski–Grothendieck set theory of Mizar and the higher-order Tarski–Grothendieck set theory of Egal, including a nontrivial proof of Tarski's Axiom A in Egal and the construction of first-order representations for the higher-order terms and propositions, enabling a Grothendieck-universe operator to be built in Mizar. It shows how certain higher-order terms and propositions in Egal have equivalent first-order presentations.
**Relevance:** A careful mapping between a higher-order set theory (Egal) and a first-order one (Mizar/TG), a concrete worked example of exactly how moving to HOL changes the axiom base and where schemas become single typed principles — illuminating which set-theoretic axioms are first-order artifacts versus genuinely higher-order, the core distinction motivating the finite-axiomatization-for-HOL question.

---

*Cross-references:* The HOTG/Egal prover realization built on this TG base, the Isabelle/HOL–Isabelle/Mizar alignment, and Megalodon live in **§03**; the typed-lambda/Church-STT view of comprehension that the topos power object internalizes is in **§04**; the FOL non-finite-axiomatizability of ZF (with its Replacement schema, inherited by first-order TG) is in **§01**.
