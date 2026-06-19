# 01 — The Metamathematics of Finite Axiomatizability

*This is the FOL baseline. Finite axiomatization is a first-order device for eliminating comprehension SCHEMAS: NBG folds ZFC's infinite Separation/Replacement schema into finitely many class-existence axioms, while ZF and impredicative Kelley–Morse provably resist any finite axiomatization (via the reflection theorem + Gödel incompleteness). These works establish the "NBG yes, ZF no, MK no" dichotomy that the HOL/second-order collapse is contrasted against, plus the independent NF schema-collapse that bridges toward typed comprehension.*

---

**★ CANON — Eine Axiomatisierung der Mengenlehre (An Axiomatization of Set Theory)**
John von Neumann — 1925 — *Journal für die reine und angewandte Mathematik* (Crelle) 154, pp. 219–240; Eng. trans. in van Heijenoort, *From Frege to Gödel* (1967), pp. 393–413 — paper
**Link:** https://eudml.org/doc/149573
Von Neumann's first major foundational paper and the historical origin of the NBG line. Rather than taking set and membership as primitive, he axiomatizes in terms of "things" (I-things, II-things) and functions, and famously introduces the size-limitation idea: a class is proper precisely when it is in bijection with the whole universe. Crucially this is the FIRST finite axiomatization of set theory, replacing the Replacement/Separation schemas with finitely many statements about functions/classes.
**Relevance:** Ground zero of the entire "finite axiomatization via classes" story. Von Neumann's insight — quantify over classes/functions to fold an infinite first-order schema into finitely many axioms — is exactly the FOL device whose HOL analog (second-order comprehension as one axiom) the project studies.

---

**★ CANON — A System of Axiomatic Set Theory (Parts I–VII)**
Paul Bernays — 1937–1954 — *The Journal of Symbolic Logic* — I: vol. 2 (1937) 65–77; II: vol. 6 (1941) 1–17; III: vol. 7 (1942) 65–89; IV: vol. 7 (1942) 133–145; V: vol. 8 (1943) 89–106; VI: vol. 13 (1948) 65–79; VII: vol. 19 (1954) 81–96 — article series
**Link:** https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/paul-bernays-a-system-of-axiomatic-set-theorypart-i-the-journal-of-symbolic-logic-vol-2-1937-pp-6577-see-errata-the-journal-of-symbolic-logic-vol-2-1937-p-iv/5C103609C4456961D10856512A657FC8
**PDF:** https://doc.rero.ch/record/301843/files/S0022481200087570.pdf
Bernays's seven-part JSL series develops and streamlines von Neumann's class-based theory into the two-sorted (sets and classes) system now standard as NBG. The series isolates the finitely many class-existence axioms that generate all comprehension instances and works out the relation to ZF, choice, and the cumulative hierarchy; Parts II–VII are the technically decisive installments. It is the primary-source origin of the Bernays-style finite class-formation axioms.
**Relevance:** The definitive working-out of HOW a small finite list of class axioms replaces the Separation/Replacement schema — the precise FOL mechanism that HOL gets "for free" via one second-order comprehension axiom.

---

**★ CANON — Axiomatic Set Theory (with a Historical Introduction by A. A. Fraenkel)**
Paul Bernays (Fraenkel, Part I) — 1958 — North-Holland, Amsterdam (Dover reprint 1991) — book
**Link:** https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/paul-bernays-axiomatic-set-theory-studies-in-logic-and-the-foundations-of-mathematics-northholland-publishing-company-amsterdam1958-viii-226-pp-a-a-fraenkel-part-i-historical-introduction-therein-pp-335/A2EB9EF82AC570036D2BADCBAB25FE35
Bernays's book-length development of NBG class/set theory, consolidating the 1937–1954 JSL series. It recasts von Neumann's unwieldy function-based theory into a two-sorted system with sets and classes primitive, and develops set theory from the finite class-existence axioms; Fraenkel's Part I supplies the historical introduction.
**Relevance:** The standard monographic reference for NBG class theory and its finite axiomatization — the FOL mechanism whose HOL counterpart is a single comprehension axiom.

---

**★ CANON — The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory**
Kurt Gödel — 1940 — Princeton University Press, Annals of Mathematics Studies no. 3 — monograph
**Link:** https://press.princeton.edu/books/paperback/9780691079271/consistency-of-the-continuum-hypothesis-am-3-volume-3
Gödel's classic monograph proving the relative consistency of AC and GCH via the constructible universe L, presented in the NBG framework with classes primitive. It is here that Gödel gives the finite axiomatization of class theory: the class-existence theorem is reduced to a finite list of basic class-construction axioms (roughly eight Gödel operations mirroring the connectives and quantifiers) rather than an axiom schema.
**Relevance:** The historical origin and exemplar of finite axiomatization as a first-order trick — NBG's finitely many class-formation axioms exist precisely to replace ZFC's infinite comprehension/Separation schema. The "NBG yes" result the thesis rests on.

---

**★ CANON — Introduction to Mathematical Logic**
Elliott Mendelson — 1997 (4th ed.; 6th ed. 2015), Chapter 4 — Chapman & Hall / CRC — book
**Link:** https://www.routledge.com/Introduction-to-Mathematical-Logic/Mendelson/p/book/9781482237726
A standard graduate logic textbook whose Chapter 4 gives the most widely cited modern development of NBG. Mendelson presents the explicit short finite list of class-formation (class-existence) axioms — corresponding to the atomic-formula and connective/quantifier cases — and proves the class-existence metatheorem: for any formula with set-quantifiers there is a corresponding class, all built from finitely many axioms.
**Relevance:** The canonical pedagogical source establishing the precise ~8 finite class-formation axioms and the proof they suffice to replace the comprehension schema. Directly supports the "finite axiomatization = FOL schema-elimination device" thesis.

---

**★ CANON — On the Principles of Reflection in Axiomatic Set Theory**
Azriel Lévy — 1960 — *Fundamenta Mathematicae* 49(1), pp. 1–10 — article
**Link:** https://www.sciencedirect.com/science/article/pii/S0049237X09705737
Lévy formulates general principles of reflection for ZF and analyzes their deductive relationships to the standard axioms, showing how Replacement and Infinity flow from reflection schemata. One of the two 1960–61 origins (with Montague) of the modern reflection principle.
**Relevance:** Fixes part of the technical content of the Lévy–Montague reflection theorem invoked to prove ZF (and MK) is not finitely axiomatizable. Articulates schemata-from-reflection, the FOL phenomenon absent in HOL.

---

**★ CANON — Axiom Schemata of Strong Infinity in Axiomatic Set Theory**
Azriel Lévy — 1960 — *Pacific Journal of Mathematics* 10(1), pp. 223–238 — article
**Link:** https://projecteuclid.org/euclid.pjm/1103038638
**PDF:** https://msp.org/pjm/1960/10-1/pjm-v10-n1-p14-s.pdf
Lévy introduces and studies reflection principles formulated as axiom schemata of "strong infinity," showing them equivalent to (and generating) large-cardinal axioms such as inaccessible, Mahlo, and hyper-Mahlo cardinals. Over a weak base, the Reflection schema with Extensionality, Separation, and Foundation is equivalent to full ZF, locating Replacement's strength inside reflection.
**Relevance:** Lévy's half of the Lévy–Montague reflection theorem — the source result showing ZF's schemas are equivalent to a reflection schema. Reflection is the precise reason ZF cannot be finitely axiomatized in FOL.

---

**★ CANON — Fraenkel's Addition to the Axioms of Zermelo**
Richard Montague — 1961 — in *Essays on the Foundations of Mathematics* (dedicated to A. A. Fraenkel), Magnes Press / North-Holland, pp. 91–114 — chapter
**Link:** https://philpapers.org/rec/MONFAT
Montague analyzes adding Fraenkel's Replacement schema to Zermelo's set theory and, using reflection-style arguments, establishes that ZF is not finitely axiomatizable (assuming consistency): no finite subset is logically equivalent to ZF, because reflection produces, for any finite fragment, a set model — contradicting Gödel's second incompleteness theorem if ZF were finitely axiomatized.
**Relevance:** One of the two foundational proofs (with Lévy) that ZF is NOT finitely axiomatizable — the direct counterpoint to NBG. Schema-elimination fails for genuinely unbounded first-order ZF, exactly what the HOL second-order comprehension axiom sidesteps.

---

**★ CANON — Semantical Closure and Non-Finite Axiomatizability I**
Richard Montague — 1961 — in *Infinitistic Methods* (Warsaw 1959), PWN / Pergamon, pp. 45–69 — chapter
**Link:** https://philpapers.org/rec/MONSCA-7
Montague formalizes "semantical closure" of an axiomatic theory and uses it to derive general non-finite-axiomatizability results, including for ZF-style theories. The technique connects compactness, reflection, and Gödel's incompleteness to show theories whose axioms come from a genuinely unbounded schema cannot be captured by any finite axiom set.
**Relevance:** The general machinery behind "ZF is not finitely axiomatizable." Pinpoints WHY first-order schemas resist finitization, clarifying that finite axiomatizability is a contingent first-order property absent in HOL.

---

**Two Contributions to the Foundations of Set Theory**
Richard Montague — 1962 — in *Logic, Methodology and Philosophy of Science* (1960 Congress, Stanford), Stanford Univ. Press, pp. 94–110 — chapter
**Link:** https://www.sciencedirect.com/science/article/abs/pii/S0049237X09705749
Montague's two contributions develop reflection principles within ZF and apply them to relative axiomatic strength and independence. The reflection principle — any finite set of formulas true in V is reflected in some initial segment V_β — is used to show non-finite-axiomatizability and generate independence/relative-consistency results.
**Relevance:** Sharpens the reflection route to ZF's non-finite-axiomatizability, supplying the model-theoretic core argument (finite fragment ⇒ set model ⇒ contradiction with incompleteness) central to the cluster's thesis.

---

**Reflection Principles and Their Use for Establishing the Complexity of Axiomatic Systems**
Georg Kreisel and Azriel Lévy — 1968 — *Zeitschrift für math. Logik u. Grundlagen der Math.* 14, pp. 97–142 — article
**Link:** https://onlinelibrary.wiley.com/doi/10.1002/malq.19680140702
Kreisel and Lévy systematically use reflection principles to measure proof-theoretic strength and axiomatic complexity of systems such as PA and ZF, making precise the connection between reflection, unbounded schemas, and non-finite-axiomatizability.
**Relevance:** The definitive technical treatment of how reflection certifies that schematic first-order theories (ZF, PA) resist finite axiomatization. Supplies the rigorous metatheorem underpinning "ZF not finitely axiomatizable if consistent."

---

**★ CANON — Set Theory: An Introduction to Independence Proofs**
Kenneth Kunen — 1980 — Studies in Logic and the Foundations of Mathematics vol. 102, North-Holland — book
**Link:** https://en.wikipedia.org/wiki/Set_Theory:_An_Introduction_to_Independence_Proofs
**PDF:** https://fa.ewi.tudelft.nl/~hart/set_theory/Jech/Kunen-1980-Set_Theory.pdf
The canonical graduate text on the metamathematics of ZFC. Its Reflection Principle chapter gives the standard textbook proof that, granting consistency, ZF/ZFC is NOT finitely axiomatizable: any finite subtheory has a set model (by reflection), so a finite axiomatization would prove Con(ZFC), violating Gödel's second incompleteness theorem. It also develops the cumulative hierarchy and relativization machinery.
**Relevance:** Supplies the clean, citable proof of the NEGATIVE half of the research question — why ZF resists finite axiomatization in FOL — the foil that makes NBG's (and HOL's) finite axiomatization remarkable.

---

**★ CANON — A Set of Axioms for Logic**
Theodore Hailperin — 1944 — *The Journal of Symbolic Logic* 9(1), pp. 1–19 — paper
**Link:** https://www.semanticscholar.org/paper/A-set-of-axioms-for-logic-Hailperin/a964c10db88ffadcc907aaa4277297cd57182085
Hailperin proves that the stratified-comprehension SCHEMA of Quine's New Foundations (NF) is equivalent to a finite conjunction of carefully chosen instances, so NF is finitely axiomatizable (extensionality plus roughly nine comprehension instances) with no reference to the underlying type notion. The construction mirrors the von Neumann–Bernays–Gödel method of folding an infinite predicative schema into finitely many primitive class-building operations.
**Relevance:** A second, independent instance of the exact phenomenon at the heart of the project — an infinite comprehension SCHEMA collapsing to finitely many axioms. NF's stratification is itself a typed-comprehension discipline, a direct bridge between NBG finite axiomatization (§1) and the typed/HOL comprehension story (§4).

---

**★ CANON — Foundations of Set Theory (2nd revised edition)**
Abraham A. Fraenkel, Yehoshua Bar-Hillel, Azriel Lévy (with Dirk van Dalen) — 1973 — Studies in Logic vol. 67, North-Holland — book
**Link:** https://archive.org/details/foundationsofset0000frae
The standard scholarly reference on the foundations and comparative metamathematics of axiomatic set theory. It systematically surveys the axiom systems (Zermelo, ZF, NBG, Quine's NF/ML, type theory), the role of axiom schemas vs. finite axiomatizations, and the historical context; Lévy's contributions bring in the reflection-principle/non-finite-axiomatizability results.
**Relevance:** The single best one-stop secondary source mapping the whole landscape the question spans: which systems use schemas, which are finitely axiomatizable, how class theories (NBG/MK) differ, and how type theory relates.

---

**Comparison of the Axioms of Local and Universal Choice**
Ulrich Felgner — 1971 — *Fundamenta Mathematicae* 71(1), pp. 43–62 — article
**Link:** https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/ulrich-felgner-comparison-of-the-axioms-of-local-and-universal-choice-fundamenta-mathematicae-vol-71-no-1-1971-pp-4362-andrzej-mostowski-models-of-second-order-arithmetic-with-definable-skolem-functions-fundamenta-mathematicae-vol-75-no-3-1972-pp-223234/5F8A8F8366A74A5CCCAAE57563497A32
Felgner compares "local" choice (the set-level AC) with "universal"/global choice (a class function choosing from every nonempty set), within class theories such as NBG and Morse–Kelley, clarifying conservativity and non-conservativity relationships across the NBG/MK spectrum.
**Relevance:** Maps the NBG-vs-MK landscape precisely on the choice axiom, illuminating where MK's full impredicative class comprehension exceeds NBG's finite predicative class theory — the boundary between finitely-axiomatizable NBG and non-finitely-axiomatizable MK.

---

**Classless**
Sam Roberts — 2020 — *Analysis* 80(1), pp. 76–83 (OUP) — paper
**Link:** https://philpapers.org/rec/ROBASR-2
**PDF:** https://samrroberts.net/wp-content/uploads/2019/03/classes_and_conservativity_.pdf
Roberts proves a general conservativity result: provided the underlying set theory T includes a sufficiently strong reflection principle, anything a "reasonable" class theory extending T proves about sets is already provable in T. This unifies and strengthens the classical facts that NBG is conservative over ZFC while Morse–Kelley (with impredicative comprehension) is not.
**Relevance:** Sharpens the predicative-vs-impredicative comprehension distinction separating finitely-axiomatizable NBG from non-finitely-axiomatizable MK — informing what the HOL analog buys (HOL second-order comprehension is impredicative, MK-like, hence stronger than a conservative class layer).

---

**Bernays and Set Theory**
Akihiro Kanamori — 2009 — *The Bulletin of Symbolic Logic* 15(1), pp. 43–69 — article
**Link:** https://projecteuclid.org/euclid.bsl/1231081769
**PDF:** https://math.bu.edu/people/aki/17.pdf
Kanamori's historical and conceptual survey of Bernays's contributions to set theory, centered on his axiomatization with sets and classes, the development of the NBG class-existence axioms, and his later higher-order reflection principles. It traces how Bernays recast von Neumann's theory into the finitely-axiomatized class framework.
**Relevance:** Authoritative secondary source documenting the genesis of NBG's finite class-formation axioms and the move from finite first-order class theory toward higher-order reflection — bridging the FOL-finitization story to its second-order/HOL successors.

---

**Lévy and Set Theory**
Akihiro Kanamori — 2006 — *Annals of Pure and Applied Logic* 140(1–3), pp. 233–252 — article
**Link:** https://www.sciencedirect.com/science/article/pii/S0168007205001338
**PDF:** https://math.bu.edu/people/aki/11.pdf
Kanamori surveys Lévy's foundational contributions — the reflection principle, the Lévy hierarchy, Lévy absoluteness, relative constructibility, the Lévy collapse — situating them within set theory around Cohen's forcing. The treatment of reflection clarifies its role in characterizing ZF and in non-finite-axiomatizability arguments.
**Relevance:** The authoritative historical account of Lévy's reflection work — the metamathematical engine for why ZF resists finite axiomatization. Author-hosted open PDF, a convenient anchor for the reflection strand.

---

**★ CANON — Alternative Axiomatic Set Theories (Stanford Encyclopedia of Philosophy)**
M. Randall Holmes, Thomas Forster, Thierry Libert — 2021 — Stanford Encyclopedia of Philosophy — encyclopedia
**Link:** https://plato.stanford.edu/entries/settheory-alternative/
A survey of set theories beyond first-order ZFC, including the class theories NBG (von Neumann–Gödel–Bernays) and KM (Kelley–Morse). It states explicitly that NBG's Class Comprehension schema (quantifying only over sets) can be replaced by finitely many of its instances yielding finite axiomatizability, whereas KM's full impredicative Class Comprehension — bound class variables ranging over all classes — cannot be so reduced, so KM is not finitely axiomatizable and proves Con(ZFC).
**Relevance:** A citable authoritative statement of the exact dividing line at the center of the research question: NBG/GBC finitely axiomatizable (predicative class comprehension reducible to finitely many instances) versus KM not. The reference point for where the schema does vs. does not collapse.

---

**von Neumann–Bernays–Gödel set theory (nLab)**
nLab contributors — 2024 — nLab wiki — encyclopedia
**Link:** https://ncatlab.org/nlab/show/von+Neumann%E2%80%93Bernays%E2%80%93G%C3%B6del+set+theory
The nLab entry describes NBG as a conservative extension of ZFC whose ontology includes proper classes, and explains the finite axiomatization: rather than an infinite class-comprehension schema, NBG uses finitely many basic class-existence axioms because every instance can be built out of a few based on the logical connectives. It contrasts NBG with the stronger, non-finitely-axiomatizable MK.
**Relevance:** Concise modern reference framing NBG's finite axiomatization as a syntactic-induction-over-formulas device and its conservativity over ZFC — the mechanism the HOL second-order comprehension axiom replaces in one stroke.

---

**Kelley–Morse Set Theory Implies Con(ZFC) and Much More**
Joel David Hamkins — 2016 — author's research blog (jdh.hamkins.org) — exposition
**Link:** https://jdh.hamkins.org/km-implies-conzfc/
An exposition of the metamathematics of second-order set theories: GBC is finitely axiomatizable because its impredicative-free class comprehension reduces to finitely many class-existence axioms, whereas KM adds the full second-order class-comprehension schema and is strictly stronger — proving Con(ZFC) and iterated consistency. It pinpoints exactly where a class-comprehension schema can and cannot be collapsed to finitely many axioms.
**Relevance:** The direct metamathematical analog at the class level of the cluster's question: GBC's finite axiomatizability mirrors NBG's, while KM's irreducible second-order comprehension schema shows what is gained/lost by going to genuine second-order (full HOL) comprehension.

---

*Cross-references:* Zermelo's 1930 second-order recasting and its quasi-categoricity belong to **§02**; the structural finite-axiomatization analog (ETCS replacing the ZF schemas with a fixed categorical list) is in **§05**; the simple-type-theory side of why one typed comprehension suffices is in **§04**.
