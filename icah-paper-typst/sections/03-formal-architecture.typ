#import "../src/macros.typ": *

= Formal architecture

This section records the paper-level interpretation of the Lean objects. The goal is to make the repository legible to mathematicians without forcing them to read Lean code first.

The development is organized as two pillars sharing the cardinal scaffolding:

+ *Pillar A* (`ICAH/ElementaryStrata.lean`): strata are elementary substructures of $RR$ in the ring language, produced by downward Löwenheim–Skolem. Elementarity is definitional; the main theorem `icahElementary` needs only `NotCH`. Nested elementary substructures of $RR$ form an elementary pair, so the strata assemble into a strictly increasing $NN$-chain and a cofinal elementary family.
+ *Pillar B* (`ICAH/FieldOnStratum.lean` and downstream): strata are concrete real-closed subfields (relative algebraic closures of generated subfields), with native `IsRealClosed` instances. Elementarity of those *named algebraic* inclusions is purchased through `RCFModelComplete`. Pillar B is the conditional pillar.

== Core objects

#definition[
  `Stratum` is the basic continuum-layer object. It consists of an ordinal index, a set $S subset.eq RR$, a cardinal $kappa$, a witness that the subtype determined by $S$ has cardinality $kappa$, and bounds $aleph_0 < kappa < c$.
]

#definition[
  `SizeAwareField` is a bundled structure containing a carrier type, a designated cardinal, and the instances `[Field K]`, `[LinearOrder K]`, and `[IsStrictOrderedRing K]`. This avoids relying on deprecated or overly strong ordered-field classes while still exposing enough structure for model-theoretic use.
]

#definition[
  `SubfieldStratum` refines `Stratum` by adding a subfield `subfield : Subfield RR` and a proof that the stratum set is exactly the underlying set of that subfield.
]

The role of `SubfieldStratum` is central. A raw set of real numbers is not automatically closed under addition, multiplication, negation, and inverses. A subfield is. Thus, the field part of the theory is moved from a fragile closure proof obligation into a stable algebraic structure.

#definition[
  `RCSubfieldStratum` refines `SubfieldStratum` once more by requiring the subfield to be *real closed*. This is the correct hypothesis for the algebraic pillar: a general subfield of $RR$ (such as $QQ$) is not elementarily embedded in $RR$, while the inclusion of a real-closed subfield into $RR$ is elementary by the specialized consequence of model completeness used here.
]

#definition[
  In Pillar A, a stratum is an `LRing.ElementarySubstructure ℝ` — Mathlib's bundled elementary substructure. The theorem `exists_elementary_substratum` produces one of every infinite cardinality $kappa <= 2^(aleph_0)$ (optionally containing a prescribed set of size $<= kappa$, via `exists_elementary_substratum_extending`), by instantiating Mathlib's downward Löwenheim–Skolem theorem `exists_elementarySubstructure_card_eq` at $M = RR$. The bridge lemma `elemSubstratumSubfield` shows every such stratum is the carrier of a subfield of $RR$: closure under ring operations is the substructure property, and closure under inverses is one formula transfer ($exists y, x dot y = 1$) along elementarity. First-order real-closedness is immediate: an elementary substratum models $op("Th")(RR)$ (`elemSubstratum_models_thReal`), and $op("Th")(RR)$ contains the ring-language axiomatization of RCF. Native `IsRealClosed` instance transfer along this observation is not formalized.
]

#construction[
  `subfieldToSAF` converts a subfield of $RR$, together with a cardinality witness, into a `SizeAwareField`. The key design choice is to use subtype inheritance for the linear order and Mathlib's subfield ordered-ring instance for the strict ordered ring structure.
]

#construction[
  `relAlgebraic K₀` is the relative algebraic closure of a subfield $K_0 subset.eq RR$ inside $RR$. It is proved real closed via a root-closure criterion, and its cardinality is bounded by the maximum of the cardinality of $K_0$ and $aleph_0$. This is the engine behind `exists_rc_subfield`, which produces a real-closed subfield of any prescribed infinite cardinality up to the continuum.
]

== Language

The language is Mathlib's `Language.ring`, abbreviated `LRing` (historical compatibility name `LOR`): function symbols $+, dot, -, 0, 1$ and *no* relation symbols. It is not a language of ordered rings. This costs nothing for the intended models, because in a real-closed field the order is definable from the ring structure ($x <= y$ iff $y - x$ is a square). The graphs of addition and multiplication are therefore atomic formulas; the corresponding definability lemmas are API stress tests of Mathlib's realization machinery, not mathematical content, and are not given a separate subsection.

== Elementary chains

#definition[
  `ElemChain` packages a sequence `obj : NN -> Type*` of first-order structures and elementary embeddings `obj n ↪ₑ obj (n+1)`.
]

From these successor maps, the project defines two related systems:

+ `embLE`, which composes successor elementary embeddings and preserves elementarity;
+ `sysEmb`, which uses Mathlib's directed-system API to build the underlying embedding system.

The lemma `embLE_eq_sysEmb` proves that these two constructions agree as functions. This is a small but important bridge: the proof-relevant elementary embedding API and the directed-colimit API are not automatically the same object.

#lemma[
  `elementaryInclusion`: if $S subset.eq T$ are both elementary substructures of a common model $M$, then the inclusion $S -> T$ is elementary. Satisfaction in $S$ and in $T$ both reduce to satisfaction in $M$.
]

#construction[
  `strictElemChain`: under `NotCH`, start from an $aleph_1$-sized elementary substratum of $RR$ (DLS); at each stage pick a real outside the current carrier (possible because the carrier has size $< c$) and apply `exists_elementary_substratum_extending` to the previous carrier plus that real. Successor maps are the nesting inclusions. The result is a strictly increasing $NN$-indexed elementary chain of intermediate-size strata; `ofLevelElem` and `directLimit_card_lt_continuum` handle the limit.
]

== Direct limit

#definition[
  For an elementary chain `C`, the direct limit `DirectLim C` is defined as `Language.DirectLimit C.obj (...)`, using the underlying directed system of embeddings.
]

The direct limit is the formal version of the intended limit field $F_omega$. The project proves the cardinality identity $\#F_omega = sup_n \#C_n$ (`directLimit_card_eq_iSup`), the closure theorem that countable chains of intermediate strata stay intermediate (`directLimit_card_lt_continuum`, via König), and two elementarity theorems: the relativized version over $RR$ (`tarskiVaughtDirectLimit`, via the Tarski--Vaught test) and the ambient-free version (`ofLevelElem`: the canonical maps into the direct limit are elementary, by induction on bounded formulas). Both elementarity statements were previously exposed as gaps and are now theorems.

== Cofinal families at the continuum, and optimality

The $NN$-indexed chain cannot, by itself, exhaust $RR$: König's theorem gives $"cof"(c) > aleph_0$, so a countable increasing union of sets of size $< c$ has size $< c$. The module `ICAH/CofinalFamily.lean` therefore constructs two `𝔠.ord`-indexed monotone covering families, both compressible to length $"cof"(c)$:

+ `exists_cofinal_elem_family`: elementary substrata, seeded at each ordinal by the previous stage plus the next real under an enumeration of $RR$. Inclusions are elementary by nesting; limit stages are elementary by the directed-union lemma. This family needs only `NotCH`.
+ `exists_cofinal_rc_family`: named real-closed subfields (relative algebraic closures). Under `RCFModelComplete`, its inclusions are elementary (`exists_cofinal_rc_family_elementary`).

The module also proves a qualified exact threshold: any family of subsets of $RR$, each of size $< c$, covering $RR$ has at least $"cof"(c)$ members (`cofinal_family_length_lower_bound`). See Section 4.
