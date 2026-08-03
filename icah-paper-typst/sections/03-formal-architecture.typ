#import "../src/macros.typ": *

= Formal architecture

This section records the paper-level interpretation of the Lean objects. The goal is to make the repository legible to mathematicians without forcing them to read Lean code first.

The development is organized as two pillars sharing the cardinal scaffolding:

+ *Pillar A* (`ICAH/ElementaryStrata.lean`): strata are elementary substructures of $RR$ in the ring language, produced by downward Löwenheim–Skolem. Elementarity is definitional; the main theorem `icahElementary` needs only `NotCH`.
+ *Pillar B* (`ICAH/FieldOnStratum.lean` and downstream): strata are concrete real-closed subfields (relative algebraic closures of generated subfields). Elementarity is purchased through `RCFModelComplete`, the compatibility name for the $RR$-specialized consequence that real-closed subfield inclusions into $RR$ are elementary.

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
  `RCSubfieldStratum` refines `SubfieldStratum` once more by requiring the subfield to be *real closed*. This is the correct hypothesis for model theory: a general subfield of $RR$ (such as $QQ$) is not elementarily embedded in $RR$, while the inclusion of a real-closed subfield into $RR$ is elementary by the specialized consequence of model completeness used here.
]

#definition[
  In Pillar A, a stratum is an `LOR.ElementarySubstructure ℝ` — Mathlib's bundled elementary substructure. The theorem `exists_elementary_substratum` produces one of every infinite cardinality $kappa <= 2^(aleph_0)$ (optionally containing a prescribed set of size $<= kappa$, via `exists_elementary_substratum_extending`), by instantiating Mathlib's downward Löwenheim–Skolem theorem `exists_elementarySubstructure_card_eq` at $M = RR$. The bridge lemma `elemSubstratumSubfield` shows every such stratum is the carrier of a subfield of $RR$: closure under ring operations is the substructure property, and closure under inverses is one formula transfer ($exists y, x dot y = 1$) along elementarity. A further strengthening, not yet formalized here, is to transfer a ring-language axiomatization of real-closed fields and prove these elementary substrata real closed as well.
]

#construction[
  `subfieldToSAF` converts a subfield of $RR$, together with a cardinality witness, into a `SizeAwareField`. The key design choice is to use subtype inheritance for the linear order and Mathlib's subfield ordered-ring instance for the strict ordered ring structure.
]

#construction[
  `relAlgebraic K₀` is the relative algebraic closure of a subfield $K_0 subset.eq RR$ inside $RR$. It is proved real closed via a root-closure criterion, and its cardinality is bounded by the maximum of the cardinality of $K_0$ and $aleph_0$. This is the engine behind `exists_rc_subfield`, which produces a real-closed subfield of any prescribed infinite cardinality up to the continuum.
]

== Definability layer

The language must be stated precisely: `LOR` is a historical compatibility name for Mathlib's `Language.ring` — the first-order language with function symbols $+, dot, -, 0, 1$ and *no* relation symbols. It is not a language of ordered rings: there is no order symbol. This costs nothing for the intended models, because in a real-closed field the order is definable from the ring structure ($x <= y$ iff $y - x$ is a square), but it matters for honesty about the definability results below. A future cleanup should rename this abbreviation to `LRing`.

In the current development, the graphs of addition and multiplication on $RR$ are proved definable by constructing bounded formulas and transporting realization through Mathlib's language-homomorphism machinery (`graphDefinable_add`, `graphDefinable_mul`).

#remark[
  Since `LOR` contains the ring symbols, the graphs of $+$ and $dot$ are *atomic* formulas, and the mathematical content of these definability lemmas is nil. They are presented honestly as what they are: an API stress test of Mathlib's realization machinery — bounded formulas, `Sum`-variable bookkeeping, and the `CompatibleRing` transfer — which is exactly the plumbing later needed for the elementarity transfers in both pillars. Had the language been a pure order language, addition would *not* be definable; the precise choice of `LOR` is therefore load-bearing.
]

== Elementary chains

#definition[
  `ElemChain` packages a sequence `obj : NN -> Type*` of first-order structures and elementary embeddings `obj n ↪ₑ obj (n+1)`.
]

From these successor maps, the project defines two related systems:

+ `embLE`, which composes successor elementary embeddings and preserves elementarity;
+ `sysEmb`, which uses Mathlib's directed-system API to build the underlying embedding system.

The lemma `embLE_eq_sysEmb` proves that these two constructions agree as functions. This is a small but important bridge: the proof-relevant elementary embedding API and the directed-colimit API are not automatically the same object.

#remark[
  The chain API and its theorems are general, but the top-level existential witnesses are not increasing: `icahElementary` uses `constElemChain S`, and `icahTheorem` uses `mkConstantSC R`. Thus the assembly theorems establish the literal existence clauses in their structures without constructing a hierarchy of distinct levels.
]

== Direct limit

#definition[
  For an elementary chain `C`, the direct limit `DirectLim C` is defined as `Language.DirectLimit C.obj (...)`, using the underlying directed system of embeddings.
]

The direct limit is the formal version of the intended limit field $F_omega$. The project proves the cardinality identity $\#F_omega = sup_n \#C_n$ (`directLimit_card_eq_iSup`), the closure theorem that countable chains of intermediate strata stay intermediate (`directLimit_card_lt_continuum`, via König), and two elementarity theorems: the relativized version over $RR$ (`tarskiVaughtDirectLimit`, via the Tarski--Vaught test) and the ambient-free version (`ofLevelElem`: the canonical maps into the direct limit are elementary, by induction on bounded formulas). Both elementarity statements were previously exposed as gaps and are now theorems.

== Cofinal family at the continuum, and optimality

The $NN$-indexed chain cannot, by itself, exhaust $RR$: König's theorem gives $"cof"(c) > aleph_0$, so a countable increasing union of sets of size $< c$ has size $< c$. The module `ICAH/CofinalFamily.lean` therefore introduces a `𝔠.ord`-indexed monotone family of intermediate-size real-closed subfields whose union is all of $RR$ (`exists_cofinal_rc_family`). The top-level statement `ICAHStatement` uses this family for its limit-size clause, which keeps the formalized claim non-vacuous.

The module also proves a qualified exact threshold: any family of subsets of $RR$, each of size $< c$, covering $RR$ has at least $"cof"(c)$ members (`cofinal_family_length_lower_bound`), and a monotone covering family of intermediate-size real-closed subfields of length exactly $"cof"(c)$ exists (`exists_cofinal_rc_family_cof_length`, by composing the `𝔠.ord`-indexed family with a fundamental sequence). These subfields are real closed, but their inclusions are not proved elementary. See Section 4.
