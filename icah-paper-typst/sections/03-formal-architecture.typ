#import "../src/macros.typ": *

= Formal architecture

This section records the paper-level interpretation of the Lean objects. The goal is to make the repository legible to mathematicians without forcing them to read Lean code first.

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
  `RCSubfieldStratum` refines `SubfieldStratum` once more by requiring the subfield to be *real closed*. This is the correct hypothesis for model theory: a general subfield of $RR$ (such as $QQ$) is not elementarily embedded in $RR$, while a real-closed subfield is, by model completeness of the theory of real-closed fields.
]

#construction[
  `subfieldToSAF` converts a subfield of $RR$, together with a cardinality witness, into a `SizeAwareField`. The key design choice is to use subtype inheritance for the linear order and Mathlib's subfield ordered-ring instance for the strict ordered ring structure.
]

#construction[
  `relAlgebraic K₀` is the relative algebraic closure of a subfield $K_0 subset.eq RR$ inside $RR$. It is proved real closed via a root-closure criterion, and its cardinality is bounded by the maximum of the cardinality of $K_0$ and $aleph_0$. This is the engine behind `exists_rc_subfield`, which produces a real-closed subfield of any prescribed infinite cardinality up to the continuum.
]

== Definability layer

The formalization uses an abbreviation `LOR` for the first-order language used in the definability kernel. In the current development, the graphs of addition and multiplication on $RR$ are proved definable by constructing bounded formulas and transporting realization through Mathlib's language-homomorphism machinery.

#remark[
  The definability results are important because they demonstrate that the paper is not only doing cardinal bookkeeping. It also touches the first-order model-theoretic infrastructure needed to express arithmetic inside a layer.
]

== Elementary chains

#definition[
  `ElemChain` packages a sequence `obj : NN -> Type*` of first-order structures and elementary embeddings `obj n ↪ₑ obj (n+1)`.
]

From these successor maps, the project defines two related systems:

+ `embLE`, which composes successor elementary embeddings and preserves elementarity;
+ `sysEmb`, which uses Mathlib's directed-system API to build the underlying embedding system.

The lemma `embLE_eq_sysEmb` proves that these two constructions agree as functions. This is a small but important bridge: the proof-relevant elementary embedding API and the directed-colimit API are not automatically the same object.

== Direct limit

#definition[
  For an elementary chain `C`, the direct limit `DirectLim C` is defined as `Language.DirectLimit C.obj (...)`, using the underlying directed system of embeddings.
]

The direct limit is the formal version of the intended limit field $F_omega$. The project proves both a substantial cardinal theorem for this direct limit (`directLimit_card`) and its elementarity over $RR$ (`losDirectLimit`, via the Tarski--Vaught test); both were previously exposed as gaps and are now theorems.

== Cofinal family at the continuum

The $NN$-indexed chain cannot, by itself, exhaust $RR$: König's theorem gives $"cof"(c) > aleph_0$, so a countable increasing union of sets of size $< c$ has size $< c$. The module `ICAH/CofinalFamily.lean` therefore introduces a `𝔠.ord`-indexed monotone family of intermediate-size real-closed subfields whose union is all of $RR$ (`exists_cofinal_rc_family`). The top-level statement `ICAHStatement` uses this family for its limit-size clause, which keeps the formalized claim non-vacuous.
