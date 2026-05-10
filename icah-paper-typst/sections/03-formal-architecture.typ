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

#construction[
  `subfieldToSAF` converts a subfield of $RR$, together with a cardinality witness, into a `SizeAwareField`. The key design choice is to use subtype inheritance for the linear order and Mathlib's subfield ordered-ring instance for the strict ordered ring structure.
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

The direct limit is the formal version of the intended limit field $F_omega$. The project currently proves a substantial cardinal theorem for this direct limit and exposes the elementarity of the direct limit as a named Mathlib gap.
