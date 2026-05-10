#import "../src/macros.typ": *

= Introduction

The Continuum Hypothesis (CH) asserts that there is no cardinal strictly between the cardinality of the natural numbers and the cardinality of the continuum. Consequently, any mathematical program that treats intermediate cardinalities inside $RR$ must either work relative to $not "CH"$, change the meaning of size, or explicitly track which assumptions are external to ZFC.

The Lean development studied here chooses the first route. It introduces a named set-theoretic assumption, `ICAH.not_CH : continuum ≠ aleph 1`, and uses it to witness an intermediate cardinal. Around this assumption, the project builds a formal architecture for strata of the real continuum, size-aware field structures, subfield refinements, definability kernels, elementary chains, and direct limits.

#contribution[
  The main contribution of the current draft is not a new set-theoretic independence theorem. It is a formalization architecture: a Lean-readable decomposition of a continuum-stratification hypothesis into proved lemmas, named assumptions, and Mathlib-facing gaps.
]

The project should be positioned for a mathematical audience as a formalization paper with three layers:

+ a set-theoretic layer, where $not "CH"$ produces intermediate cardinal witnesses;
+ an algebra/model-theoretic layer, where subfields of $RR$ carry field and order structure and are intended to support real-closed-field semantics;
+ a proof-engineering layer, where every remaining dependency is exposed as a named axiom and can be attacked as an independent Mathlib contribution.

The present paper draft is organized as follows. Section 2 recalls the mathematical background. Section 3 describes the Lean architecture. Section 4 isolates the results that are already proved. Section 5 gives the axiom inventory and explains which parts are mathematical assumptions and which parts are formalization gaps. Section 6 discusses related work. Section 7 sketches analogues in valued and p-adic field theory.

== Guiding problem

#definition[
  An #emph[intermediate-cardinality stratum] is, informally, a subset $S subset.eq RR$ equipped with a cardinal $kappa$ such that
  $ aleph_0 < kappa < 2^aleph_0 $
  and a proof that the subtype determined by $S$ has cardinality $kappa$.
]

#definition[
  A #emph[size-aware field] is a bundled field-like object carrying its underlying type, a designated cardinal, and the typeclass instances needed to treat the carrier as an ordered ring or field in Lean.
]

The central formal question is:

#statement("Question", [
  Can one build, under explicit assumptions, a hierarchy of intermediate-size strata whose carriers support enough algebra and model theory to form elementary chains with a direct limit of cardinality continuum?
])

The current Lean code answers part of this question constructively and isolates the rest as a small collection of named assumptions.
