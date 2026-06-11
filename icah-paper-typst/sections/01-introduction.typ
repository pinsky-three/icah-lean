#import "../src/macros.typ": *

= Introduction

The Continuum Hypothesis (CH) asserts that there is no cardinal strictly between the cardinality of the natural numbers and the cardinality of the continuum. Consequently, any mathematical program that treats intermediate cardinalities inside $RR$ must either work relative to $not "CH"$, change the meaning of size, or explicitly track which assumptions are external to ZFC.

The Lean development studied here chooses the first route. It introduces a named proposition, `ICAH.NotCH : Prop`, defined as `continuum ≠ aleph 1`, and threads it through the development as an explicit hypothesis. Around this hypothesis, the project builds a formal architecture for strata of the real continuum, size-aware field structures, subfield refinements, elementary substructures, elementary chains, and direct limits.

== What "ICAH" denotes

The name requires precision. Despite the word "Hypothesis", ICAH is *not* an axiom candidate in the sense of Martin's Axiom or PFA: it is not a new assumption whose consistency strength is at issue. ICAH denotes a *theorem schema under $not "CH"$* — a conjunction of structural claims about intermediate-cardinality strata of $RR$, each provable (in ZFC, formalized in Lean/Mathlib) once $not "CH"$ is granted. The formal content is the pair of Lean propositions `ICAHElementary` and `ICAHStatement` displayed below, together with their proofs.

== Main theorem

The development is organized as two pillars that realize the same informal picture at different levels of concreteness.

#theorem[
  *(Theorem 1 — Pillar A, semantic form; Lean: `icahElementary`.)*
  Assume $not "CH"$ (i.e. `NotCH`). Then, writing $cal(L)$ for the first-order ring language and "stratum" for an elementary substructure $S prec RR$ in $cal(L)$:

  + *(band)* there exists a cardinal $kappa$ with $aleph_0 < kappa < 2^(aleph_0)$;
  + *(strata at every level)* for every cardinal $kappa$ with $aleph_0 < kappa < 2^(aleph_0)$ there is an elementary substructure $S prec RR$ with $\#S = kappa$ (this clause is ZFC-pure: downward Löwenheim–Skolem);
  + *(chains)* there is an $NN$-indexed elementary chain of intermediate-size strata whose direct limit is elementarily equivalent to $RR$;
  + *(closure; ZFC-pure)* for every $NN$-indexed elementary chain whose levels have size $< 2^(aleph_0)$, the direct limit has size $< 2^(aleph_0)$ — countable chains never escape the hierarchy;
  + *(cofinality)* every real number lies in some intermediate-size elementary substructure of $RR$.

  The Lean proof depends only on the kernel axioms `propext`, `Classical.choice`, `Quot.sound`; this is machine-checked by `#guard_msgs` in the build.
]

#theorem[
  *(Theorem 2 — Pillar B, algebraic realization; Lean: `icahTheorem`.)*
  Assume $not "CH"$ and additionally `RCFModelComplete` (compatibility name for the $RR$-specialized consequence that every real-closed subfield of $RR$ is an elementary substructure in the ring language; it follows from model completeness of RCF, the single remaining Mathlib gap). Then the four clauses of `ICAHStatement` hold:

  + *(M1)* for every ordinal $n$ there is a stratum $R$ with index $n$ and $aleph_0 < \#R < 2^(aleph_0)$;
  + *(M3)* every stratum carries a size-aware ordered-field structure with matching carrier and cardinal;
  + *(M5)* there is a chain of strata — concretely, real-closed subfields of $RR$ given as relative algebraic closures — whose direct limit is elementarily equivalent to $RR$;
  + *(M6)* there is a `𝔠.ord`-indexed monotone family of intermediate-size subfields of $RR$ whose union is all of $RR$ and hence has cardinality $2^(aleph_0)$.
]

The duality between the pillars is a genuine trade-off, made explicit throughout the paper: Pillar A gets elementarity for free (the strata are Skolem hulls, already known in Lean to be subfields and expected to be real closed after an RCF-axiomatization transfer), while Pillar B has concrete, named strata (relative algebraic closures, with native `IsRealClosed` instances) but must purchase elementarity through Tarski–Seidenberg.

#contribution[
  The main contribution is not new mathematics — to a model theorist, the existence of real-closed subfields of every intermediate cardinality is a corollary of downward Löwenheim–Skolem plus Tarski, and the chain results are textbook Tarski–Vaught. The contribution is the formalization architecture and the assumption cartography: a Lean-readable decomposition of a continuum-stratification statement into proved lemmas, explicitly threaded hypotheses, and Mathlib-facing gaps, with the dependency set of every flagship theorem machine-audited in the build. The development declares *zero* axioms; the main theorem (Pillar A) holds under $not "CH"$ alone.
]

The project should be positioned for a mathematical audience as a formalization paper with three layers:

+ a set-theoretic layer, where the hypothesis $not "CH"$ produces intermediate cardinal witnesses;
+ a model-theoretic/algebraic layer, where elementary substrata of every intermediate cardinality are produced by downward Löwenheim–Skolem (Pillar A), and real-closed subfields of every infinite cardinality up to the continuum are constructed and assembled into elementary chains (Pillar B);
+ a proof-engineering layer, where the one remaining Mathlib dependency is exposed as a named hypothesis, machine-audited in the build, and can be attacked as an independent Mathlib contribution.

The present paper draft is organized as follows. Section 2 recalls the mathematical background. Section 3 describes the Lean architecture. Section 4 isolates the results that are already proved. Section 5 gives the hypothesis inventory, the per-theorem audit, and the Mathlib roadmap. Section 6 discusses related work, including the formalizations of the independence of CH and the certified quantifier-elimination procedures for real-closed fields in other proof assistants. Section 7 briefly notes analogues in valued and p-adic field theory. Section 8 concludes with reproducibility data and an engagement plan.

== Guiding problem

#definition[
  An #emph[intermediate-cardinality stratum] is, informally, a subset $S subset.eq RR$ equipped with a cardinal $kappa$ such that
  $ aleph_0 < kappa < 2^(aleph_0) $
  and a proof that the subtype determined by $S$ has cardinality $kappa$.
]

#definition[
  A #emph[size-aware field] is a bundled field-like object carrying its underlying type, a designated cardinal, and the typeclass instances needed to treat the carrier as an ordered ring or field in Lean.
]

The central formal question is:

#statement("Question", [
  Can one build, under explicit assumptions, a hierarchy of intermediate-size strata whose carriers support enough algebra and model theory to form elementary chains, and how long must a family of such strata be to exhaust $RR$?
])

The current Lean code answers this question completely. Semantically (Pillar A), every clause is proved under $not "CH"$ alone. Algebraically (Pillar B), every clause is proved once the model completeness of real-closed fields is granted. And the exhaustion question has a sharp answer: the least length of a family of intermediate strata covering $RR$ is exactly $"cof"(2^(aleph_0))$.
