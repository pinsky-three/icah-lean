#import "../src/macros.typ": *

= Introduction

The Continuum Hypothesis (CH) asserts that there is no cardinal strictly between the cardinality of the natural numbers and the cardinality of the continuum. Consequently, any mathematical program that treats intermediate cardinalities inside $RR$ must either work relative to $not "CH"$, change the meaning of size, or explicitly track which assumptions are external to ZFC.

The Lean development studied here chooses the first route. It introduces a named proposition, `ICAH.NotCH : Prop`, defined as `continuum ≠ aleph 1`, and threads it through the development as an explicit hypothesis. Around this hypothesis, the project builds a formal architecture for elementary substrata of the real continuum, size-aware field structures, named real-closed subfields, elementary chains, and cofinal covering families.

The project name "ICAH" is retained as a repository identifier. The mathematics is standard: downward Löwenheim–Skolem plus Tarski for existence, Tarski–Vaught for chains and directed unions. The contribution is the formalization and the assumption cartography, not a new set-theoretic hypothesis.

== Main theorem

The development is organized as two pillars that realize the same informal picture at different levels of concreteness.

#theorem[
  *(Theorem 1 — Pillar A, semantic form; Lean: `icahElementary`.)*
  Assume $not "CH"$ (i.e. `NotCH`). Then, writing #LRing for the first-order ring language and "stratum" for an elementary substructure $S prec RR$ in #LRing:

  + *(band)* there exists a cardinal $kappa$ with $aleph_0 < kappa < 2^(aleph_0)$;
  + *(strata at every level)* for every cardinal $kappa$ with $aleph_0 < kappa < 2^(aleph_0)$ there is an elementary substructure $S prec RR$ with $\#S = kappa$ (this clause is ZFC-pure: downward Löwenheim–Skolem);
  + *(strict chains)* there is a *strictly increasing* $NN$-indexed elementary chain of intermediate-size strata whose direct limit is elementarily equivalent to $RR$;
  + *(closure; ZFC-pure)* for every $NN$-indexed elementary chain whose levels have size $< 2^(aleph_0)$, the direct limit has size $< 2^(aleph_0)$ — countable chains never escape the hierarchy;
  + *(cofinality)* every real number lies in some intermediate-size elementary substructure of $RR$.

  Separately, and still from $not "CH"$ alone, there is a monotone `𝔠.ord`-indexed family of intermediate-size elementary substrata covering $RR$, compressible to length $"cof"(2^(aleph_0))$ (`exists_cofinal_elem_family`, `exists_cofinal_elem_family_cof_length`). Every inclusion is elementary by the nesting lemma.

  The Lean proof depends only on the kernel axioms `propext`, `Classical.choice`, `Quot.sound`; this is machine-checked by `#guard_msgs` in the build.
]

#theorem[
  *(Theorem 2 — Pillar B, algebraic realization; Lean: `icahTheorem`.)*
  Assume $not "CH"$ and additionally `RCFModelComplete` (compatibility name for the $RR$-specialized consequence that the inclusion of every real-closed subfield of $RR$ into $RR$ is elementary in the ring language; it follows from model completeness of RCF, a Mathlib gap). Then the clauses of `ICAHStatement` hold:

  + *(M1)* for every ordinal $n$ there is a stratum $R$ with index $n$ and $aleph_0 < \#R < 2^(aleph_0)$;
  + *(M3)* every stratum carries a size-aware ordered-field structure with matching carrier and cardinal;
  + *(M5)* there is a *strictly increasing* chain of strata whose direct limit is elementarily equivalent to $RR$ (the witness is the Pillar A chain; this clause does not use the RCF hypothesis);
  + *(M6)* there is a nonconstant `𝔠.ord`-indexed monotone family of intermediate-size real-closed subfields of $RR$ whose union is all of $RR$;
  + *(elementary RC family)* under the RCF hypothesis, that same family has elementary inclusions (`exists_cofinal_rc_family_elementary`).
]

Pillar A is unconditional on model completeness: its strata are elementary by construction, model $op("Th")(RR)$ (hence the first-order theory of real-closed fields), and assemble into the nonconstant elementary hierarchy the informal picture asks for. Pillar B is the *conditional* pillar in both senses: it supplies named, algebraically explicit real-closed subfields (relative algebraic closures, with native `IsRealClosed` instances), and it purchases elementarity of those algebraic inclusions through the remaining Mathlib gap. Once a ring-language RCF axiomatization is transferred to a native `IsRealClosed` instance, Pillar A already supplies concrete-enough real-closed elementary strata without `RCFModelComplete`.

#remark[
  Three constructions must not be conflated. First, `tarskiVaughtDirectLimit` and `ofLevelElem` are general theorems about arbitrary $NN$-indexed elementary chains. Second, the existential chain clauses of `icahElementary` and `icahTheorem` are discharged by the *strictly increasing* chain `strictElemChain`, built by iterating downward Löwenheim–Skolem from an $aleph_1$-sized substratum and adjoining a fresh real at each step; successor maps are the nesting inclusions. Third, `exists_cofinal_elem_family` is a genuinely nonconstant monotone covering family of elementary substrata of length at most $c$, compressible to $"cof"(c)$. The older constant-chain objects remain in the library as test cases; they are not the witnesses of the top-level theorems.
]

#contribution[
  The main contribution is not new mathematics — to a model theorist, the existence of elementary (hence first-order real-closed) substrata of every intermediate cardinality is a corollary of downward Löwenheim–Skolem, and the chain and union results are textbook Tarski–Vaught. The contribution is the formalization architecture and the assumption cartography: a Lean-readable decomposition into proved lemmas, explicitly threaded hypotheses, and Mathlib-facing gaps, with the dependency set of every flagship theorem machine-audited in the build. The development declares *zero* axioms; the semantic theorem (Pillar A) holds under $not "CH"$ alone.
]

The project should be positioned for a mathematical audience as a formalization paper with three layers:

+ a set-theoretic layer, where the hypothesis $not "CH"$ produces intermediate cardinal witnesses;
+ a model-theoretic/algebraic layer, where elementary substrata of every intermediate cardinality are produced by downward Löwenheim–Skolem (Pillar A), general elementary-chain theorems are proved, a cofinal elementary family of optimal length is constructed, and named real-closed subfields of every infinite cardinality up to the continuum are constructed (Pillar B);
+ a proof-engineering layer, where the remaining Mathlib-facing dependency of Pillar B is exposed as a named hypothesis, machine-audited in the build, and can be attacked as an independent Mathlib contribution.

The paper is organized as follows. Section 2 recalls the mathematical background. Section 3 describes the Lean architecture. Section 4 isolates the results that are already proved. Section 5 gives the hypothesis inventory, the per-theorem audit, and the Mathlib roadmap. Section 6 discusses related work, including the formalizations of the independence of CH and the certified quantifier-elimination procedures for real-closed fields in other proof assistants. Section 7 briefly notes analogues in valued and p-adic field theory. Section 8 concludes with reproducibility data and an engagement plan.

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
  Which components of an intermediate-cardinality stratification can be formalized under explicit assumptions, what general elementary-chain theorems are available, and how long must a family of intermediate-size elementary substrata or real-closed subfields be to exhaust $RR$?
])

The current Lean code gives complete proofs of the stated `ICAHElementary` clauses under $not "CH"$ and of the stated `ICAHStatement` clauses under its two explicit hypotheses. The chain witnesses are strictly increasing; the cofinal elementary family of length $"cof"(2^(aleph_0))$ is proved. For arbitrary covering families of subsets of $RR$ whose members have size below the continuum, the lower bound is $"cof"(2^(aleph_0))$; under $not "CH"$, this bound is attained both by elementary substrata and by named real-closed subfields.
