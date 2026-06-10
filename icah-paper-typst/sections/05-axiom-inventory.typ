#import "../src/macros.typ": *

#pagebreak(weak: true)
= Axiom inventory and Mathlib roadmap

A central strength of the Lean development is that it does not hide its assumptions. The theorem `icahTheorem` is assembled from proved components plus a small set of named dependencies. After the June 2026 axiom-reduction effort, the inventory contains exactly **two** project axioms, enforced in-source by a `#guard_msgs in #print axioms icahTheorem` check and audited in CI:

```
'ICAH.icahTheorem' depends on axioms:
  [propext, Classical.choice, not_CH, rcfModelComplete, Quot.sound]
```

== External mathematical assumption

#gap[
  `ICAH.not_CH`: the negation of the Continuum Hypothesis, represented as `continuum ≠ aleph 1`.
]

This is not a Mathlib gap. It is the intended set-theoretic regime of the project. The paper should say explicitly that the theory is developed relative to $not "CH"$.

== The single remaining Mathlib gap

#gap[
  `ICAH.rcfModelComplete`: model completeness of the theory of real-closed ordered fields (Tarski--Seidenberg). Concretely: the inclusion of a real-closed subfield of $RR$ into $RR$ is an elementary embedding in the language of ordered rings.
]

This is a true classical theorem whose first-order formalization (quantifier elimination or model completeness for RCF inside Mathlib's `ModelTheory` framework) is absent from Mathlib. It is the natural next contribution target, and discharging it would reduce the project to the single definitional axiom `not_CH`.

== Resolved former axioms

The five remaining entries of the previous inventory were all discharged:

#theorem[
  `ICAH.Real.isRealClosed` --- *proved* (`ICAH/RealClosed.lean`): $RR$ is real closed, via `IsRealClosed.of_linearOrderedField`, `Real.sqrt` for squares, and the intermediate value theorem for odd-degree polynomials.
]

#theorem[
  `ICAH.fieldOnStratum` --- *proved* (`ICAH/FieldOnStratum.lean`): every stratum admits a size-aware field, by `Equiv`-transport of the field structure of a real-closed subfield of matching cardinality.
]

#theorem[
  `ICAH.subfieldStratumExists` --- *proved and strengthened* (`exists_rc_subfield`): for every $aleph_0 <= kappa <= c$ there is a *real-closed* subfield of $RR$ of cardinality exactly $kappa$, obtained as the relative algebraic closure of a generated subfield.
]

#theorem[
  `ICAH.ElemChain.losDirectLimit` --- *proved* (`ICAH/ElementaryChain.lean`): the direct limit of an elementary chain compatibly embedded in $RR$ is elementarily equivalent to $RR$, via `Language.DirectLimit.lift` and the Tarski--Vaught test.
]

#remark[
  Two further axioms of the earlier draft, `subfieldIsRealClosed` and `subfieldStratumElemEmb`, were *deleted as false in the stated generality*: $QQ$ is a subfield of $RR$ that is neither real closed nor elementarily embedded. They are replaced by the sound refinement `RCSubfieldStratum` (a stratum whose carrier is a real-closed subfield), for which elementarity follows from `rcfModelComplete`.
]

== The honest limit construction

The original $NN$-indexed chain formulation of the limit-size milestone is vacuous under $not "CH"$: König's theorem gives $"cof"(c) > aleph_0$, so no countable chain of intermediate-size strata can union to $RR$. The corrected statement (`ICAH/CofinalFamily.lean`) indexes the family by the ordinal `𝔠.ord`:

#theorem[
  `exists_cofinal_rc_family`: there is a monotone family of real-closed subfields of $RR$, indexed by `𝔠.ord`, each of intermediate cardinality, whose union is all of $RR$; and `cofinal_family_limit_size`: the union has cardinality $c$.
]

== Recommended order of attack

+ Extract `IsRealClosed RR` and the root-closure criterion `isRealClosed_of_forall_root` as Mathlib PRs.
+ Extract the elementary-direct-limit theorem (`losDirectLimit`) for `Language.DirectLimit` as a Mathlib PR.
+ Formalize quantifier elimination / model completeness for RCF in Mathlib's `ModelTheory` framework, discharging `rcfModelComplete` --- the final gap.
