#import "../src/macros.typ": *

#pagebreak(weak: true)
= Hypothesis inventory, per-theorem audit, and Mathlib roadmap

A central strength of the Lean development is that it does not hide its assumptions. After the June 2026 refactor, the project declares *zero* axioms: the two named assumptions are ordinary `Prop`s threaded through the development as explicit hypotheses, so the assumption set of every theorem is visible in its type signature. The kernel-level audit is enforced in-source by `#guard_msgs in #print axioms` blocks and checked in CI:

```
'ICAH.icahElementary' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ICAH.icahTheorem' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Any drift in these sets — including a hidden `sorryAx` — fails the build. With hypotheses in signatures rather than axioms in the environment, `#guard_msgs` is demoted from safety mechanism to regression test, which is the right division of labor.

== External mathematical hypothesis

#assumption[
  `ICAH.NotCH : Prop`, defined as `continuum ≠ aleph 1`: the negation of the Continuum Hypothesis.
]

This is not a Mathlib gap. It is the intended set-theoretic regime of the project: the theory is developed relative to $not "CH"$, which is consistent with ZFC by Cohen's forcing argument @cohen1966 — itself formalized in Lean by the Flypitch project @flypitch_itp (see Section 6).

== The single remaining Mathlib gap

#gap[
  `ICAH.RCFSubfieldRealElementary : Prop` (compatibility spelling `ICAH.RCFModelComplete`): the inclusion of a real-closed subfield of $RR$ into $RR$ is an elementary embedding in the ring language (in which the order of a real-closed field is definable via squares). This is the $RR$-specialized consequence of model completeness of the theory of real-closed fields needed by Pillar B.
]

This is a true classical theorem whose first-order formalization follows from quantifier elimination or model completeness for RCF inside Mathlib's `ModelTheory` framework, neither of which is currently available in the needed form. It is consumed only by Pillar B (`icahTheorem`); Pillar A (`icahElementary`) avoids it entirely via downward Löwenheim–Skolem.

#remark[
  *Why this gap is harder than the ACF precedent.* Mathlib already contains the deep-embedded model theory of algebraically closed fields: the theory `ACF p` over the ring language, its completeness for $p$ prime or zero (`ACF_isComplete`), and the Lefschetz principle. That suggests a template — but completeness of ACF comes cheap via uncountable categoricity and the Łoś–Vaught test, a route that is *closed* for RCF: the theory of real-closed fields is unstable (it defines a linear order) and has the maximum number of models in every uncountable cardinality. Discharging `RCFSubfieldRealElementary` therefore requires QE-grade work — e.g. Robinson's model-completeness test with sign-change/root-counting embedding arguments inside the deep embedding — substantially more than porting the ACF files.

  Prior art calibrates the effort: the `math-comp/real-closed` library in Coq/Rocq contains a certified quantifier-elimination procedure for RCF with the decision procedure `rcf_sat` and its correctness proof (Cohen–Mahboubi @cohen_mahboubi_lmcs), and HOL Light has McLaughlin–Harrison's proof-producing decision procedure for RCF @mclaughlin_harrison_cade. Neither transfers directly to Mathlib's `FirstOrder` framework, but Cohen–Mahboubi is the closest blueprint. (This also discharges the earlier draft's TODO asking for a situated estimate of the gap.)
]

== Per-theorem audit

Because the hypotheses are explicit, the audit can be given per theorem. The classification below is the contractual content of the development:

+ *ZFC-pure* (kernel axioms only, no project hypotheses): `exists_elementary_substratum`, `exists_elementary_substratum_extending`, `elemSubstratumSubfield`, `exists_rc_subfield`, `relAlgebraic_isRealClosed`, `isRealClosed_of_forall_root`, `Real.isRealClosed`, `tarskiVaughtDirectLimit`, `ofLevelElem` (the ambient-free chain theorem), `directLimit_card_eq_iSup`, `directLimit_card_lt_continuum`, `directLimit_intermediate`, `cofinal_family_length_lower_bound`, `fieldOnStratum`, `fieldOnSubfieldStratum`, `algReal_card_le_aleph0`.
+ *Under `NotCH`*: `exists_intermediate_cardinal`, `syntheticStratum`, `subfieldStratumExists`, `intermediateRCSubfieldStratum`, `exists_cofinal_rc_family`, `exists_cofinal_rc_family_cof_length`, `cofinal_family_limit_size`, and the Pillar A main theorem `icahElementary`.
+ *Under `NotCH` and `RCFModelComplete`*: the Pillar B main theorem `icahTheorem` (the specialized real-closed-subfield elementarity hypothesis enters only through the elementary-chain clause M5).

The ZFC-pure results need neither hypothesis — that property is precisely their upstream selling point.

== Resolved former axioms

The earlier inventory was discharged in two stages. First, five axioms became theorems:

#theorem[
  `ICAH.Real.isRealClosed` --- *proved* (`ICAH/RealClosed.lean`): $RR$ is real closed, via `IsRealClosed.of_linearOrderedField`, `Real.sqrt` for squares, and the intermediate value theorem for odd-degree polynomials.
]

#theorem[
  `ICAH.fieldOnStratum` --- *proved* (`ICAH/FieldOnStratum.lean`): every stratum admits a size-aware field, by `Equiv`-transport of the field structure of a real-closed subfield of matching cardinality (a packaging lemma; see Section 4).
]

#theorem[
  `ICAH.subfieldStratumExists` --- *proved and strengthened* (`exists_rc_subfield`): for every $aleph_0 <= kappa <= c$ there is a *real-closed* subfield of $RR$ of cardinality exactly $kappa$, obtained as the relative algebraic closure of a generated subfield.
]

#theorem[
  `ICAH.ElemChain.losDirectLimit` --- *proved and renamed* (`tarskiVaughtDirectLimit`, `ICAH/ElementaryChain.lean`): the direct limit of an elementary chain compatibly embedded in $RR$ is elementarily equivalent to $RR$, via `Language.DirectLimit.lift` and the Tarski--Vaught test.
]

Second, the two remaining axioms (`not_CH`, `rcfModelComplete`) were converted from axioms into the explicit hypotheses `NotCH` and `RCFSubfieldRealElementary` (with compatibility spelling `RCFModelComplete`), emptying the axiom inventory entirely.

#remark[
  Two further axioms of the earlier draft, `subfieldIsRealClosed` and `subfieldStratumElemEmb`, were *deleted as false in the stated generality*: $QQ$ is a subfield of $RR$ that is neither real closed nor elementarily embedded (the sentence $exists x, x^2 = 2$ distinguishes $QQ$ from $RR$). They are replaced by the sound refinement `RCSubfieldStratum` (a stratum whose carrier is a real-closed subfield), for which inclusion elementarity follows from `RCFModelComplete`. This self-correction record — two former assumptions identified as false, with counterexample, and repaired by an honest weakening — is, we believe, the most scientifically credible feature of the methodology, and the reason the audit infrastructure exists.
]

== The honest limit construction

The original $NN$-indexed chain formulation of the limit-size milestone is vacuous: König's theorem gives $"cof"(c) > aleph_0$, so no countable chain of intermediate-size strata can union to $RR$. The same disease affected the earlier cardinality theorem `directLimit_card`, whose hypotheses were jointly unsatisfiable; it has been replaced by the identity/closure/sharpness triple of Section 4. The corrected limit-size statement (`ICAH/CofinalFamily.lean`) indexes the family by the ordinal `𝔠.ord`:

#theorem[
  `exists_cofinal_rc_family`: there is a monotone family of real-closed subfields of $RR$, indexed by `𝔠.ord`, each of intermediate cardinality, whose union is all of $RR$; and `cofinal_family_limit_size`: the union has cardinality $c$. Moreover the index length can be improved to the optimum $"cof"(c)$ (`exists_cofinal_rc_family_cof_length`), and no shorter family exists (`cofinal_family_length_lower_bound`).
]

== Recommended order of attack

+ Post the minimized in-framework statement of `RCFSubfieldRealElementary` on the Lean Zulip model-theory stream (resolving possible overlap with in-progress ordered-field/real-closure work) before any PR.
+ PR 1 (small, ZFC-pure, attractive): the DLS-based elementary-substrata existence for $RR$ plus the direct-limit cardinality identity `directLimit_card_eq_iSup`.
+ PR 2: the ambient-free Tarski–Vaught chain theorem for `Language.DirectLimit` (proved here as `ofLevelElem` / `realize_ofLevel_iff` for ℕ-indexed chains in the ring language; the upstream version should generalize the index order and language — the formula induction carries over verbatim, with the relation case no longer vacuous).
+ PR 3 (after dedup check): `Real.isRealClosed`, the root-closure criterion `isRealClosed_of_forall_root`, and `relAlgebraic_isRealClosed`.
+ Long-term: formalize quantifier elimination / model completeness for RCF in Mathlib's `ModelTheory` framework, modeled on the ACF files but via Robinson's test, discharging `RCFSubfieldRealElementary` --- the final gap.
