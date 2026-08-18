#import "../src/macros.typ": *

= Hypothesis inventory, per-theorem audit, and Mathlib roadmap

A central strength of the Lean development is that it does not hide its assumptions. The project declares *zero* axioms: the two named assumptions are ordinary `Prop`s threaded through the development as explicit hypotheses, so the assumption set of every theorem is visible in its type signature. The kernel-level audit is enforced in-source by `#guard_msgs in #print axioms` blocks and checked in CI:

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

== The remaining Mathlib-facing gap (Pillar B)

#gap[
  `ICAH.RCFSubfieldRealElementary : Prop` (compatibility spelling `ICAH.RCFModelComplete`): the inclusion of a real-closed subfield of $RR$ into $RR$ is an elementary embedding in the ring language (in which the order of a real-closed field is definable via squares). This is the $RR$-specialized consequence of model completeness of the theory of real-closed fields needed by Pillar B.
]

This is a true classical theorem whose first-order formalization follows from quantifier elimination @tarski1951 or model completeness for RCF inside Mathlib's `ModelTheory` framework, neither of which is currently available in the needed form in the pinned Mathlib revision. It is consumed only by Pillar B (`nestedRCEmbedding`, `exists_cofinal_rc_family_elementary`, and the last clause of `icahTheorem`). Pillar A (`icahElementary`, `exists_cofinal_elem_family`) avoids it entirely via downward Löwenheim–Skolem.

The claim that this is "the remaining gap" is local to this development and the pinned Mathlib revision. Ordered-field model theory is an active area; the engagement plan in Section 8 posts a minimized statement on the Lean Zulip *before* any upstream PR, precisely to catch in-progress work.

#remark[
  *Why this gap is harder than the ACF precedent.* Mathlib already contains the deep-embedded model theory of algebraically closed fields: the theory `ACF p` over the ring language, its completeness for $p$ prime or zero (`ACF_isComplete`), and the Lefschetz principle. That suggests a template — but completeness of ACF comes cheap via uncountable categoricity and the Łoś–Vaught test, a route that is *closed* for RCF: the theory of real-closed fields is unstable (it defines a linear order) and has the maximum number of models in every uncountable cardinality. Discharging `RCFSubfieldRealElementary` therefore requires QE-grade work — e.g. Robinson's model-completeness test with sign-change/root-counting embedding arguments inside the deep embedding — substantially more than porting the ACF files.

  Prior art calibrates the effort: the `math-comp/real-closed` library in Coq/Rocq contains a certified quantifier-elimination procedure for RCF with the decision procedure `rcf_sat` and its correctness proof (Cohen–Mahboubi @cohen_mahboubi_lmcs), and HOL Light has McLaughlin–Harrison's proof-producing decision procedure for RCF @mclaughlin_harrison_cade. Neither transfers directly to Mathlib's `FirstOrder` framework, but Cohen–Mahboubi is the closest blueprint.
]

== Per-theorem audit

Because the hypotheses are explicit, the audit can be given per theorem. The classification below is the contractual content of the development:

+ *ZFC-pure* (kernel axioms only, no project hypotheses): `exists_elementary_substratum`, `exists_elementary_substratum_extending`, `elemSubstratumSubfield`, `elemSubstratum_models_thReal`, `elementaryInclusion`, `directed_iSup_isElementary`, `exists_rc_subfield`, `relAlgebraic_isRealClosed`, `isRealClosed_of_forall_root`, `Real.isRealClosed`, `tarskiVaughtDirectLimit`, `ofLevelElem` (the ambient-free chain theorem), `directLimit_card_eq_iSup`, `directLimit_card_lt_continuum`, `directLimit_intermediate`, `cofinal_family_length_lower_bound`, `fieldOnStratum`, `fieldOnSubfieldStratum`, `algReal_card_le_aleph0`.
+ *Under `NotCH`*: `exists_intermediate_cardinal`, `syntheticStratum`, `subfieldStratumExists` (the `NotCH`-specialized wrapper of the ZFC-pure `exists_rc_subfield`, instantiated at $aleph_1$), `intermediateRCSubfieldStratum`, `strictElemChain`, `exists_cofinal_elem_family`, `exists_cofinal_elem_family_cof_length`, `exists_cofinal_rc_family`, `exists_cofinal_rc_family_cof_length`, `cofinal_family_limit_size`, and the Pillar A main theorem `icahElementary` (descriptive alias `elementaryStrata`).
+ *Under `NotCH` and `RCFModelComplete`*: `nestedRCEmbedding`, `exists_cofinal_rc_family_elementary`, and the last clause of `icahTheorem` (descriptive alias `algebraicRealization`). The M1/M3/M5/M6 clauses of `icahTheorem` are available from `NotCH` alone; the RCF hypothesis is used only for elementary inclusions of the named real-closed family.

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

The original $NN$-indexed chain formulation of the limit-size milestone is vacuous: König's theorem gives $"cof"(c) > aleph_0$, so no countable chain of intermediate-size strata can union to $RR$. The same disease affected the earlier cardinality theorem `directLimit_card`, whose hypotheses were jointly unsatisfiable; it has been replaced by the identity/closure/sharpness triple of Section 4. The corrected limit-size statements index families by `𝔠.ord` (or by $"cof"(c)$ after compression along a fundamental sequence):

#theorem[
  `exists_cofinal_elem_family`: a monotone family of elementary substrata of $RR$, indexed by `𝔠.ord`, each of intermediate cardinality, covering $RR$, with elementary inclusions. The same length optimum $"cof"(c)$ is attained (`exists_cofinal_elem_family_cof_length`). The named real-closed counterpart is `exists_cofinal_rc_family`; under `RCFModelComplete` its inclusions are elementary.
]

== Recommended order of attack

+ Post the minimized in-framework statement of `RCFSubfieldRealElementary` on the Lean Zulip model-theory stream (resolving possible overlap with in-progress ordered-field/real-closure work) before any PR.
+ PR 1 (small, ZFC-pure, attractive): the DLS-based elementary-substrata existence for $RR$ plus the direct-limit cardinality identity `directLimit_card_eq_iSup`.
+ PR 2: the ambient-free Tarski–Vaught chain theorem for `Language.DirectLimit` (proved here as `ofLevelElem` / `realize_ofLevel_iff` for ℕ-indexed chains in the ring language; the upstream version should generalize the index order and language — the formula induction carries over verbatim, with the relation case no longer vacuous). Companion: `elementaryInclusion` and `directed_iSup_isElementary`.
+ PR 3 (after dedup check): `Real.isRealClosed`, the root-closure criterion `isRealClosed_of_forall_root`, and `relAlgebraic_isRealClosed`.
+ Long-term: formalize quantifier elimination / model completeness for RCF in Mathlib's `ModelTheory` framework, modeled on the ACF files but via Robinson's test, discharging `RCFSubfieldRealElementary`.
