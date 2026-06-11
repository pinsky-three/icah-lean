import Mathlib
import ICAH.Axioms
import ICAH.Strata
import ICAH.Definability
import ICAH.RealClosed
import ICAH.FieldOnStratum
import ICAH.ElementaryChain
import ICAH.ElementaryStrata
import ICAH.CofinalFamily

namespace ICAH

open Cardinal FirstOrder FirstOrder.Language FirstOrder.Ring

/-!
## ICAH — Main statements (two pillars)

The development proves two main theorems, sharing the `NotCH` hypothesis:

* **Pillar A** (`icahElementary`, in `ICAH.ElementaryStrata`): the *semantic*
  ICAH statement — strata are elementary substructures of ℝ produced by
  downward Löwenheim–Skolem — holds under `NotCH` **alone**.
* **Pillar B** (`icahTheorem`, this file): the *algebraic realization* —
  strata are concrete real-closed subfields (relative algebraic closures) —
  additionally assumes `RCFModelComplete` (model completeness of RCF, the
  single remaining Mathlib gap).

`ICAHStatement` is the conjunction of the four core claims:

1. **(M1) Intermediate-size strata**: For each ordinal `n`, there exists a
   stratum `R` with `R.n = n` and `ℵ₀ < #R < 𝔠`.
2. **(M3) Internal arithmetic**: Each stratum carries a `SizeAwareField`
   structure with the same carrier and cardinal.
3. **(M5) Elementary chain**: A `StratumChain` whose direct limit is
   elementarily equivalent to `ℝ` in `LOR`.
4. **(M6) Limit size**: A `𝔠.ord`-indexed monotone family of
   intermediate-size subfields of ℝ whose union has cardinality `𝔠`.
   (The former ℕ-indexed formulation was vacuous by König's theorem — see
   `ICAH.CofinalFamily`, which also proves the sharp `cf(𝔠)` optimality
   results.)

### Hypothesis (not axiom) inventory

The project declares **zero** axioms.  The former axioms `not_CH` and
`rcfModelComplete` are now named `Prop`s (`NotCH`, `RCFModelComplete`) taken
as explicit hypotheses, so the audit is the type signature of each theorem
and every `#print axioms` below reports only the Lean kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`).  The `#guard_msgs` blocks turn
any drift — including a hidden `sorryAx` — into a build failure.

Everything else that used to be an axiom (`fieldOnStratum`,
`Real.isRealClosed`, `subfieldIsRealClosed`, `subfieldStratumExists`,
`losDirectLimit` (now `tarskiVaughtDirectLimit`), `subfieldStratumElemEmb`)
has been proved or deleted (the two false ones).
-/

/-! ### ICAHStatement -/

/-- The four core claims of ICAH (Pillar B: algebraic realization),
    assembled from the milestone results. -/
structure ICAHStatement : Prop where
  /-- M1: For every ordinal, an intermediate-size stratum exists. -/
  strata_exist : ∀ (n : Ordinal), ∃ R : Stratum, R.n = n
  /-- M3: Every stratum admits a size-aware field structure. -/
  field_on_stratum : ∀ (R : Stratum), ∃ F : SizeAwareField, F.carrier = R.carrier ∧ F.κ = R.κ
  /-- M5: There exists a StratumChain whose direct limit is elementarily equivalent to ℝ. -/
  elementary_chain : ∃ (SC : StratumChain), SC.toElemChain.DirectLim ≅[LOR] ℝ
  /-- M6 (honest form): a `𝔠.ord`-indexed monotone family of subfields of ℝ,
      each of intermediate size, whose union has cardinality `𝔠`. -/
  limit_size : ∃ K : ContinuumIdx → Subfield ℝ,
    Monotone K ∧
    (∀ i, aleph0 < #(K i) ∧ #(K i) < continuum) ∧
    #(⋃ i, (K i : Set ℝ)) = continuum

/-! ### Helper: constant StratumChain on a SubfieldStratum -/

/-- Build a constant `StratumChain` from a `SubfieldStratum`.
    All levels are the same stratum; the successor embeddings are identity.
    The `LOR`-structure on the carrier is provided by `subfieldStratumLORStr`. -/
noncomputable def mkConstantSC (R : SubfieldStratum) : StratumChain where
  strata  := fun _ => R.toStratum
  strStr  := fun _ => subfieldStratumLORStr R
  embSucc := fun _ => ElementaryEmbedding.refl LOR _

/-! ### Proof of ICAHStatement (Pillar B) -/

/-- **Pillar B**: ICAH's algebraic realization, assembling all milestone
    results.  Takes both hypotheses explicitly:
    - `hCH : NotCH` — the ¬CH regime;
    - `hMC : RCFModelComplete` — model completeness of RCF (Mathlib gap).

    Compare `icahElementary` (Pillar A), which needs only `NotCH`. -/
theorem icahTheorem (hCH : NotCH) (hMC : RCFModelComplete) : ICAHStatement where
  -- M1: Build a stratum with the requested ordinal index, reusing syntheticStratum's
  -- cardinal witness (which exists under NotCH).
  strata_exist := fun n => ⟨{ syntheticStratum hCH with n := n }, rfl⟩
  -- M3: fieldOnStratum is a theorem (Equiv transport from a real-closed
  -- subfield of the right cardinality).
  field_on_stratum := fieldOnStratum
  -- M5: Constant StratumChain on intermediateRCSubfieldStratum; each level embeds
  -- elementarily into ℝ via the RCFModelComplete hypothesis, and
  -- tarskiVaughtDirectLimit gives the elementary equivalence of the direct
  -- limit with ℝ.
  elementary_chain := by
    let R  := intermediateRCSubfieldStratum hCH
    let SC := mkConstantSC R.toSubfieldStratum
    let hEmb : ∀ n, SC.toElemChain.obj n ↪ₑ[LOR] ℝ := fun _ => hMC.emb R
    have hCompat : ∀ n x, hEmb (n + 1) (SC.toElemChain.emb n x) = hEmb n x :=
      fun _ _ => rfl
    exact ⟨SC, ElemChain.tarskiVaughtDirectLimit SC.toElemChain hEmb hCompat⟩
  -- M6: the cofinal family of intermediate-size real-closed subfields covering ℝ.
  limit_size := cofinal_family_limit_size hCH

/-! ### Axiom audits

All flagship results depend only on the Lean kernel axioms.  `#guard_msgs`
turns any drift in these axiom sets into a build failure. -/

/--
info: 'ICAH.icahTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms icahTheorem

/--
info: 'ICAH.icahElementary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms icahElementary

/-! #### Pillar A building blocks -/

/--
info: 'ICAH.exists_elementary_substratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_elementary_substratum

/--
info: 'ICAH.elemSubstratumSubfield' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms elemSubstratumSubfield

/-! #### Pillar B building blocks -/

/--
info: 'ICAH.exists_rc_subfield' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_rc_subfield

/--
info: 'ICAH.relAlgebraic_isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms relAlgebraic_isRealClosed

/--
info: 'ICAH.Real.isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Real.isRealClosed

/--
info: 'ICAH.fieldOnStratum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fieldOnStratum

/-! #### Elementary chains and direct limits -/

/--
info: 'ICAH.ElemChain.tarskiVaughtDirectLimit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ElemChain.tarskiVaughtDirectLimit

/--
info: 'ICAH.ElemChain.ofLevelElem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ElemChain.ofLevelElem

/--
info: 'ICAH.ElemChain.directLimit_card_eq_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ElemChain.directLimit_card_eq_iSup

/--
info: 'ICAH.ElemChain.directLimit_card_lt_continuum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ElemChain.directLimit_card_lt_continuum

/-! #### Cofinal families and optimality -/

/--
info: 'ICAH.cofinal_family_length_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cofinal_family_length_lower_bound

/--
info: 'ICAH.exists_cofinal_rc_family_cof_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_cofinal_rc_family_cof_length

end ICAH
