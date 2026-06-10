import Mathlib
import ICAH.Axioms
import ICAH.Strata
import ICAH.Definability
import ICAH.RealClosed
import ICAH.FieldOnStratum
import ICAH.ElementaryChain
import ICAH.CofinalFamily

namespace ICAH

open Cardinal FirstOrder FirstOrder.Language FirstOrder.Ring

/-!
## ICAH — Main statement

`ICAHStatement` is the conjunction of the four core claims from the README:

1. **(M1) Intermediate-size strata**: For each ordinal `n`, there exists a stratum
   `R` with `R.n = n` and `ℵ₀ < #R < 𝔠`.

2. **(M3) Internal arithmetic**: Each stratum carries a `SizeAwareField` structure
   with the same carrier and cardinal.

3. **(M5) Elementary chain**: A `StratumChain` whose direct limit is elementarily
   equivalent to `ℝ` in `LOR`.

4. **(M6) Limit size**: A `𝔠.ord`-indexed monotone family of intermediate-size
   subfields of ℝ whose union has cardinality `𝔠`.  (The former ℕ-indexed
   formulation was vacuous by König's theorem — see `ICAH.CofinalFamily`.)

### Axiom inventory

Run `#print axioms icahTheorem` to see the full axiom set. Expected non-kernel axioms:
- `ICAH.not_CH` — the ¬CH assumption (intentional, definitional for ICAH).
- `ICAH.rcfModelComplete` — model completeness of RCF (Tarski–Seidenberg), the
  single remaining Mathlib gap.

Everything else that used to be an axiom (`fieldOnStratum`, `Real.isRealClosed`,
`subfieldIsRealClosed`, `subfieldStratumExists`, `losDirectLimit`,
`subfieldStratumElemEmb`) has been proved or deleted (the two false ones).
-/

/-! ### ICAHStatement -/

/-- The four core claims of ICAH, assembled from the milestone results. -/
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

/-! ### Proof of ICAHStatement -/

/-- ICAH holds, assembling all milestone results.

    **Axiom dependency** (see `#print axioms icahTheorem` below):
    - `ICAH.not_CH`: ¬CH (global assumption)
    - `ICAH.rcfModelComplete`: model completeness of RCF (Mathlib gap) -/
theorem icahTheorem : ICAHStatement where
  -- M1: Build a stratum with the requested ordinal index, reusing syntheticStratum's
  -- cardinal witness (which exists under not_CH).
  strata_exist := fun n =>
    ⟨{ n       := n
       S       := syntheticStratum.S
       κ       := syntheticStratum.κ
       h_card  := syntheticStratum.h_card
       h_bounds := syntheticStratum.h_bounds }, rfl⟩
  -- M3: fieldOnStratum is now a theorem (Equiv transport from a real-closed
  -- subfield of the right cardinality).
  field_on_stratum := fieldOnStratum
  -- M5: Constant StratumChain on intermediateRCSubfieldStratum; each level embeds
  -- elementarily into ℝ via rcfModelComplete, and losDirectLimit (now a theorem)
  -- gives the elementary equivalence of the direct limit with ℝ.
  elementary_chain := by
    let R  := intermediateRCSubfieldStratum
    let SC := mkConstantSC R.toSubfieldStratum
    let hEmb : ∀ n, SC.toElemChain.obj n ↪ₑ[LOR] ℝ := fun _ => rcfModelComplete R
    have hCompat : ∀ n x, hEmb (n + 1) (SC.toElemChain.emb n x) = hEmb n x :=
      fun _ _ => rfl
    exact ⟨SC, ElemChain.losDirectLimit SC.toElemChain hEmb hCompat⟩
  -- M6: the cofinal family of intermediate-size real-closed subfields covering ℝ.
  limit_size := cofinal_family_limit_size

-- Axiom inventory: all non-kernel axioms used by icahTheorem.
-- `#guard_msgs` turns any drift in this axiom set into a build failure.
/--
info: 'ICAH.icahTheorem' depends on axioms: [propext, Classical.choice, not_CH, rcfModelComplete, Quot.sound]
-/
#guard_msgs in
#print axioms icahTheorem

end ICAH
