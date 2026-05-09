import Mathlib
import ICAH.Axioms
import ICAH.SizeAwareField

namespace ICAH

open Cardinal

/-!
## Definability strata `R[≤ n]`

This file sets up a placeholder structure for the strata you describe in ICAH.
Replace the axioms below with concrete definitions as your formalisation advances.
-/

/-- A definability stratum `R[≤ n]` represented as a subset `S ⊆ ℝ`,
    together with a cardinal `κ` recording its size and the basic bounds `ℵ₀ < κ < 2^ℵ₀`. -/
structure Stratum where
  n : Ordinal
  S : Set ℝ
  κ : Cardinal
  h_card : (# {x : ℝ // x ∈ S}) = κ
  h_bounds : (aleph0 : Cardinal) < κ ∧ κ < continuum

/-- ICAH envisions a real-closed field structure *internal* to each stratum.
    Here we only provide a placeholder field living on the subtype `S`. -/
def Stratum.carrier (R : Stratum) : Type := {x : ℝ // x ∈ R.S}

/-- Stub: a size-aware field attached to a stratum.
    You will eventually supply the real-closed field structure and show it is definable within the same level. -/
axiom fieldOnStratum (R : Stratum) :
  ∃ (F : SizeAwareField), F.carrier = R.carrier ∧ F.κ = R.κ

/-! ## M1 — Cardinal lemmas -/

/-- The designated cardinal of a stratum is positive. -/
lemma Stratum.card_pos (R : Stratum) : 0 < R.κ :=
  lt_trans Cardinal.aleph0_pos R.h_bounds.1

/-- The designated cardinal is strictly less than the continuum. -/
lemma Stratum.card_lt_continuum (R : Stratum) : R.κ < continuum :=
  R.h_bounds.2

/-- The designated cardinal is strictly greater than `ℵ₀`. -/
lemma Stratum.card_gt_aleph0 (R : Stratum) : aleph0 < R.κ :=
  R.h_bounds.1

/-- The designated cardinal is uncountable. -/
lemma Stratum.not_countable (R : Stratum) : ¬ R.κ ≤ aleph0 :=
  not_le.mpr R.h_bounds.1

/-! ## Synthetic example

Under `ICAH.not_CH`, `ℵ₁ < 𝔠`, so we can exhibit a concrete `Stratum`
whose carrier is a subset of `ℝ` of cardinality `ℵ₁`. -/

/-- A synthetic stratum of size `ℵ₁`, existing under `ICAH.not_CH`. -/
noncomputable def syntheticStratum : Stratum :=
  -- Under ¬CH, ℵ₁ ≤ #ℝ = 𝔠, so a subset of ℝ of size ℵ₁ exists.
  let hle : aleph 1 ≤ #ℝ := by rw [Cardinal.mk_real]; exact aleph_one_le_continuum
  let S := (Cardinal.le_mk_iff_exists_set.mp hle).choose
  let hS := (Cardinal.le_mk_iff_exists_set.mp hle).choose_spec
  { n       := 0
    S       := S
    κ       := aleph 1
    h_card  := hS
    h_bounds := ⟨aleph0_lt_aleph_one,
                 lt_of_le_of_ne aleph_one_le_continuum (Ne.symm not_CH)⟩ }

/-- Verify the bounds hold for `syntheticStratum`. -/
lemma syntheticStratum_bounds :
    aleph0 < syntheticStratum.κ ∧ syntheticStratum.κ < continuum :=
  syntheticStratum.h_bounds

end ICAH
