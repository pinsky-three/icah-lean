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

-- `fieldOnStratum` (formerly an axiom here) is now a theorem in
-- `ICAH.FieldOnStratum`, proved by transporting a real-closed subfield of the
-- right cardinality across an equivalence with the stratum carrier.

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

/-! ## König's theorem at the continuum

`cof(𝔠) > ℵ₀` is the obstruction that makes any ℕ-indexed exhaustion of ℝ by
strata impossible; it is used both for the direct-limit closure theorem
(`ElemChain.directLimit_card_lt_continuum`) and the cofinal-family length
lower bound (`cofinal_family_length_lower_bound`). -/

/-- **König**: the cofinality of the continuum is uncountable.
    Instance of `Cardinal.lt_cof_ord_power` at `𝔠 = 2 ^ ℵ₀`. -/
lemma aleph0_lt_cof_ord_continuum : aleph0 < continuum.ord.cof := by
  have h := Cardinal.lt_cof_ord_power (le_refl aleph0) Cardinal.one_lt_two
  rwa [Cardinal.two_power_aleph0] at h

/-! ## Synthetic example

Under `ICAH.NotCH`, `ℵ₁ < 𝔠`, so we can exhibit a concrete `Stratum`
whose carrier is a subset of `ℝ` of cardinality `ℵ₁`. -/

/-- A synthetic stratum of size `ℵ₁`, existing under `NotCH`. -/
noncomputable def syntheticStratum (h : NotCH) : Stratum :=
  -- Under ¬CH, ℵ₁ ≤ #ℝ = 𝔠, so a subset of ℝ of size ℵ₁ exists.
  let hle : aleph 1 ≤ #ℝ := by rw [Cardinal.mk_real]; exact aleph_one_le_continuum
  let S := (Cardinal.le_mk_iff_exists_set.mp hle).choose
  let hS := (Cardinal.le_mk_iff_exists_set.mp hle).choose_spec
  { n       := 0
    S       := S
    κ       := aleph 1
    h_card  := hS
    h_bounds := ⟨aleph0_lt_aleph_one, aleph_one_lt_continuum_of_notCH h⟩ }

/-- Verify the bounds hold for `syntheticStratum`. -/
lemma syntheticStratum_bounds (h : NotCH) :
    aleph0 < (syntheticStratum h).κ ∧ (syntheticStratum h).κ < continuum :=
  (syntheticStratum h).h_bounds

end ICAH
