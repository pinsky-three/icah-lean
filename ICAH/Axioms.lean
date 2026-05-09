import Mathlib

namespace ICAH

open Cardinal

/-!
## Global set-theoretic axioms for ICAH

ICAH requires the existence of cardinals strictly between `ℵ₀` and `2^ℵ₀`,
which is consistent with ZFC but independent of it (it fails under CH).
We therefore assume `¬CH` as a named axiom so that all downstream uses are
explicit and trackable via `#print axioms`.

Run `#print axioms ICAH.not_CH` to confirm this is the only non-standard axiom.
-/

/-- The negation of the Continuum Hypothesis: `2^ℵ₀ ≠ ℵ₁`.
    Consistent with ZFC (Cohen 1963). Required for ICAH's intermediate-size strata. -/
axiom not_CH : continuum ≠ aleph 1

/-- Consequence: there exists a cardinal strictly between `ℵ₀` and `2^ℵ₀`.
    This is the key existence fact used to populate `Stratum.h_bounds`. -/
theorem exists_intermediate_cardinal : ∃ κ : Cardinal, aleph0 < κ ∧ κ < continuum := by
  -- Under ¬CH, aleph 1 < continuum, and aleph0 < aleph 1.
  use aleph 1
  constructor
  · exact aleph0_lt_aleph_one
  · exact lt_of_le_of_ne (aleph_one_le_continuum) (Ne.symm not_CH)

end ICAH
