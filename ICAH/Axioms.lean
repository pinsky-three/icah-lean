import Mathlib

namespace ICAH

open Cardinal

/-!
## Global set-theoretic hypotheses for ICAH

ICAH requires the existence of cardinals strictly between `ℵ₀` and `2^ℵ₀`,
which is consistent with ZFC but independent of it (it fails under CH).

A former version of this file declared `¬CH` as a global `axiom not_CH`.
It is now a named `Prop` (`NotCH`) threaded through the development as an
explicit hypothesis: the audit *is* the type signature of each theorem, the
environment contains **zero** project axioms, and the `#guard_msgs` blocks in
`ICAH.Main` lock the axiom set of every flagship result to the Lean kernel
axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

/-- The negation of the Continuum Hypothesis: `2^ℵ₀ ≠ ℵ₁`.
    Consistent with ZFC (Cohen 1963). Required for ICAH's intermediate-size
    strata. Threaded through the development as an explicit hypothesis rather
    than declared as an axiom. -/
def NotCH : Prop := continuum.{0} ≠ aleph.{0} 1

/-- Under `¬CH`, `ℵ₁` is strictly below the continuum. -/
theorem aleph_one_lt_continuum_of_notCH (h : NotCH) :
    aleph.{0} 1 < continuum.{0} :=
  lt_of_le_of_ne aleph_one_le_continuum (Ne.symm h)

/-- Consequence of `¬CH`: there exists a cardinal strictly between `ℵ₀` and
    `2^ℵ₀`. This is the key existence fact used to populate
    `Stratum.h_bounds`. -/
theorem exists_intermediate_cardinal (h : NotCH) :
    ∃ κ : Cardinal.{0}, aleph0 < κ ∧ κ < continuum :=
  ⟨aleph 1, aleph0_lt_aleph_one, aleph_one_lt_continuum_of_notCH h⟩

end ICAH
