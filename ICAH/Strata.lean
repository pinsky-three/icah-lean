import Mathlib
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

end ICAH
