import Mathlib
import ICAH.Strata

namespace ICAH

/-!
## ICAH — statement stub

Refine `ICAHStatement` as your formal specification solidifies.
-/

def ICAHStatement : Prop :=
  ∀ (n : Ordinal),  -- (eventually: assume `n` countable)
    ∃ R : Stratum, R.n = n

-- Treat the high-level research claim as an axiom for now so the library compiles.
axiom ICAH : ICAHStatement

end ICAH
