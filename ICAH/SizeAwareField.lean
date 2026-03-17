import Mathlib

namespace ICAH

open Cardinal

/-!
## Size-aware ordered fields

A `SizeAwareField` bundles a carrier type with its cardinality and the
algebraic instances for an ordered field.  `LinearOrderedField` was deprecated
in Mathlib (2025-10-30); we use `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`.
-/

/-- A carrier type together with its designated cardinal and ordered-field instances.
    Used to track which size layer a field lives in. -/
structure SizeAwareField where
  carrier  : Type*
  κ        : Cardinal
  [instField  : Field carrier]
  [instLinOrd : LinearOrder carrier]
  [instSOrd   : IsStrictOrderedRing carrier]
  hcard    : Cardinal.mk carrier = κ

attribute [instance] SizeAwareField.instField
attribute [instance] SizeAwareField.instLinOrd
attribute [instance] SizeAwareField.instSOrd

/-- Coerce a `SizeAwareField` to its carrier type. -/
abbrev SizeAwareField.toType (F : SizeAwareField) : Type* := F.carrier

/-- Notation `⟪F⟫` for the carrier of a size-aware field. -/
notation "⟪" F "⟫" => SizeAwareField.toType F

/-- The carrier has the recorded cardinality. -/
lemma SizeAwareField.card (F : SizeAwareField) : Cardinal.mk ⟪F⟫ = F.κ := F.hcard

end ICAH
