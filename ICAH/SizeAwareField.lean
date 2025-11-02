import Mathlib

namespace ICAH

open Cardinal

/-- A size-aware ordered field with a designated cardinal `κ`.
    This is a light wrapper used to talk about carriers together with their size. -/
structure SizeAwareField where
  carrier : Type u
  κ : Cardinal
  inst : LinearOrderedField carrier

  -- the designated size of the carrier
  hcard : (#carrier) = κ

attribute [instance] SizeAwareField.inst

notation "⟪" F "⟫" => F.carrier

/-- The carrier of a size-aware field has the recorded cardinality. -/
lemma SizeAwareField.card (F : SizeAwareField) : (#⟪F⟫) = F.κ := F.hcard

end ICAH
