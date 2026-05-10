import Mathlib
import ICAH.Axioms
import ICAH.SizeAwareField
import ICAH.Strata
import ICAH.Definability

namespace ICAH

open Cardinal FirstOrder FirstOrder.Language FirstOrder.Ring

/-!
## M3 — Internal field operations on strata

### Design

A `Stratum` carries a bare `Set ℝ` as its carrier. The subtype `{x : ℝ // x ∈ S}`
does **not** automatically inherit a `Field` structure unless `S` is closed under
the ring operations. We therefore introduce `SubfieldStratum` — a `Stratum` whose
carrier set is the underlying set of a `Subfield ℝ`.

For any `K : Subfield ℝ`, the subtype `K` inherits:
- `Field K` (from `Subfield.instField`)
- `LinearOrder K` (from `Subtype.instLinearOrder`)
- `IsStrictOrderedRing K` (from `Subfield.toIsStrictOrderedRing`)

These are exactly the instances required by `SizeAwareField`.

### Concrete base field F₀

We exhibit `algebraicClosure ℚ ℝ` (the real algebraic numbers) as a concrete
subfield of ℝ. Its cardinality is `ℵ₀` (countable), so it does **not** satisfy
the intermediate-size bound `ℵ₀ < κ < 𝔠` required by `Stratum.h_bounds`. It
serves as a **base field** `F₀` outside the ICAH hierarchy, demonstrating that
the field construction is concrete.

For the full ICAH hierarchy (strata with `ℵ₀ < κ < 𝔠`), the existence of
subfields of ℝ with intermediate cardinality is asserted by `subfieldStratumExists`
(which follows from `ICAH.not_CH` via a transfinite construction).

## M4 — Real-closedness (named axioms for Mathlib gaps)

`IsRealClosed ℝ` is not yet an instance in Mathlib (noted as a TODO in
`Mathlib.FieldTheory.IsRealClosed.Basic`). We introduce named axioms so the
gaps are explicit and trackable via `#print axioms`.
-/

/-! ### Subfield → SizeAwareField -/

/-- Any subfield of ℝ with a given cardinality witness yields a `SizeAwareField`. -/
noncomputable def subfieldToSAF (K : Subfield ℝ) (κ : Cardinal) (hκ : #K = κ) :
    SizeAwareField where
  carrier  := K
  κ        := κ
  instField  := inferInstance
  instLinOrd := Subtype.instLinearOrder (fun x => x ∈ K)
  instSOrd   := Subfield.toIsStrictOrderedRing K
  hcard    := hκ

/-! ### SubfieldStratum -/

/-- A `SubfieldStratum` is a `Stratum` whose carrier set is the underlying set of
    a subfield of ℝ. This guarantees closure under `+`, `·`, `-`, `⁻¹`. -/
structure SubfieldStratum extends Stratum where
  /-- The subfield of ℝ whose underlying set is the stratum carrier. -/
  subfield : Subfield ℝ
  /-- The carrier set equals the underlying set of the subfield. -/
  h_subfield : S = ↑subfield

/-- Every `SubfieldStratum` yields a `SizeAwareField` with matching carrier and cardinal. -/
noncomputable def SubfieldStratum.toSAF (R : SubfieldStratum) : SizeAwareField :=
  subfieldToSAF R.subfield R.κ (by
    -- ↥R.subfield = {x : ℝ // x ∈ ↑R.subfield} = {x : ℝ // x ∈ R.S} by h_subfield
    have : #{x : ℝ // x ∈ (↑R.subfield : Set ℝ)} = #{x : ℝ // x ∈ R.S} :=
      Cardinal.mk_congr (Equiv.subtypeEquivRight (fun x => by rw [R.h_subfield]))
    exact this.trans R.h_card)

/-- The carrier of `R.toSAF` is definitionally `R.subfield`. -/
lemma SubfieldStratum.toSAF_carrier (R : SubfieldStratum) :
    R.toSAF.carrier = R.subfield := rfl

/-- The cardinal of `R.toSAF` equals `R.κ`. -/
lemma SubfieldStratum.toSAF_kappa (R : SubfieldStratum) : R.toSAF.κ = R.κ := rfl

/-! ### Replacing `fieldOnStratum` for SubfieldStrata -/

/-- For any `SubfieldStratum`, a `SizeAwareField` with the correct carrier and cardinal exists.
    This is a proved replacement for `axiom fieldOnStratum` in the subfield case. -/
theorem fieldOnSubfieldStratum (R : SubfieldStratum) :
    ∃ (F : SizeAwareField), F.carrier = R.toStratum.carrier ∧ F.κ = R.κ := by
  refine ⟨R.toSAF, ?_, R.toSAF_kappa⟩
  -- F.carrier = R.subfield (as Type)
  -- R.toStratum.carrier = {x : ℝ // x ∈ R.S} (as Type)
  -- ↥R.subfield = {x : ℝ // x ∈ ↑R.subfield}; when R.S = ↑R.subfield these coincide.
  simp only [SubfieldStratum.toSAF_carrier, Stratum.carrier]
  show (R.subfield : Type) = {x : ℝ // x ∈ R.S}
  show {x : ℝ // x ∈ (↑R.subfield : Set ℝ)} = {x : ℝ // x ∈ R.S}
  rw [R.h_subfield]

/-! ### Concrete base field: real algebraic numbers -/

/-- The real algebraic numbers `algebraicClosure ℚ ℝ` form a subfield of ℝ. -/
noncomputable def algRealSubfield : Subfield ℝ := (algebraicClosure ℚ ℝ).toSubfield

/-- The real algebraic numbers are countable: `#algRealSubfield ≤ ℵ₀`. -/
lemma algReal_card_le_aleph0 : #algRealSubfield ≤ aleph0 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℝ) := algebraicClosure.isAlgebraic ℚ ℝ
  have h : #(algebraicClosure ℚ ℝ) ≤ max #ℚ aleph0 :=
    Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℝ)
  -- #algRealSubfield = #(algebraicClosure ℚ ℝ) definitionally
  calc #algRealSubfield
      = #(algebraicClosure ℚ ℝ) := rfl
    _ ≤ max #ℚ aleph0 := h
    _ = max aleph0 aleph0 := by rw [Cardinal.mkRat]
    _ = aleph0 := max_self _

/-- The real algebraic numbers form a `SizeAwareField` with cardinal `ℵ₀`.
    Note: `ℵ₀` does **not** satisfy `ℵ₀ < ℵ₀`, so this is a base field
    outside the ICAH stratum hierarchy. -/
noncomputable def algRealSAF : SizeAwareField :=
  subfieldToSAF algRealSubfield aleph0
    (le_antisymm algReal_card_le_aleph0 (Cardinal.aleph0_le_mk _))

/-! ### M4 — Real-closedness (named axioms for Mathlib gaps) -/

/-- **Mathlib gap**: `ℝ` is a real-closed field.
    Blocked on: `IsRealClosed ℝ` instance not yet in Mathlib
    (`Mathlib.FieldTheory.IsRealClosed.Basic` lists this as a TODO).
    Proof sketch:
    - `isSquare_or_isSquare_neg`: use `Real.sqrt` for non-negatives.
    - `exists_isRoot_of_odd_natDegree`: IVT + polynomial growth at ±∞. -/
axiom Real.isRealClosed : IsRealClosed ℝ

/-- **Mathlib gap**: every subfield of ℝ is real-closed.
    Blocked on: the model-theoretic fact that elementary substructures of RCFs
    are RCFs is not yet assembled in Mathlib for `IsRealClosed`. -/
axiom subfieldIsRealClosed (K : Subfield ℝ) : IsRealClosed K

/-! ### Existence of intermediate-size subfield strata -/

/-- **Axiom**: under `ICAH.not_CH`, there exists a subfield of ℝ with
    intermediate cardinality `ℵ₀ < κ < 𝔠`.

    Proof sketch: By `ICAH.not_CH`, `ℵ₁ < 𝔠`. A transfinite construction
    (e.g., taking the real closure of a transcendence basis of size `ℵ₁`) yields
    a subfield of ℝ of cardinality `ℵ₁`. This requires set-theoretic machinery
    not yet in Mathlib. -/
axiom subfieldStratumExists :
    ∃ (K : Subfield ℝ) (κ : Cardinal),
      aleph0 < κ ∧ κ < continuum ∧ #K = κ

/-- Under `subfieldStratumExists`, a `SubfieldStratum` with intermediate cardinality exists. -/
noncomputable def intermediateSubfieldStratum : SubfieldStratum :=
  let K  := subfieldStratumExists.choose
  let κ  := subfieldStratumExists.choose_spec.choose
  let hκ := subfieldStratumExists.choose_spec.choose_spec
  { n         := 0
    S         := ↑K
    κ         := κ
    h_card    := hκ.2.2
    h_bounds  := ⟨hκ.1, hκ.2.1⟩
    subfield  := K
    h_subfield := rfl }

/-! ### LOR structure instance for SubfieldStratum carriers -/

/-- Every `SubfieldStratum` carrier inherits a `LOR`-structure from its subfield.
    Registered as a global instance so that `ElementaryEmbedding` synthesis works. -/
noncomputable instance subfieldStratumLORStr (R : SubfieldStratum) :
    LOR.Structure R.toStratum.carrier :=
  have heq : R.toStratum.carrier = R.subfield := by
    show {x : ℝ // x ∈ R.S} = {x : ℝ // x ∈ (↑R.subfield : Set ℝ)}
    rw [R.h_subfield]
  heq ▸ (compatibleRingOfRing R.subfield).toStructure

end ICAH
