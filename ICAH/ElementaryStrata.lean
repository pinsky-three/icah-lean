import Mathlib
import ICAH.Axioms
import ICAH.Strata
import ICAH.Definability
import ICAH.ElementaryChain

/-!
## Pillar A — Elementary substrata via downward Löwenheim–Skolem

This module proves the *semantic* form of ICAH from `NotCH` alone, with no
model-completeness hypothesis: strata are taken to be **elementary
substructures** of ℝ in the ring language `LOR`, produced at every
intermediate cardinality by Mathlib's downward Löwenheim–Skolem theorem
(`FirstOrder.Language.exists_elementarySubstructure_card_eq`, built via
Skolem functions).

### The duality with Pillar B (`ICAH.FieldOnStratum`)

* **Pillar A (this file)**: elementarity is *free* — an elementary
  substructure is elementarily equivalent to ℝ by definition.  The cost is
  concreteness: the strata are Skolem hulls rather than explicitly generated
  algebraic closures.  The bridge lemma `elemSubstratumSubfield` recovers
  basic algebraic structure: every elementary substratum is (the carrier of) a
  subfield of ℝ.  Proving that these substrata are real closed is the next
  natural strengthening: it should follow by transferring a ring-language
  axiomatization of real-closed fields.
* **Pillar B**: strata are concrete — relative algebraic closures of
  generated subfields, with native `IsRealClosed` instances.  The cost is
  elementarity, which requires the ℝ-specialized real-closed-subfield
  elementarity consequence of RCF model completeness (`RCFModelComplete`, the
  single remaining Mathlib gap).

### Key results

1. `exists_elementary_substratum_extending` — DLS specialized to ℝ: for every
   `ℵ₀ ≤ κ ≤ 𝔠` and every set `s ⊆ ℝ` of size `≤ κ`, an elementary
   substructure of ℝ of size exactly `κ` containing `s`.
2. `elemSubstratumSubfield` — the carrier of an elementary substratum is a
   subfield of ℝ (closure under inverses via one formula transfer).
3. `ICAHElementary` / `icahElementary` — the semantic ICAH statement, proved
   from `NotCH` **alone** (kernel axioms only; see the audit in `ICAH.Main`).
-/

namespace ICAH

open Cardinal FirstOrder FirstOrder.Language FirstOrder.Ring
open FirstOrder.Ring.CompatibleRing

/-! ### Downward Löwenheim–Skolem specialized to ℝ -/

/-- **DLS for ℝ in the ring language**: for every infinite `κ ≤ 𝔠` and every
    set `s ⊆ ℝ` with `#s ≤ κ`, there is an elementary substructure of ℝ of
    cardinality exactly `κ` containing `s`.  Elementarity comes for free —
    no Tarski–Seidenberg needed. -/
theorem exists_elementary_substratum_extending (s : Set ℝ) {κ : Cardinal}
    (hs : #s ≤ κ) (h0 : aleph0 ≤ κ) (hc : κ ≤ continuum) :
    ∃ S : LOR.ElementarySubstructure ℝ, s ⊆ S ∧ #S = κ := by
  obtain ⟨S, hsub, hS⟩ :=
    Language.exists_elementarySubstructure_card_eq LOR s κ h0
      (by simpa using hs)
      (by
        rw [show LOR.card = 5 from card_ring]
        have h5 : (5 : Cardinal) ≤ κ :=
          le_trans (Cardinal.lt_aleph0.mpr ⟨5, by norm_num⟩).le h0
        simpa using h5)
      (by rw [Cardinal.mk_real]; simpa using hc)
  exact ⟨S, hsub, by simpa using hS⟩

/-- An elementary substratum of every infinite cardinality up to `𝔠`. -/
theorem exists_elementary_substratum {κ : Cardinal}
    (h0 : aleph0 ≤ κ) (hc : κ ≤ continuum) :
    ∃ S : LOR.ElementarySubstructure ℝ, #S = κ := by
  obtain ⟨S, -, hS⟩ :=
    exists_elementary_substratum_extending (∅ : Set ℝ) (by simp) h0 hc
  exact ⟨S, hS⟩

/-! ### Bridge: elementary substrata are subfields of ℝ -/

/-- The first-order formula `∃ y, x · y = 1` in the ring language, with one
    free variable. Used to transfer closure under inverses along
    elementarity. -/
def invFormula : LOR.Formula (Fin 1) :=
  BoundedFormula.ex
    (Term.bdEqual
      (Term.var (Sum.inl (0 : Fin 1)) * Term.var (Sum.inr (0 : Fin 1)) :
        LOR.Term (Fin 1 ⊕ Fin 1))
      1)

/-- Realization of `invFormula` in ℝ. -/
lemma realize_invFormula (v : Fin 1 → ℝ) :
    invFormula.Realize v ↔ ∃ y : ℝ, v 0 * y = 1 := by
  unfold invFormula Formula.Realize
  rw [BoundedFormula.realize_ex]
  refine exists_congr fun y => ?_
  rw [BoundedFormula.realize_bdEqual]
  simp [Fin.snoc]

/-- The carrier of an elementary substructure of ℝ is a **subfield** of ℝ:
    closure under the ring operations comes from being a substructure of the
    ring language; closure under inverses is one formula transfer
    (`invFormula`) along elementarity. -/
noncomputable def elemSubstratumSubfield (S : LOR.ElementarySubstructure ℝ) :
    Subfield ℝ where
  carrier := S
  zero_mem' := by
    have h := (S : LOR.Substructure ℝ).fun_mem (zeroFunc : LOR.Constants) ![]
      (fun i => i.elim0)
    rw [funMap_zero] at h
    exact h
  one_mem' := by
    have h := (S : LOR.Substructure ℝ).fun_mem (oneFunc : LOR.Constants) ![]
      (fun i => i.elim0)
    rw [funMap_one] at h
    exact h
  add_mem' := by
    intro a b ha hb
    have h := (S : LOR.Substructure ℝ).fun_mem addFunc ![a, b]
      (fun i => by fin_cases i; exacts [ha, hb])
    rw [funMap_add] at h
    exact h
  mul_mem' := by
    intro a b ha hb
    have h := (S : LOR.Substructure ℝ).fun_mem mulFunc ![a, b]
      (fun i => by fin_cases i; exacts [ha, hb])
    rw [funMap_mul] at h
    exact h
  neg_mem' := by
    intro a ha
    have h := (S : LOR.Substructure ℝ).fun_mem negFunc ![a]
      (fun i => by fin_cases i; exact ha)
    rw [funMap_neg] at h
    exact h
  inv_mem' := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [inv_zero]
      have h := (S : LOR.Substructure ℝ).fun_mem (zeroFunc : LOR.Constants) ![]
        (fun i => i.elim0)
      rw [funMap_zero] at h
      exact h
    -- ℝ realizes `∃ y, x · y = 1`; transfer the witness into S.
    have hR : invFormula.Realize (fun _ => x) :=
      (realize_invFormula _).mpr ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
    have hS : invFormula.Realize (fun _ : Fin 1 => (⟨x, hx⟩ : S)) :=
      (S.isElementary invFormula _).mp hR
    -- Extract the witness y ∈ S and push the equation back to ℝ
    -- through the elementary inclusion `S.subtype`.
    unfold invFormula Formula.Realize at hS
    rw [BoundedFormula.realize_ex] at hS
    obtain ⟨y, hy⟩ := hS
    have hyR := (S.subtype.map_boundedFormula _ _ _).mpr hy
    rw [BoundedFormula.realize_bdEqual] at hyR
    have hxy : x * (y : ℝ) = 1 := by
      simpa [Fin.snoc] using hyR
    have hinv : x⁻¹ = (y : ℝ) := inv_eq_of_mul_eq_one_right hxy
    rw [hinv]
    exact y.2

@[simp]
lemma mem_elemSubstratumSubfield {S : LOR.ElementarySubstructure ℝ} {x : ℝ} :
    x ∈ elemSubstratumSubfield S ↔ x ∈ S := Iff.rfl

/-! ### Constant elementary chains on a substratum -/

/-- The constant elementary chain at an elementary substructure `S ≼ ℝ`. -/
noncomputable def constElemChain (S : LOR.ElementarySubstructure ℝ) :
    ElemChain where
  obj := fun _ => S
  str := fun _ => inferInstance
  emb := fun _ => ElementaryEmbedding.refl LOR S

/-- The direct limit of the constant chain at `S ≼ ℝ` is elementarily
    equivalent to ℝ: instance of `tarskiVaughtDirectLimit` with the canonical
    elementary inclusions `S.subtype`. -/
theorem constElemChain_directLim_equiv (S : LOR.ElementarySubstructure ℝ) :
    (constElemChain S).DirectLim ≅[LOR] ℝ :=
  ElemChain.tarskiVaughtDirectLimit (constElemChain S)
    (fun _ => S.subtype) (fun _ _ => rfl)

/-! ### The semantic ICAH statement (Pillar A) -/

/-- **The semantic ICAH statement**: strata are elementary substructures of
    ℝ in the ring language.  Every clause is provable from `NotCH` alone —
    elementarity is free by construction (downward Löwenheim–Skolem), so no
    model-completeness hypothesis appears. -/
structure ICAHElementary : Prop where
  /-- The intermediate band is nonempty (this is exactly ¬CH). -/
  band_nonempty : ∃ κ : Cardinal.{0}, aleph0 < κ ∧ κ < continuum
  /-- For every intermediate cardinal there is an elementary substratum of ℝ
      of exactly that size (ZFC-pure; DLS). -/
  strata_exist : ∀ κ : Cardinal.{0}, aleph0 < κ → κ < continuum →
    ∃ S : LOR.ElementarySubstructure ℝ, #S = κ
  /-- There is an elementary chain of intermediate-size strata whose direct
      limit is elementarily equivalent to ℝ. -/
  elementary_chain : ∃ C : ElemChain.{0},
    (∀ n, aleph0 < #(C.obj n) ∧ #(C.obj n) < continuum) ∧
    (C.DirectLim ≅[LOR] ℝ)
  /-- Closure (König, ZFC-pure): countable chains of strata of size `< 𝔠`
      never escape the hierarchy. -/
  chain_closure : ∀ C : ElemChain.{0}, (∀ n, #(C.obj n) < continuum) →
    #(C.DirectLim) < continuum
  /-- Cofinality: every real lies in some intermediate elementary
      substratum. -/
  cofinal : ∀ x : ℝ, ∃ S : LOR.ElementarySubstructure ℝ,
    aleph0 < #S ∧ #S < continuum ∧ x ∈ S

/-- **The main theorem of Pillar A**: the semantic ICAH statement holds under
    `¬CH` alone.  Audit (locked in `ICAH.Main`): kernel axioms only —
    `[propext, Classical.choice, Quot.sound]`. -/
theorem icahElementary (h : NotCH) : ICAHElementary where
  band_nonempty := exists_intermediate_cardinal h
  strata_exist := fun _ h0 hc => exists_elementary_substratum h0.le hc.le
  elementary_chain := by
    obtain ⟨S, hS⟩ := exists_elementary_substratum
      aleph0_lt_aleph_one.le aleph_one_le_continuum
    refine ⟨constElemChain S, fun n => ?_, constElemChain_directLim_equiv S⟩
    have hobj : #((constElemChain S).obj n) = aleph 1 := hS
    rw [hobj]
    exact ⟨aleph0_lt_aleph_one, aleph_one_lt_continuum_of_notCH h⟩
  chain_closure := fun C hC => C.directLimit_card_lt_continuum hC
  cofinal := by
    intro x
    obtain ⟨S, hxS, hS⟩ := exists_elementary_substratum_extending {x}
      (by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_lt_aleph0.le.trans aleph0_lt_aleph_one.le)
      aleph0_lt_aleph_one.le aleph_one_le_continuum
    exact ⟨S, by rw [hS]; exact aleph0_lt_aleph_one,
      by rw [hS]; exact aleph_one_lt_continuum_of_notCH h,
      hxS (Set.mem_singleton x)⟩

end ICAH
