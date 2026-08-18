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
  subfield of ℝ.  First-order real-closedness is immediate: an elementary
  substratum models `Th(ℝ)`, which contains the ring-language axiomatization
  of RCF (`elemSubstratum_models_thReal`).  Native `IsRealClosed` instance
  transfer is not formalized here.
* **Pillar B**: strata are concrete — relative algebraic closures of
  generated subfields, with native `IsRealClosed` instances.  The cost is
  elementarity of those *named algebraic* inclusions, which requires the
  ℝ-specialized real-closed-subfield elementarity consequence of RCF model
  completeness (`RCFModelComplete`).  Pillar B is the conditional pillar.

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

/-- An elementary substratum of `ℝ` satisfies every sentence true in `ℝ`.
    In particular it models `Th(ℝ)`, which contains the first-order
    axiomatization of real-closed fields in the ring language (ring axioms,
    every nonnegative is a square, odd-degree polynomials have roots).
    Native `IsRealClosed` instance transfer along this observation is not
    formalized here; that is a packaging gap, not a first-order gap. -/
theorem elemSubstratum_models_thReal (S : LOR.ElementarySubstructure ℝ)
    (φ : LOR.Sentence) (hφ : ℝ ⊨ φ) : S ⊨ φ :=
  (S.subtype.map_sentence φ).mpr hφ

/-! ### Nesting: elementary substructures of a common model form an elementary pair -/

/-- If `S ⊆ T` are both elementary substructures of a common model `M`, then
    the inclusion `S → T` is elementary: satisfaction in `S` and in `T` both
    reduce to satisfaction in `M`. -/
noncomputable def elementaryInclusion {M : Type*} [LOR.Structure M]
    {S T : LOR.ElementarySubstructure M} (hST : S ≤ T) :
    S ↪ₑ[LOR] T where
  toFun := Substructure.inclusion (show (S : LOR.Substructure M) ≤ T from hST)
  map_formula' := fun {n} φ x => by
    let ιST : (S : LOR.Substructure M) ≤ T := hST
    have hS := S.subtype.map_formula φ x
    have hT := T.subtype.map_formula φ (Substructure.inclusion ιST ∘ x)
    change φ.Realize (Substructure.inclusion ιST ∘ x) ↔ φ.Realize x
    rw [← hT]
    exact hS

/-- The inclusion of nested elementary substrata of `ℝ` is compatible with the
    canonical embeddings into `ℝ`. -/
lemma subtype_comp_elementaryInclusion {S T : LOR.ElementarySubstructure ℝ}
    (hST : S ≤ T) (x : S) :
    T.subtype (elementaryInclusion hST x) = S.subtype x :=
  rfl

/-! ### Directed unions of elementary substrata are elementary -/

/-- A monotone family along a linear order is directed. -/
lemma monotone_directed {ι : Type*} [LinearOrder ι]
    (S : ι → LOR.ElementarySubstructure ℝ) (hmono : Monotone S) :
    Directed (· ≤ ·) S :=
  fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩

/-- Realization of an `Empty`-free formula does not depend on the empty assignment. -/
lemma realize_empty_congr {M : Type*} [LOR.Structure M] {k : ℕ}
    (ψ : LOR.BoundedFormula Empty k) (v w : Empty → M) (xs : Fin k → M) :
    ψ.Realize v xs → ψ.Realize w xs := by
  intro h
  rwa [Subsingleton.elim w v]

/-- Tarski–Vaught witness for a directed union of elementary substrata of `ℝ`:
    parameters from the union live in some common member, which is `≺ ℝ`. -/
lemma directed_iSup_tarskiVaught {ι : Type*} [Nonempty ι]
    (S : ι → LOR.ElementarySubstructure ℝ)
    (hdir : Directed (· ≤ ·) S)
    {n : ℕ} (φ : LOR.BoundedFormula Empty (n + 1))
    (x : Fin n → ↥(⨆ i, (S i : LOR.Substructure ℝ))) (a : ℝ)
    (ha : φ.Realize default (Fin.snoc (fun k => (x k : ℝ)) a)) :
    ∃ b : ↥(⨆ i, (S i : LOR.Substructure ℝ)),
      φ.Realize default (Fin.snoc (fun k => (x k : ℝ)) (b : ℝ)) := by
  classical
  have hdir' : Directed (· ≤ ·) (fun i => (S i : LOR.Substructure ℝ)) :=
    hdir.mono fun _ _ h => h
  have mem : ∀ k : Fin n, ∃ i, (x k : ℝ) ∈ S i := fun k =>
    (Substructure.mem_iSup_of_directed hdir').1 (x k).2
  let idx : Fin n → ι := fun k => (mem k).choose
  obtain ⟨j, hj⟩ := hdir.finite_le idx
  have hxj : ∀ k, (x k : ℝ) ∈ S j := fun k =>
    hj k (mem k).choose_spec
  let y : Fin n → S j := fun k => ⟨x k, hxj k⟩
  have hexR : φ.ex.Realize ((S j).subtype ∘ (default : Empty → S j))
      ((S j).subtype ∘ y) :=
    BoundedFormula.realize_ex.mpr ⟨a, realize_empty_congr _ _ _ _ ha⟩
  have hexS : φ.ex.Realize (default : Empty → S j) y :=
    ((S j).subtype.map_boundedFormula φ.ex default y).mp hexR
  obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.mp hexS
  refine ⟨⟨(b : ℝ), (le_iSup (fun i => (S i : LOR.Substructure ℝ)) j) b.2⟩, ?_⟩
  have hpush := ((S j).subtype.map_boundedFormula φ default (Fin.snoc y b)).mpr hb
  rw [Fin.comp_snoc] at hpush
  exact realize_empty_congr _ _ _ _ hpush

/-- **Tarski–Vaught for directed unions**: the directed supremum of a nonempty
    family of elementary substructures of `ℝ` is again elementary in `ℝ`. -/
theorem directed_iSup_isElementary {ι : Type*} [Nonempty ι]
    (S : ι → LOR.ElementarySubstructure ℝ)
    (hdir : Directed (· ≤ ·) S) :
    (⨆ i, (S i : LOR.Substructure ℝ)).IsElementary :=
  Substructure.isElementary_of_exists _ (fun n φ x a ha => by
    obtain ⟨b, hb⟩ := directed_iSup_tarskiVaught S hdir φ x a
      (realize_empty_congr _ _ _ _ ha)
    exact ⟨b, realize_empty_congr _ _ _ _ hb⟩)

/-- The directed union of a nonempty family of elementary substructures of `ℝ`,
    bundled as an elementary substructure. -/
noncomputable def directedISupElem {ι : Type*} [Nonempty ι]
    (S : ι → LOR.ElementarySubstructure ℝ)
    (hdir : Directed (· ≤ ·) S) :
    LOR.ElementarySubstructure ℝ :=
  (⨆ i, (S i : LOR.Substructure ℝ)).toElementarySubstructure
    (fun n φ x a ha => by
      obtain ⟨b, hb⟩ := directed_iSup_tarskiVaught S hdir φ x a
        (realize_empty_congr _ _ _ _ ha)
      exact ⟨b, realize_empty_congr _ _ _ _ hb⟩)

/-- Carrier of the directed union is the set-theoretic union. -/
lemma coe_directedISupElem {ι : Type*} [Nonempty ι]
    (S : ι → LOR.ElementarySubstructure ℝ)
    (hdir : Directed (· ≤ ·) S) :
    (directedISupElem S hdir : Set ℝ) = ⋃ i, (S i : Set ℝ) := by
  ext x
  have hdir' : Directed (· ≤ ·) (fun i => (S i : LOR.Substructure ℝ)) :=
    hdir.mono fun _ _ h => h
  simp only [directedISupElem, Substructure.toElementarySubstructure,
    SetLike.mem_coe, Set.mem_iUnion]
  exact Substructure.mem_iSup_of_directed hdir'

/-- Specialization: the union of a nonempty monotone chain of elementary
    substructures of `ℝ` is an elementary substructure of `ℝ`. -/
noncomputable def iUnionChainElem {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (S : ι → LOR.ElementarySubstructure ℝ) (hmono : Monotone S) :
    LOR.ElementarySubstructure ℝ :=
  directedISupElem S (monotone_directed S hmono)

/-! ### Strictly increasing ℕ-indexed elementary chain -/

/-- An elementary substratum of `ℝ` of cardinality exactly `ℵ₁`. -/
structure AlephOneElem where
  /-- The underlying elementary substructure. -/
  S : LOR.ElementarySubstructure ℝ
  /-- Cardinality pin. -/
  card : #S = aleph 1

lemma AlephOneElem.lt_continuum (R : AlephOneElem) (h : NotCH) :
    #R.S < continuum := by
  rw [R.card]
  exact aleph_one_lt_continuum_of_notCH h

/-- A real lying outside an `ℵ₁`-sized elementary substratum. -/
noncomputable def AlephOneElem.fresh (h : NotCH) (R : AlephOneElem) : ℝ :=
  (exists_real_not_mem (R.S : Set ℝ) (R.lt_continuum h)).choose

lemma AlephOneElem.fresh_not_mem (h : NotCH) (R : AlephOneElem) :
    R.fresh h ∉ R.S :=
  (exists_real_not_mem (R.S : Set ℝ) (R.lt_continuum h)).choose_spec

/-- Seed set for the successor: the previous carrier plus one fresh real. -/
noncomputable def AlephOneElem.succSeed (h : NotCH) (R : AlephOneElem) : Set ℝ :=
  (R.S : Set ℝ) ∪ {R.fresh h}

lemma AlephOneElem.mk_succSeed (h : NotCH) (R : AlephOneElem) :
    #(R.succSeed h) = aleph 1 :=
  mk_union_singleton_aleph1 R.card _

/-- Successor: DLS applied to `S ∪ {x}` at cardinality `ℵ₁`. -/
noncomputable def AlephOneElem.succ (h : NotCH) (R : AlephOneElem) : AlephOneElem :=
  ⟨(exists_elementary_substratum_extending (R.succSeed h)
      (by rw [R.mk_succSeed h])
      aleph0_lt_aleph_one.le aleph_one_le_continuum).choose,
   (exists_elementary_substratum_extending (R.succSeed h)
      (by rw [R.mk_succSeed h])
      aleph0_lt_aleph_one.le aleph_one_le_continuum).choose_spec.2⟩

lemma AlephOneElem.subset_succ (h : NotCH) (R : AlephOneElem) :
    (R.S : Set ℝ) ⊆ (R.succ h).S :=
  (exists_elementary_substratum_extending (R.succSeed h)
      (by rw [R.mk_succSeed h])
      aleph0_lt_aleph_one.le aleph_one_le_continuum).choose_spec.1.trans'
    Set.subset_union_left

lemma AlephOneElem.le_succ (h : NotCH) (R : AlephOneElem) :
    R.S ≤ (R.succ h).S :=
  R.subset_succ h

lemma AlephOneElem.fresh_mem_succ (h : NotCH) (R : AlephOneElem) :
    R.fresh h ∈ (R.succ h).S :=
  (exists_elementary_substratum_extending (R.succSeed h)
      (by rw [R.mk_succSeed h])
      aleph0_lt_aleph_one.le aleph_one_le_continuum).choose_spec.1
    (Or.inr (Set.mem_singleton _))

/-- The `ℵ₁`-sized elementary chain, starting from any DLS substratum of
    size `ℵ₁` and strictly extending at each successor. -/
noncomputable def alephOneElemSeq (h : NotCH) : ℕ → AlephOneElem
  | 0 =>
    ⟨(exists_elementary_substratum
        aleph0_lt_aleph_one.le aleph_one_le_continuum).choose,
     (exists_elementary_substratum
        aleph0_lt_aleph_one.le aleph_one_le_continuum).choose_spec⟩
  | n + 1 => (alephOneElemSeq h n).succ h

/-- **Strictly increasing `ℕ`-indexed elementary chain** of intermediate-size
    substrata of `ℝ`.  Successor maps are the nesting inclusions
    `elementaryInclusion`; each step adjoins a fresh real via DLS. -/
noncomputable def strictElemChain (h : NotCH) : ElemChain where
  obj := fun n => (alephOneElemSeq h n).S
  str := fun _ => inferInstance
  emb := fun n => elementaryInclusion ((alephOneElemSeq h n).le_succ h)

lemma strictElemChain_card (h : NotCH) (n : ℕ) :
    #((strictElemChain h).obj n) = aleph 1 :=
  (alephOneElemSeq h n).card

lemma strictElemChain_intermediate (h : NotCH) (n : ℕ) :
    aleph0 < #((strictElemChain h).obj n) ∧
      #((strictElemChain h).obj n) < continuum := by
  rw [strictElemChain_card h n]
  exact ⟨aleph0_lt_aleph_one, aleph_one_lt_continuum_of_notCH h⟩

/-- The successor embedding is a proper inclusion: the fresh real at stage `n`
    is in level `n+1` but not in the image of level `n`. -/
lemma strictElemChain_strict (h : NotCH) (n : ℕ) :
    ∃ x : (strictElemChain h).obj (n + 1),
      ∀ y : (strictElemChain h).obj n, (strictElemChain h).emb n y ≠ x := by
  refine ⟨⟨(alephOneElemSeq h n).fresh h,
      (alephOneElemSeq h n).fresh_mem_succ h⟩, ?_⟩
  change ∀ y : (alephOneElemSeq h n).S,
      elementaryInclusion ((alephOneElemSeq h n).le_succ h) y ≠
        ⟨(alephOneElemSeq h n).fresh h, (alephOneElemSeq h n).fresh_mem_succ h⟩
  intro y hxy
  apply (alephOneElemSeq h n).fresh_not_mem h
  have : (y : ℝ) = (alephOneElemSeq h n).fresh h :=
    congrArg Subtype.val hxy
  exact this ▸ y.2

/-- The direct limit of the strictly increasing chain is elementarily
    equivalent to `ℝ`, via the canonical elementary inclusions into `ℝ`. -/
theorem strictElemChain_directLim_equiv (h : NotCH) :
    (strictElemChain h).DirectLim ≅[LOR] ℝ :=
  ElemChain.tarskiVaughtDirectLimit (strictElemChain h)
    (fun n => (alephOneElemSeq h n).S.subtype)
    (fun _ _ => rfl)

/-! ### Constant elementary chains on a substratum (kept as a test object) -/

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
  /-- There is a *strictly increasing* elementary chain of intermediate-size
      strata whose direct limit is elementarily equivalent to ℝ. -/
  elementary_chain : ∃ C : ElemChain.{0},
    (∀ n, aleph0 < #(C.obj n) ∧ #(C.obj n) < continuum) ∧
    (∀ n, ∃ x : C.obj (n + 1), ∀ y : C.obj n, C.emb n y ≠ x) ∧
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
  elementary_chain :=
    ⟨strictElemChain h, strictElemChain_intermediate h,
      strictElemChain_strict h, strictElemChain_directLim_equiv h⟩
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

/-- Descriptive name of `icahElementary` for Mathlib-facing discussion.
    The `icahElementary` identifier is retained for repository continuity. -/
theorem elementaryStrata (h : NotCH) : ICAHElementary :=
  icahElementary h

end ICAH
