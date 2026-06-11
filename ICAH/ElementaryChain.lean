import Mathlib
import ICAH.Definability
import ICAH.Strata

/-!
## Elementary chain and limit field (M5)

A `ℕ`-indexed chain of `LOR`-structures connected by elementary embeddings,
together with its direct limit `F_ω`.

### Architecture

We use Mathlib's `DirectedSystem.natLERec` to build the directed system from
the successor embeddings, and `Language.DirectLimit` for the colimit.

The elementary embeddings `obj n ↪ₑ[LOR] obj (n+1)` are stored separately;
the directed system is built from their underlying `Embedding` coercions.

### Key results (deliverables)

1. `ElemChain.embLE`  — compose successor elem-embeddings: `obj m ↪ₑ[LOR] obj n`.
2. `ElemChain.DirectLim` — the `Language.DirectLimit` colimit type.
3. `tarskiVaughtDirectLimit` — `F_ω ≅[LOR] ℝ` (proved via `DirectLimit.lift` +
   the Tarski–Vaught test).  This is the Tarski–Vaught elementary chain theorem
   relativized to the ambient model ℝ — *not* Łoś's theorem, which concerns
   ultraproducts; the former name `losDirectLimit` was a misattribution.
4. `directLimit_card_eq_iSup` — `#F_ω = ⨆ n, #(obj n)` (the honest cardinality
   identity).
5. `directLimit_card_lt_continuum` — closure: a countable chain of strata of
   size `< 𝔠` has direct limit of size `< 𝔠` (König: `cof 𝔠 > ℵ₀`).

### A note on M6 and König's theorem

A former version of this file stated `directLimit_card`: *if* every level has
size `< 𝔠` *and* the level cardinalities have supremum `𝔠`, *then* the limit
has size `𝔠`.  Those hypotheses are jointly unsatisfiable (`cof 𝔠 > ℵ₀` by
König, so a countable supremum of cardinals `< 𝔠` stays `< 𝔠`), making the
theorem vacuously true.  It has been replaced by the non-vacuous pair above:
the supremum identity `directLimit_card_eq_iSup`, and the closure theorem
`directLimit_card_lt_continuum` showing that ℕ-indexed chains can *never*
escape the stratum hierarchy.  The continuum is attained only by families of
uncountable cofinality — see `ICAH.CofinalFamily`.
-/

namespace ICAH

open FirstOrder FirstOrder.Language FirstOrder.Ring Cardinal Set

/-! ### Elementary chain -/

/-- A `ℕ`-indexed sequence of `LOR`-structures connected by elementary embeddings. -/
structure ElemChain where
  obj  : ℕ → Type*
  [str : ∀ n, LOR.Structure (obj n)]
  emb  : ∀ n, obj n ↪ₑ[LOR] obj (n + 1)

attribute [instance] ElemChain.str

namespace ElemChain

variable (C : ElemChain)

/-- The underlying first-order embeddings (forgetting elementarity). -/
noncomputable def embSucc (n : ℕ) : C.obj n ↪[LOR] C.obj (n + 1) :=
  (C.emb n).toEmbedding

/-- The directed system of embeddings, built by `natLERec` from the successor maps. -/
noncomputable def sysEmb (m n : ℕ) (h : m ≤ n) : C.obj m ↪[LOR] C.obj n :=
  DirectedSystem.natLERec C.embSucc m n h

/-- `sysEmb` forms a `DirectedSystem`. -/
instance : DirectedSystem C.obj (fun i j h => C.sysEmb i j h) :=
  DirectedSystem.natLERec.directedSystem C.embSucc

/-- Compose successor elementary embeddings: `obj m ↪ₑ[LOR] obj n` for `m ≤ n`.
    Built via `Nat.leRecOn`, mirroring `natLERec` but preserving elementarity. -/
noncomputable def embLE {m : ℕ} : ∀ {n : ℕ}, m ≤ n → C.obj m ↪ₑ[LOR] C.obj n :=
  fun {_} h => Nat.leRecOn h (fun {k} e => (C.emb k).comp e) (ElementaryEmbedding.refl LOR _)

/-- `embLE` and `sysEmb` agree as functions. -/
lemma embLE_eq_sysEmb {m n : ℕ} (h : m ≤ n) :
    (C.embLE h : C.obj m → C.obj n) = C.sysEmb m n h := by
  simp only [sysEmb, DirectedSystem.coe_natLERec, embLE]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [Nat.leRecOn_self, embSucc]
  | succ k ih =>
    erw [Nat.leRecOn_succ le_self_add, Nat.leRecOn_succ le_self_add]
    simp [ElementaryEmbedding.comp_apply, embSucc, ih]

/-! ### Direct limit (colimit field F_ω) -/

/-- The direct limit of the chain — the colimit field `F_ω`. -/
noncomputable def DirectLim : Type* :=
  Language.DirectLimit C.obj (fun i j h => C.sysEmb i j h)

noncomputable instance directLimStr : LOR.Structure (DirectLim C) :=
  inferInstanceAs (LOR.Structure (Language.DirectLimit C.obj _))

/-- The canonical embedding of level `n` into the direct limit. -/
noncomputable def ofLevel (n : ℕ) : C.obj n ↪[LOR] DirectLim C :=
  Language.DirectLimit.of LOR ℕ C.obj (fun i j h => C.sysEmb i j h) n

/-! ### Ambient-free Tarski–Vaught: `ofLevel` is elementary

The transition maps of an `ElemChain` are elementary by definition, so the
direct limit is an *elementary* extension of every level — with no ambient
model needed.  Mathlib's `Language.DirectLimit` has no elementarity results,
and the Tarski–Vaught test alone does not suffice here (pulling realization
back through `ofLevel` for arbitrary formulas is exactly what is being
proved), so we do the induction on `BoundedFormula` directly.  The only
interesting case is `all`: a direct-limit witness is pulled down to a level
`m` above both the tuple's level and the witness's level (directedness +
`DirectLimit.of_f`), and the universally quantified hypothesis is pushed from
level `i` to level `m` through the elementary embedding `embLE`. -/

/-- Realization of any bounded formula commutes with `ofLevel`:
    the heart of the ambient-free Tarski–Vaught chain theorem. -/
theorem realize_ofLevel_iff {α : Type*} {k : ℕ} (φ : LOR.BoundedFormula α k) :
    ∀ (i : ℕ) (v : α → C.obj i) (xs : Fin k → C.obj i),
      φ.Realize ((C.ofLevel i) ∘ v) ((C.ofLevel i) ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum =>
    intro i v xs
    simp [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    intro i v xs
    simp only [BoundedFormula.Realize]
    rw [← Sum.comp_elim, HomClass.realize_term, HomClass.realize_term]
    exact (C.ofLevel i).injective.eq_iff
  | rel R ts =>
    -- The ring language has no relation symbols.
    exact Empty.elim R
  | imp φ ψ ihφ ihψ =>
    intro i v xs
    simp only [BoundedFormula.realize_imp, ihφ i v xs, ihψ i v xs]
  | all φ ih =>
    intro i v xs
    simp only [BoundedFormula.realize_all]
    constructor
    · -- Downward: instantiate the limit-side ∀ at images of level-i elements.
      intro h b
      have hb := h (C.ofLevel i b)
      rw [← Fin.comp_snoc] at hb
      exact (ih i v (Fin.snoc xs b)).mp hb
    · -- Upward: pull a limit witness down to a common level m,
      -- and push the level-i hypothesis up to m by elementarity of embLE.
      intro h a
      refine Language.DirectLimit.inductionOn a ?_
      intro j ya
      show φ.Realize ((C.ofLevel i) ∘ v)
        (Fin.snoc ((C.ofLevel i) ∘ xs) (C.ofLevel j ya))
      have him : i ≤ max i j := le_max_left i j
      have hjm : j ≤ max i j := le_max_right i j
      -- Push the universally quantified hypothesis from level i to level m.
      have hall : ∀ c : C.obj (max i j),
          φ.Realize (C.embLE him ∘ v) (Fin.snoc (C.embLE him ∘ xs) c) :=
        BoundedFormula.realize_all.mp
          (((C.embLE him).map_boundedFormula φ.all v xs).mpr
            (BoundedFormula.realize_all.mpr h))
      -- Rewrite all limit elements as images from level m.
      have hov : (C.ofLevel i) ∘ v = (C.ofLevel (max i j)) ∘ (C.embLE him ∘ v) := by
        funext b
        simp only [Function.comp_apply, congrFun (C.embLE_eq_sysEmb him)]
        exact (Language.DirectLimit.of_f (hij := him)).symm
      have hoxs : (C.ofLevel i) ∘ xs =
          (C.ofLevel (max i j)) ∘ (C.embLE him ∘ xs) := by
        funext b
        simp only [Function.comp_apply, congrFun (C.embLE_eq_sysEmb him)]
        exact (Language.DirectLimit.of_f (hij := him)).symm
      have hoya : C.ofLevel j ya = C.ofLevel (max i j) (C.embLE hjm ya) := by
        rw [congrFun (C.embLE_eq_sysEmb hjm)]
        exact (Language.DirectLimit.of_f (hij := hjm)).symm
      rw [hov, hoxs, hoya, ← Fin.comp_snoc]
      exact (ih (max i j) (C.embLE him ∘ v)
        (Fin.snoc (C.embLE him ∘ xs) (C.embLE hjm ya))).mpr
        (hall (C.embLE hjm ya))

/-- **Ambient-free Tarski–Vaught chain theorem**: the canonical embedding of
    each level into the direct limit of an elementary chain is *elementary*.
    Mathlib's `Language.DirectLimit` currently has no elementarity results;
    this is the natural upstreaming target. -/
noncomputable def ofLevelElem (n : ℕ) : C.obj n ↪ₑ[LOR] DirectLim C where
  toFun := C.ofLevel n
  map_formula' := fun {k} φ x => by
    have h := C.realize_ofLevel_iff φ n x (default : Fin 0 → C.obj n)
    rwa [Subsingleton.elim ((C.ofLevel n) ∘ (default : Fin 0 → C.obj n))
      (default : Fin 0 → DirectLim C)] at h

/-- The direct limit of an elementary chain is elementarily equivalent to
    every level — with no ambient model required. -/
theorem directLim_elementarilyEquivalent (n : ℕ) :
    C.obj n ≅[LOR] DirectLim C :=
  (C.ofLevelElem n).elementarilyEquivalent

/-! ### Key theorems (M5 + M6 deliverables) -/

/-- The composite elementary embeddings are compatible with the directed-system maps:
    pushing through `embLE` agrees with the given embeddings into ℝ. -/
lemma hEmb_embLE (hEmb : ∀ n, C.obj n ↪ₑ[LOR] ℝ)
    (hCompat : ∀ n x, hEmb (n + 1) (C.emb n x) = hEmb n x)
    {i j : ℕ} (hij : i ≤ j) (x : C.obj i) :
    hEmb j (C.embLE hij x) = hEmb i x := by
  induction j, hij using Nat.le_induction with
  | base =>
    have h : C.embLE (le_refl i) x = x := by
      simp [ElemChain.embLE, Nat.leRecOn_self]
    rw [h]
  | succ j hij ih =>
    have h : C.embLE (Nat.le_succ_of_le hij) x = (C.emb j) (C.embLE hij x) := by
      simp only [ElemChain.embLE]
      erw [Nat.leRecOn_succ hij]
      rfl
    rw [h, hCompat, ih]

/-- Compatibility through the directed-system maps `sysEmb`. -/
lemma hEmb_sysEmb (hEmb : ∀ n, C.obj n ↪ₑ[LOR] ℝ)
    (hCompat : ∀ n x, hEmb (n + 1) (C.emb n x) = hEmb n x)
    (i j : ℕ) (hij : i ≤ j) (x : C.obj i) :
    hEmb j (C.sysEmb i j hij x) = hEmb i x := by
  rw [← congrFun (C.embLE_eq_sysEmb hij) x]
  exact C.hEmb_embLE hEmb hCompat hij x

/-- **Tarski–Vaught elementary chain theorem, relativized to ℝ** (formerly a
    named axiom, and formerly misnamed `losDirectLimit` — Łoś's theorem is
    about ultraproducts): the direct limit of an elementary chain is
    elementarily equivalent to ℝ, given compatible elementary embeddings of
    each level into ℝ.

    Proof: `Language.DirectLimit.lift` assembles the level embeddings into
    `F : DirectLim C ↪[LOR] ℝ`; the Tarski–Vaught test
    (`Embedding.toElementaryEmbedding`) shows `F` is elementary, because any
    existential witness in ℝ over a tuple from `DirectLim C` can be reflected
    into the level `C.obj i` where the (finitely many) tuple entries live,
    by elementarity of `hEmb i`. -/
theorem tarskiVaughtDirectLimit (C : ElemChain)
    (hEmb    : ∀ n, C.obj n ↪ₑ[LOR] ℝ)
    (hCompat : ∀ n x, hEmb (n + 1) (C.emb n x) = hEmb n x) :
    DirectLim C ≅[LOR] ℝ := by
  classical
  -- Assemble the level embeddings into an embedding of the direct limit.
  let g : ∀ n, C.obj n ↪[LOR] ℝ := fun n => (hEmb n).toEmbedding
  have Hg : ∀ i j hij x, g j (C.sysEmb i j hij x) = g i x := fun i j hij x =>
    C.hEmb_sysEmb hEmb hCompat i j hij x
  let F : DirectLim C ↪[LOR] ℝ :=
    Language.DirectLimit.lift LOR ℕ C.obj (fun i j h => C.sysEmb i j h) g Hg
  have hF : ∀ (i : ℕ) (x : C.obj i), F (C.ofLevel i x) = hEmb i x := by
    intro i x
    show Language.DirectLimit.lift LOR ℕ C.obj (fun i j h => C.sysEmb i j h) g Hg
      (Language.DirectLimit.of LOR ℕ C.obj (fun i j h => C.sysEmb i j h) i x) = hEmb i x
    rw [Language.DirectLimit.lift_of]
    rfl
  -- Tarski–Vaught test.
  refine (F.toElementaryEmbedding ?_).elementarilyEquivalent
  -- `Empty → M` is a subsingleton, so realization is independent of the
  -- free-variable assignment (the `default` terms below differ by instance path).
  have realize_congr : ∀ {M : Type _} [LOR.Structure M] {k : ℕ}
      (ψ : LOR.BoundedFormula Empty k) (v w : Empty → M) (xs : Fin k → M),
      ψ.Realize v xs → ψ.Realize w xs := by
    intro M _ k ψ v w xs h
    rwa [Subsingleton.elim w v]
  intro n φ x a ha
  -- The tuple x comes from a single level i.
  obtain ⟨i, y, rfl⟩ := Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    C.obj (fun i j h => C.sysEmb i j h) x
  have hFx : F ∘ (fun a => (⟦Structure.Sigma.mk (fun i j h => C.sysEmb i j h) i (y a)⟧ :
      DirectLim C)) = (hEmb i : C.obj i → ℝ) ∘ y := by
    funext b
    simp only [Function.comp_apply]
    exact hF i (y b)
  rw [hFx] at ha
  -- ℝ realizes the existential at the image of y; pull it back to level i.
  have hex : φ.ex.Realize ((hEmb i : C.obj i → ℝ) ∘ (default : Empty → C.obj i))
      ((hEmb i : C.obj i → ℝ) ∘ y) :=
    BoundedFormula.realize_ex.mpr ⟨a, realize_congr _ _ _ _ ha⟩
  have hexi : φ.ex.Realize (default : Empty → C.obj i) y :=
    ((hEmb i).map_boundedFormula φ.ex (default : Empty → C.obj i) y).mp hex
  obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.mp hexi
  -- Push the witness forward into the direct limit.
  refine ⟨C.ofLevel i b, ?_⟩
  have hpush := ((hEmb i).map_boundedFormula φ (default : Empty → C.obj i)
    (Fin.snoc y b)).mpr hb
  rw [Fin.comp_snoc] at hpush
  rw [hFx, hF]
  exact realize_congr _ _ _ _ hpush

/-- The direct limit of the chain has size at most `ℵ₀ · ⨆ n, #(obj n)`:
    it is a quotient of the sigma type `Σ n, C.obj n`. -/
lemma directLimit_card_le :
    Cardinal.mk (DirectLim C) ≤ aleph0 * ⨆ n : ℕ, Cardinal.mk (C.obj n) := by
  have hsurj : Function.Surjective
      (fun p : Σ n : ℕ, C.obj n => (C.ofLevel p.1).toFun p.2) :=
    fun z => DirectLimit.inductionOn z (fun i x => ⟨⟨i, x⟩, rfl⟩)
  calc #(DirectLim C)
      ≤ #(Σ n : ℕ, C.obj n) := Cardinal.mk_le_of_surjective hsurj
    _ ≤ aleph0 * ⨆ n, #(C.obj n) := by
        rw [Cardinal.mk_sigma]
        calc Cardinal.sum (fun n => #(C.obj n))
            ≤ Cardinal.sum (fun _ : ℕ => ⨆ n, #(C.obj n)) :=
              Cardinal.sum_le_sum _ _ (fun i => le_ciSup bddAbove_of_small i)
          _ = aleph0 * ⨆ n, #(C.obj n) := by simp [Cardinal.sum_const]

/-- **Cardinality of the direct limit** (the honest, non-vacuous identity):
    for an infinite chain, `#(DirectLim C) = ⨆ n, #(obj n)`.

    A former version (`directLimit_card`) instead assumed `∀ n, #(obj n) < 𝔠`
    and `⨆ n, #(obj n) = 𝔠` — jointly unsatisfiable by König (`cof 𝔠 > ℵ₀`),
    hence vacuous.  This statement is the contentful replacement.

    **Proof**: upper bound — `DirectLim C` is a quotient of `Σ n, C.obj n`, so
    `#(DirectLim C) ≤ ℵ₀ · ⨆ n, #(obj n) = ⨆ n, #(obj n)`.
    Lower bound — every level embeds via `C.ofLevel n`. -/
theorem directLimit_card_eq_iSup
    (hSup : aleph0 ≤ ⨆ n : ℕ, Cardinal.mk (C.obj n)) :
    Cardinal.mk (DirectLim C) = ⨆ n : ℕ, Cardinal.mk (C.obj n) := by
  apply le_antisymm
  · calc #(DirectLim C)
        ≤ aleph0 * ⨆ n, #(C.obj n) := C.directLimit_card_le
      _ = ⨆ n, #(C.obj n) := Cardinal.mul_eq_right hSup hSup aleph0_ne_zero
  · exact ciSup_le (fun n => Cardinal.mk_le_of_injective (C.ofLevel n).injective)

/-- **Closure of the stratum hierarchy under countable chains** (König):
    if every level has size `< 𝔠`, so does the direct limit.  A ℕ-indexed
    chain of intermediate strata can never exhaust ℝ; only families of
    uncountable cofinality can (see `ICAH.CofinalFamily`). -/
theorem directLimit_card_lt_continuum
    (hCard : ∀ n, Cardinal.mk (C.obj n) < continuum) :
    Cardinal.mk (DirectLim C) < continuum := by
  have hsup : (⨆ n : ℕ, Cardinal.mk (C.obj n)) < continuum := by
    apply Cardinal.lift_iSup_lt_of_lt_cof_ord _ hCard
    rw [Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_continuum]
    exact aleph0_lt_cof_ord_continuum
  calc #(DirectLim C)
      ≤ aleph0 * ⨆ n, #(C.obj n) := C.directLimit_card_le
    _ < continuum := Cardinal.mul_lt_of_lt aleph0_le_continuum
        aleph0_lt_continuum hsup

/-- The direct limit of a chain of intermediate strata is itself of
    intermediate size: the hierarchy is closed under countable elementary
    chains. -/
theorem directLimit_intermediate
    (h0 : aleph0 < Cardinal.mk (C.obj 0))
    (hCard : ∀ n, Cardinal.mk (C.obj n) < continuum) :
    aleph0 < Cardinal.mk (DirectLim C) ∧ Cardinal.mk (DirectLim C) < continuum :=
  ⟨h0.trans_le (Cardinal.mk_le_of_injective (C.ofLevel 0).injective),
   C.directLimit_card_lt_continuum hCard⟩

end ElemChain

/-! ### Stratum chain -/

/-- A chain of strata with elementary embeddings between their carrier fields. -/
structure StratumChain where
  strata  : ℕ → Stratum
  [strStr : ∀ n, LOR.Structure (strata n).carrier]
  embSucc : ∀ n, (strata n).carrier ↪ₑ[LOR] (strata (n + 1)).carrier

attribute [instance] StratumChain.strStr

/-- Extract the underlying `ElemChain` from a `StratumChain`. -/
def StratumChain.toElemChain (SC : StratumChain) : ElemChain where
  obj := fun n => (SC.strata n).carrier
  emb := SC.embSucc

end ICAH
