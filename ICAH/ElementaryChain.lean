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
3. `losDirectLimit` — `F_ω ≅[LOR] ℝ` (proved via `DirectLimit.lift` + Tarski–Vaught).
4. `directLimit_card` — `#F_ω = continuum` given the chain hypotheses.

### A note on M6 and König's theorem

For a ℕ-indexed chain the hypothesis `⨆ n, #(obj n) = 𝔠` together with
`∀ n, #(obj n) < 𝔠` is unsatisfiable: `cof 𝔠 > ℵ₀` (König), so a countable
supremum of cardinals `< 𝔠` is `< 𝔠`.  `directLimit_card` is therefore an
honest conditional theorem but vacuous over ℕ.  The non-vacuous form of M6
is `ICAH.CofinalFamily`: a `𝔠.ord`-indexed nested family of intermediate-size
real-closed subfields covering all of ℝ.
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

/-- **Łoś / Tarski–Vaught for the direct limit** (formerly a named axiom):
    the direct limit of an elementary chain is elementarily equivalent to ℝ,
    given compatible elementary embeddings of each level into ℝ.

    Proof: `Language.DirectLimit.lift` assembles the level embeddings into
    `F : DirectLim C ↪[LOR] ℝ`; the Tarski–Vaught test
    (`Embedding.toElementaryEmbedding`) shows `F` is elementary, because any
    existential witness in ℝ over a tuple from `DirectLim C` can be reflected
    into the level `C.obj i` where the (finitely many) tuple entries live,
    by elementarity of `hEmb i`. -/
theorem losDirectLimit (C : ElemChain)
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

/-- The direct limit has cardinality `continuum`, given that the supremum of level
    cardinalities is `continuum`.

    **Proof**: `DirectLim C` is a quotient of `Σ n, C.obj n`, so
    `#(DirectLim C) ≤ #(Σ n, C.obj n) = sum (fun n => #(C.obj n)) ≤ ℵ₀ · ⨆ n, #(C.obj n) = 𝔠`.
    The lower bound follows from the embeddings `C.ofLevel n : C.obj n ↪ DirectLim C`. -/
theorem directLimit_card
    (hCard : ∀ n, Cardinal.mk (C.obj n) < continuum)
    (hSup  : ⨆ n : ℕ, Cardinal.mk (C.obj n) = continuum) :
    Cardinal.mk (DirectLim C) = continuum := by
  apply le_antisymm
  · -- Upper bound: DirectLim is a quotient of Σ n, C.obj n
    have hsurj : Function.Surjective
        (fun p : Σ n : ℕ, C.obj n => (C.ofLevel p.1).toFun p.2) :=
      fun z => DirectLimit.inductionOn z (fun i x => ⟨⟨i, x⟩, rfl⟩)
    have hle1 : #(DirectLim C) ≤ #(Σ n : ℕ, C.obj n) :=
      Cardinal.mk_le_of_surjective hsurj
    have hle2 : #(Σ n : ℕ, C.obj n) ≤ aleph0 * continuum := by
      rw [Cardinal.mk_sigma]
      calc Cardinal.sum (fun n => #(C.obj n))
          ≤ Cardinal.sum (fun _ : ℕ => ⨆ n, #(C.obj n)) :=
            Cardinal.sum_le_sum _ _ (fun i => le_ciSup bddAbove_of_small i)
        _ = aleph0 * ⨆ n, #(C.obj n) := by simp [Cardinal.sum_const]
        _ = aleph0 * continuum := by rw [hSup]
    calc #(DirectLim C) ≤ #(Σ n : ℕ, C.obj n) := hle1
      _ ≤ aleph0 * continuum := hle2
      _ = continuum := by rw [mul_comm]; exact Cardinal.continuum_mul_aleph0
  · -- Lower bound: each level embeds into DirectLim
    rw [← hSup]
    exact ciSup_le (fun n => Cardinal.mk_le_of_injective (C.ofLevel n).injective)

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
