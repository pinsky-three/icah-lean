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
3. `directLimit_elementarilyEquiv_real` — `F_ω ≅[LOR] ℝ` (sorry-stub).
4. `directLimit_card` — `#F_ω = continuum` (sorry-stub).

### Status

Infrastructure compiles.  Theorems 3–4 are `sorry`-stubs pending:
- A Łoś/Tarski–Vaught theorem for direct limits of elementary embeddings
  (not yet in Mathlib).
- Cardinal arithmetic for the colimit size.
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

/-! ### Key theorems (M5 deliverables) -/

/-- The direct limit of an elementary chain is elementarily equivalent to ℝ,
    given compatible elementary embeddings of each level into ℝ.

    **Proof sketch**: By the Tarski–Vaught criterion, the union of an elementary
    chain is an elementary substructure of any ambient model.  The colimit
    inherits elementarity from the chain.

    Blocked on: a Łoś/Tarski–Vaught theorem for `Language.DirectLimit` of
    elementary embeddings, not yet in Mathlib. -/
theorem directLimit_elementarilyEquiv_real
    (hEmb    : ∀ n, C.obj n ↪ₑ[LOR] ℝ)
    (hCompat : ∀ n x, hEmb (n + 1) (C.emb n x) = hEmb n x) :
    DirectLim C ≅[LOR] ℝ := by
  sorry

/-- The direct limit has cardinality `continuum`, given that each level has
    intermediate cardinality and the supremum of level cardinalities is `continuum`.

    **Proof sketch**: `#F_ω = ⨆ n, #(F n)`.  The hypothesis `hSup` asserts
    this sup equals `continuum`.

    Blocked on: cardinal arithmetic for `Language.DirectLimit`. -/
theorem directLimit_card
    (hCard : ∀ n, Cardinal.mk (C.obj n) < continuum)
    (hSup  : ⨆ n : ℕ, Cardinal.mk (C.obj n) = continuum) :
    Cardinal.mk (DirectLim C) = continuum := by
  sorry

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
