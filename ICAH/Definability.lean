import Mathlib
import ICAH.SizeAwareField

/-!
## Definability interface (M2)

First-order definability of relations and functions on subtypes of ℝ, using
the ring language `FirstOrder.Language.ring`.

### Design

We use `Set.Definable` from `Mathlib.ModelTheory.Definability`:
  `A.Definable L s` — set `s : Set (α → M)` is definable with parameters from
  `A : Set M` in language `L`.

For ICAH we specialise to `M := ℝ`, `L := Language.ring`, `A := S` (a stratum).

`ℝ` does not automatically carry a `Language.ring.Structure` instance; we
register one via `compatibleRingOfRing` (which is `@[instance_reducible]` in
Mathlib and therefore not picked up by default synthesis).

### Status

Closure lemmas are proved by direct delegation to the corresponding
`Set.Definable` lemmas.  `ElemEmb` wraps `FirstOrder.Language.ElementaryEmbedding`.
-/

namespace ICAH

open FirstOrder FirstOrder.Language FirstOrder.Ring Set

/-! ### Language -/

/-- The language of rings used throughout ICAH. -/
abbrev LOR : Language := Language.ring

/-! ### Structure instance for ℝ

`compatibleRingOfRing` builds a `CompatibleRing` (hence `Language.ring.Structure`)
from the bare ring operations.  We register it as a global instance so that
`Set.Definable LOR` type-checks with `M := ℝ`.
-/
noncomputable instance : CompatibleRing ℝ := compatibleRingOfRing ℝ

/-! ### Definability predicate -/

/-- A `k`-ary relation on ℝ is first-order definable in `LOR` with parameters
    drawn from `S`. -/
def DefinableOn (S : Set ℝ) (k : ℕ) (r : Set (Fin k → ℝ)) : Prop :=
  S.Definable LOR r

/-- Unary variant: a subset of ℝ is definable with parameters from `S`. -/
def DefinableOn₁ (S : Set ℝ) (s : Set ℝ) : Prop :=
  S.Definable₁ LOR s

/-- Binary variant: a binary relation on ℝ is definable with parameters from `S`. -/
def DefinableOn₂ (S : Set ℝ) (r : Set (ℝ × ℝ)) : Prop :=
  S.Definable₂ LOR r

/-! ### Closure lemmas

Each lemma delegates to the corresponding `Set.Definable` lemma.  We use
`show` to make the unfolding explicit and avoid name-clash recursion.
-/

lemma definableOn_inter {S : Set ℝ} {k : ℕ} {r₁ r₂ : Set (Fin k → ℝ)}
    (h₁ : DefinableOn S k r₁) (h₂ : DefinableOn S k r₂) :
    DefinableOn S k (r₁ ∩ r₂) :=
  show S.Definable LOR _ from h₁.inter h₂

lemma definableOn_union {S : Set ℝ} {k : ℕ} {r₁ r₂ : Set (Fin k → ℝ)}
    (h₁ : DefinableOn S k r₁) (h₂ : DefinableOn S k r₂) :
    DefinableOn S k (r₁ ∪ r₂) :=
  show S.Definable LOR _ from h₁.union h₂

lemma definableOn_compl {S : Set ℝ} {k : ℕ} {r : Set (Fin k → ℝ)}
    (h : DefinableOn S k r) :
    DefinableOn S k rᶜ :=
  show S.Definable LOR _ from h.compl

lemma definableOn_mono {S T : Set ℝ} {k : ℕ} {r : Set (Fin k → ℝ)}
    (h : DefinableOn S k r) (hST : S ⊆ T) :
    DefinableOn T k r :=
  show T.Definable LOR _ from h.mono hST

/-- Definable sets are closed under finite projections (existential quantification). -/
lemma definableOn_image_comp {S : Set ℝ} {k m : ℕ} {r : Set (Fin k → ℝ)}
    (h : DefinableOn S k r) (f : Fin m → Fin k) :
    DefinableOn S m (r.image (· ∘ f)) :=
  show S.Definable LOR _ from h.image_comp f

/-! ### Graph definability for binary operations -/

/-- The graph of a binary operation `op` restricted to `S` is definable with
    parameters from `S`. -/
def GraphDefinable (S : Set ℝ) (op : ℝ → ℝ → ℝ) : Prop :=
  DefinableOn₂ S {p : ℝ × ℝ | ∃ z ∈ S, op p.1 p.2 = z}

/-! ### Elementary embedding wrapper -/

/-- An elementary embedding between two `LOR`-structures, wrapping
    `FirstOrder.Language.ElementaryEmbedding`. -/
abbrev ElemEmb (A B : Type*) [LOR.Structure A] [LOR.Structure B] :=
  A ↪ₑ[LOR] B

end ICAH
