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

/-- Definable sets are closed under preimage along index reordering.
    Given `r : Set (Fin k → ℝ)` definable with params from `S`, and `f : Fin k → Fin m`,
    the set `{g : Fin m → ℝ | g ∘ f ∈ r}` is also definable. -/
lemma definableOn_preimage_comp {S : Set ℝ} {k m : ℕ} {r : Set (Fin k → ℝ)}
    (h : DefinableOn S k r) (f : Fin k → Fin m) :
    DefinableOn S m ((fun g => g ∘ f) ⁻¹' r) :=
  show S.Definable LOR _ from h.preimage_comp f

/-! ### Graph definability for ring operations

The graphs of `+` and `·` on `ℝ` are first-order definable in `LOR` with any
parameter set, because they are given by quantifier-free atomic formulas.

Strategy: build the witness `BoundedFormula`, lift it to `LOR[[↑S]].Formula`
via `lhomWithConstants`, then verify `Realize` via the chain:
  `LHom.realize_onFormula` → `Formula.realize_relabel` → `BoundedFormula.realize_toFormula`. -/

/-- The `LOR`-formula expressing `x₀ + x₁ = x₂` (no free parameters). -/
private def addGraphBF : LOR.BoundedFormula Empty 3 :=
  (Language.Term.func Ring.addFunc
    (fun i => Language.Term.var (Sum.inr i.castSucc))) ='
  (Language.Term.var (Sum.inr (Fin.last 2)))

/-- The `LOR`-formula expressing `x₀ * x₁ = x₂` (no free parameters). -/
private def mulGraphBF : LOR.BoundedFormula Empty 3 :=
  (Language.Term.func Ring.mulFunc
    (fun i => Language.Term.var (Sum.inr i.castSucc))) ='
  (Language.Term.var (Sum.inr (Fin.last 2)))

/-- Lift a parameter-free `LOR`-formula to `LOR[[↑S]]` for use in `Set.Definable`. -/
private noncomputable def liftToWithConstants (S : Set ℝ)
    (φ : LOR.BoundedFormula Empty 3) : LOR.withConstants ↑S |>.Formula (Fin 3) :=
  (Language.lhomWithConstants LOR ↑S).onFormula
    (φ.toFormula.relabel (Sum.elim Empty.elim id))


/-- The graph of real addition is `LOR`-definable with any parameter set. -/
lemma graphDefinable_add (S : Set ℝ) :
    DefinableOn S 3 {f : Fin 3 → ℝ | f 0 + f 1 = f 2} := by
  haveI : (Language.lhomWithConstants LOR ↑S).IsExpansionOn ℝ :=
    withConstants_expansion LOR ↑S
  exact ⟨liftToWithConstants S addGraphBF, by
    ext v
    simp only [Set.mem_setOf_eq, liftToWithConstants, LHom.realize_onFormula,
               Formula.realize_relabel, BoundedFormula.realize_toFormula,
               addGraphBF, BoundedFormula.realize_bdEqual, Term.realize_func,
               Term.realize_var, Ring.addFunc, CompatibleRing.funMap_add,
               Function.comp, Sum.elim_inr]
    simp [Fin.castSucc, Fin.last]⟩

/-- The graph of real multiplication is `LOR`-definable with any parameter set. -/
lemma graphDefinable_mul (S : Set ℝ) :
    DefinableOn S 3 {f : Fin 3 → ℝ | f 0 * f 1 = f 2} := by
  haveI : (Language.lhomWithConstants LOR ↑S).IsExpansionOn ℝ :=
    withConstants_expansion LOR ↑S
  exact ⟨liftToWithConstants S mulGraphBF, by
    ext v
    simp only [Set.mem_setOf_eq, liftToWithConstants, LHom.realize_onFormula,
               Formula.realize_relabel, BoundedFormula.realize_toFormula,
               mulGraphBF, BoundedFormula.realize_bdEqual, Term.realize_func,
               Term.realize_var, Ring.mulFunc, CompatibleRing.funMap_mul,
               Function.comp, Sum.elim_inr]
    simp [Fin.castSucc, Fin.last]⟩

/-! ### Elementary embedding wrapper -/

/-- An elementary embedding between two `LOR`-structures, wrapping
    `FirstOrder.Language.ElementaryEmbedding`. -/
abbrev ElemEmb (A B : Type*) [LOR.Structure A] [LOR.Structure B] :=
  A ↪ₑ[LOR] B

end ICAH
