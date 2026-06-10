import Mathlib
import ICAH.Definability

namespace ICAH

open Cardinal Polynomial Filter Topology Set

/-!
## Real-closedness of `ℝ` and of root-closed subfields (M4)

This file proves:

1. `ICAH.Real.isRealClosed` — `IsRealClosed ℝ`, replacing the former named axiom.
   Uses `IsRealClosed.of_linearOrderedField` with `Real.sqrt` for squares and an
   IVT argument for odd-degree polynomial roots.

2. `ICAH.isRealClosed_of_forall_root` — a `Subfield ℝ` that contains every real
   root of every nonzero polynomial with coefficients in it is real closed.
   The hypothesis is stated entirely at the level of `ℝ[X]`, so no instance
   transport between subtype carriers is needed when applying it.
-/

/-! ### Squares -/

/-- Every non-negative real is a square (`Real.sqrt`). -/
private lemma Real.isSquare_of_nonneg {x : ℝ} (hx : 0 ≤ x) : IsSquare x :=
  Real.isSquare_iff.mpr hx

/-! ### Odd-degree polynomials have roots (IVT) -/

private lemma Real.exists_pos_eval {f : ℝ[X]} (hdeg : 0 < f.degree)
    (hlead : 0 < f.leadingCoeff) : ∃ x, 0 < f.eval x := by
  obtain ⟨t, ht⟩ := ((f.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead.le).eventually
    (eventually_gt_atTop 0)).exists
  exact ⟨t, ht⟩

private lemma Real.exists_neg_eval {f : ℝ[X]} (hf : Odd f.natDegree)
    (hlead : 0 < f.leadingCoeff) : ∃ x, f.eval x < 0 := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hf.pos
  set g := -f.comp (-X) with hg
  have hgdeg : 0 < g.degree := by
    simpa [g, degree_neg, degree_comp, degree_X] using hdeg
  have hglead : 0 < g.leadingCoeff := by
    simp [g, leadingCoeff_neg, comp_neg_X_leadingCoeff_eq, hf.neg_one_pow]
    exact hlead
  obtain ⟨t, ht⟩ := Real.exists_pos_eval hgdeg hglead
  simp [g, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] at ht
  exact ⟨-t, by linarith⟩

private lemma Real.exists_isRoot_of_odd_pos_leading {f : ℝ[X]} (hf : Odd f.natDegree)
    (hlead : 0 < f.leadingCoeff) : ∃ x, f.IsRoot x := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hf.pos
  obtain ⟨a, ha⟩ := Real.exists_pos_eval hdeg hlead
  obtain ⟨b, hb⟩ := Real.exists_neg_eval hf hlead
  have h0mem : (0 : ℝ) ∈ Set.Icc (f.eval b) (f.eval a) := ⟨le_of_lt hb, le_of_lt ha⟩
  obtain ⟨c, hc⟩ := intermediate_value_univ b a f.continuous h0mem
  exact ⟨c, hc⟩

/-- Every odd-degree polynomial over `ℝ` has a real root (IVT). -/
theorem Real.exists_isRoot_of_odd_natDegree {f : ℝ[X]} (hf : Odd f.natDegree) :
    ∃ x, f.IsRoot x := by
  rcases lt_trichotomy 0 f.leadingCoeff with hlead | heq | hlead
  · exact Real.exists_isRoot_of_odd_pos_leading hf hlead
  · exfalso
    have hfz : f = 0 := leadingCoeff_eq_zero.mp heq.symm
    rw [hfz, natDegree_zero] at hf
    exact absurd hf (by decide)
  · have hneg : 0 < (-f).leadingCoeff := by rw [leadingCoeff_neg]; linarith
    have hf' : Odd (-f).natDegree := by rwa [natDegree_neg]
    obtain ⟨x, hx⟩ := Real.exists_isRoot_of_odd_pos_leading hf' hneg
    refine ⟨x, ?_⟩
    have hzero : -f.eval x = 0 := by simpa [IsRoot, eval_neg] using hx
    simpa [IsRoot] using neg_eq_zero.mp hzero

/-- `ℝ` is a real-closed field. Formerly the named axiom `ICAH.Real.isRealClosed`. -/
theorem Real.isRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun hx => Real.isSquare_of_nonneg hx)
    (fun hf => Real.exists_isRoot_of_odd_natDegree hf)

/-! ### Root-closed subfields of ℝ are real closed -/

/-- A subfield of `ℝ` that contains every real root of every nonzero polynomial
    with coefficients in it is real closed.

    The root-closure hypothesis is stated at the level of `ℝ[X]`, which keeps all
    instance reasoning on the ambient `ℝ` side. Squares are handled via the
    polynomial `X² - C x` and `Real.sqrt`; odd-degree roots come from
    `Real.exists_isRoot_of_odd_natDegree` applied to the pushed-forward polynomial. -/
theorem isRealClosed_of_forall_root (K : Subfield ℝ)
    (hroot : ∀ p : ℝ[X], p ≠ 0 → (∀ n, p.coeff n ∈ K) → ∀ c : ℝ, p.IsRoot c → c ∈ K) :
    IsRealClosed K := by
  apply IsRealClosed.of_linearOrderedField
  · -- non-negative elements are squares
    intro x hx
    have hx' : (0 : ℝ) ≤ (x : ℝ) := by
      have := Subtype.coe_le_coe.mpr hx
      simpa using this
    have hmem : Real.sqrt (x : ℝ) ∈ K := by
      refine hroot (X ^ 2 - C (x : ℝ)) (X_pow_sub_C_ne_zero (by norm_num) _) ?_ _ ?_
      · intro n
        rcases n with _ | _ | _ | n
        · simpa [coeff_sub, coeff_X_pow, coeff_C] using K.neg_mem x.2
        · simp [coeff_sub, coeff_X_pow, coeff_C]
        · simpa [coeff_sub, coeff_X_pow, coeff_C] using K.one_mem
        · simp [coeff_sub, coeff_X_pow, coeff_C]
      · simp [IsRoot, Real.sq_sqrt hx']
    refine ⟨⟨Real.sqrt (x : ℝ), hmem⟩, Subtype.ext ?_⟩
    push_cast
    exact (Real.mul_self_sqrt hx').symm
  · -- odd-degree polynomials have roots
    intro f hf
    have hf0 : f ≠ 0 := fun h => by
      rw [h, natDegree_zero] at hf
      exact absurd hf (by decide)
    have hpdeg : Odd (f.map (algebraMap K ℝ)).natDegree := by rwa [natDegree_map]
    obtain ⟨c, hc⟩ := Real.exists_isRoot_of_odd_natDegree hpdeg
    have hcK : c ∈ K := by
      refine hroot (f.map (algebraMap K ℝ)) (map_ne_zero hf0) ?_ c hc
      intro n
      rw [coeff_map]
      exact (f.coeff n).2
    refine ⟨⟨c, hcK⟩, ?_⟩
    have h1 : (f.map (algebraMap K ℝ)).eval c = 0 := hc
    rw [eval_map, show c = algebraMap K ℝ ⟨c, hcK⟩ from rfl, eval₂_at_apply] at h1
    -- h1 : algebraMap K ℝ (f.eval ⟨c, hcK⟩) = 0
    show f.eval ⟨c, hcK⟩ = 0
    exact (algebraMap K ℝ).injective (h1.trans (map_zero (algebraMap K ℝ)).symm)

end ICAH
