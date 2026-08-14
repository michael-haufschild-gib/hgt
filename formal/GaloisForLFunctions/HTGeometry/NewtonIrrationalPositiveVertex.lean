import GaloisForLFunctions.HTGeometry.NewtonLevelComposition
import GaloisForLFunctions.HTGeometry.NewtonBoundRational

/-!
# An irrational exact order forces a positive leading vertex

The Newton condition at level `r` says exactly that the weighted level of an operator is maximised
at the shift `0`:

```text
deg Φ_μ ≤ deg Φ_0 + r μ      ⟺      λ_r(μ) ≤ λ_r(0) .
```

If a formal solution of a linear analytic equation had irrational exact Gevrey order `s` while that
condition held at level `s`, then the least admissible level would be a **rational** number below
`s`, and Maillet's theorem at that level would make the solution Gevrey of an order strictly below
its exact one.  So the leading vertex of the operator at an irrational exact order always sits at a
positive shift.

This is the exact point where the elementary theory stops: the remaining half of the exact-order
theorem has to move that vertex, which is what a factorization along the Newton polygon does.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The Newton condition read on weighted levels -/

theorem newtonBoundedBy_iff_weightedLevel_le {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) {r : ℝ} :
    NewtonBoundedBy B r ↔
      ∀ μ : ℕ, 1 ≤ μ → shiftPolynomial B μ ≠ 0 →
        weightedLevel r (shiftPolynomial B) μ ≤ weightedLevel r (shiftPolynomial B) 0 := by
  constructor
  · intro h μ hμ hne
    have hdeg : (shiftPolynomial B μ).natDegree ≤ m := natDegree_shiftPolynomial_le B μ
    have hcoef : (shiftPolynomial B μ).coeff (shiftPolynomial B μ).natDegree ≠ 0 := by
      rw [← Polynomial.leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hne
    set j : Fin (m + 1) := ⟨(shiftPolynomial B μ).natDegree, by omega⟩ with hj
    have hj' : ((j : ℕ) : ℕ) = (shiftPolynomial B μ).natDegree := rfl
    have hBj : PowerSeries.coeff μ (B j) ≠ 0 := by
      rw [← coeff_shiftPolynomial B μ j, hj']
      exact hcoef
    have hle := h μ j hμ hBj
    rw [weightedLevel, weightedLevel_zero]
    rw [hj'] at hle
    linarith
  · intro h μ j hμ hBj
    have hne : shiftPolynomial B μ ≠ 0 := shiftPolynomial_ne_zero_of_coeff hBj
    have hle := h μ hμ hne
    have hjdeg : (j : ℕ) ≤ (shiftPolynomial B μ).natDegree := by
      refine Polynomial.le_natDegree_of_ne_zero ?_
      rw [coeff_shiftPolynomial B μ j]
      exact hBj
    have hjdeg' : ((j : ℕ) : ℝ) ≤ (((shiftPolynomial B μ).natDegree : ℕ) : ℝ) := by
      exact_mod_cast hjdeg
    rw [weightedLevel, weightedLevel_zero] at hle
    linarith

/-! ### The obstruction -/

/-- **An irrational exact Gevrey order forces the leading vertex to a positive shift.**  Otherwise
the least Newton level would be a rational number strictly below the exact order, and Maillet's
theorem there would contradict exactness. -/
theorem exists_positive_weightedLevel_of_irrational_exactOrder {m : ℕ}
    (B : Fin (m + 1) → PowerSeries ℂ) (hB : ∀ j, IsGevreySeries 0 (B j))
    (hΦ : shiftPolynomial B 0 ≠ 0)
    {F G : PowerSeries ℂ} (hG : IsGevreySeries 0 G) (hsol : eulerLinearOp B F = G)
    {s : ℝ} (hs0 : 0 ≤ s) (hirr : Irrational s) (hex : IsExactGevreySeriesOrder F s) :
    ∃ μ : ℕ, 1 ≤ μ ∧ shiftPolynomial B μ ≠ 0 ∧
      weightedLevel s (shiftPolynomial B) 0 < weightedLevel s (shiftPolynomial B) μ := by
  by_contra hcon
  push Not at hcon
  have hNB : NewtonBoundedBy B s := by
    rw [newtonBoundedBy_iff_weightedLevel_le]
    intro μ hμ hne
    exact hcon μ hμ hne
  obtain ⟨q, hq0, hqNB, hqmin⟩ := exists_rat_least_newtonBound B
  have hqs : ((q : ℚ) : ℝ) ≤ s := hqmin s hs0 hNB
  have hqne : ((q : ℚ) : ℝ) ≠ s := fun hc => hirr ⟨q, hc⟩
  have hlt : ((q : ℚ) : ℝ) < s := lt_of_le_of_ne hqs hqne
  have hq0' : (0 : ℝ) ≤ ((q : ℚ) : ℝ) := by exact_mod_cast hq0
  have hgev : IsGevreySeries ((q : ℚ) : ℝ) F :=
    isGevreySeries_of_eulerLinearOp_eq_newton hq0' B hB hΦ hqNB hG hsol
  exact hex.2 ((q : ℚ) : ℝ) hlt hgev

end GaloisForLFunctions.HTGeometry
