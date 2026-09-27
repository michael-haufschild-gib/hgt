import GaloisForLFunctions.RHTower.XiGaussianDerivativeOrientation

/-!
# A surviving leading coefficient in the derivative ceiling

Signed cancellation cannot remove the top coefficient of a nonzero
polynomial at positive heat time. The resulting lower bound tests whether
the explicit phase majorant can cross the domination threshold.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

theorem xiGaussianDerivativeRootEnvelope_coeff_lower (Q : Polynomial ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) (j : ℕ) :
    (xiGaussianDerivativePolynomial Q t).coeff j ^ 2 * xiGaussianDerivativeWeight j s ≤
      xiGaussianDerivativeRootEnvelope Q s t := by
  let D := xiGaussianDerivativePolynomial Q t
  change D.coeff j ^ 2 * xiGaussianDerivativeWeight j s ≤
    (∑ k ∈ Finset.range (D.natDegree + 1),
      ‖D.coeff k‖ * Real.sqrt (xiGaussianDerivativeWeight k s)) ^ 2
  by_cases hj : D.coeff j = 0
  · rw [hj, zero_pow (by omega : 2 ≠ 0), zero_mul]
    exact sq_nonneg _
  have hmem : j ∈ Finset.range (D.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hj))
  have hsum := Finset.single_le_sum
    (s := Finset.range (D.natDegree + 1))
    (f := fun k => ‖D.coeff k‖ * Real.sqrt (xiGaussianDerivativeWeight k s))
    (fun k _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hmem
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  simpa only [mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (xiGaussianDerivativeWeight_pos j s).le] using hsq

/-- The heat derivative retains the original leading coefficient with factor `-t/2`. -/
theorem xiGaussianDerivativeRootEnvelope_leading_lower (Q : Polynomial ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    (t ^ 2 / 4 * Q.leadingCoeff ^ 2) * xiGaussianDerivativeWeight Q.natDegree s ≤
      xiGaussianDerivativeRootEnvelope Q s t := by
  have h := xiGaussianDerivativeRootEnvelope_coeff_lower Q s t Q.natDegree
  rw [xiGaussianDerivativePolynomial_coeff, Polynomial.coeff_natDegree_succ_eq_zero,
    Polynomial.coeff_natDegree, mul_zero, zero_sub] at h
  convert h using 1
  ring

/-- Half-time anchoring has only polynomial decay in this coefficient envelope. -/
theorem xiGaussianDerivativeRootEnvelope_half_leading_lower (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    (Q.leadingCoeff ^ 2 * ((2 * Q.natDegree + 4).factorial : ℝ) *
      4 ^ (2 * Q.natDegree + 3)) / (t : ℝ) ^ (2 * Q.natDegree + 2) ≤
        xiGaussianDerivativeRootEnvelope Q (xiGaussianHalfHeat t) t := by
  have h := xiGaussianDerivativeRootEnvelope_leading_lower Q (xiGaussianHalfHeat t) t
  refine le_trans (le_of_eq ?_) h
  unfold xiGaussianDerivativeWeight xiGaussianHalfHeat
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  rw [show (2 : ℝ) / ((t : ℝ) / 2) = 4 / (t : ℝ) by field_simp; ring]
  rw [show 2 * Q.natDegree + 4 = (2 * Q.natDegree + 2) + 2 by omega,
    show 2 * Q.natDegree + 3 = (2 * Q.natDegree + 2) + 1 by omega]
  simp only [pow_add, pow_one, div_pow]
  field_simp [ht]

end RHTower
