import GaloisForLFunctions.RHTower.XiGaussianDerivativeOrientation

/-!
# A cancellation-preserving bound for the complete quadratic polynomial

The three signed derivative coefficients remain together. The resulting
phase envelope improves the previous three-monomial root envelope by an
explicit nonnegative quadratic term, strictly positive when the constant
coefficient is nonzero and heat time is positive.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianThirdDerivativeRoot (a b c : ℝ) (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  |b - t / 2 * a| * Real.sqrt (xiGaussianDerivativeWeight 0 s) +
    |2 * c - t / 2 * b| * Real.sqrt (xiGaussianDerivativeWeight 1 s) +
      |t / 2 * c| * Real.sqrt (xiGaussianDerivativeWeight 2 s)

theorem xiGaussianThirdDerivativeRoot_nonneg (a b c : ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : 0 ≤ xiGaussianThirdDerivativeRoot a b c s t := by
  unfold xiGaussianThirdDerivativeRoot
  positivity

theorem xiGaussianDerivativeRootEnvelope_third (a b c : ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    xiGaussianDerivativeRootEnvelope (xiHeatThirdPolynomial a b c) s t =
      xiGaussianThirdDerivativeRoot a b c s t ^ 2 := by
  let Q := xiHeatThirdPolynomial a b c
  let D := xiGaussianDerivativePolynomial Q t
  have hQ : Q.natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp only [Polynomial.natDegree_C]; omega
      · have h := Polynomial.natDegree_C_mul_X_pow_le b 1
        simp only [pow_one] at h
        exact h.trans (by omega)
    · exact Polynomial.natDegree_C_mul_X_pow_le c 2
  have hD : D.natDegree ≤ 2 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_derivative_le Q).trans ((Nat.sub_le _ _).trans hQ))
      ((Polynomial.natDegree_C_mul_le _ Q).trans hQ))
  have hs : (∑ j ∈ Finset.range (D.natDegree + 1),
      ‖D.coeff j‖ * Real.sqrt (xiGaussianDerivativeWeight j s)) =
      ∑ j ∈ Finset.range 3, ‖D.coeff j‖ * Real.sqrt (xiGaussianDerivativeWeight j s) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    have hz : D.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
      simp only [Finset.mem_range] at hj
      omega)
    rw [hz, norm_zero, zero_mul]
  change (∑ j ∈ Finset.range (D.natDegree + 1),
    ‖D.coeff j‖ * Real.sqrt (xiGaussianDerivativeWeight j s)) ^ 2 = _
  rw [hs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [D, Q, xiGaussianDerivativePolynomial_coeff, xiHeatThirdPolynomial,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, xiGaussianThirdDerivativeRoot,
    Real.norm_eq_abs, abs_div, show (1 : ℝ) + 1 = 2 by ring]

/-- A signed derivative bound for every coefficient of the actual full three-by-three form. -/
theorem xiGaussianThirdImaginaryChannel_le_derivative (F : Finset XiZeroCopy)
    (a b c : ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom (xiHeatThirdPolynomial a b c) t.1 q) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianThirdDerivativeRoot a b c s t.1 ^ 2 * xiResidualOrientationBudget F := by
  simpa only [xiGaussianDerivativeRootEnvelope_third] using
    xiGaussianImaginaryChannel_le_derivative_budget F (xiHeatThirdPolynomial a b c) s t

/-- The new square-root bound has a uniform explicit saving in the constant direction. -/
theorem xiGaussianThirdDerivativeRoot_add_saving_le (a b c : ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : ℝ // 0 ≤ t}) :
    xiGaussianThirdDerivativeRoot a b c s t +
      |a| * (Real.sqrt (xiGaussianOrientationMonomialEnvelope 0 s t) -
        (t : ℝ) / 2 * Real.sqrt (xiGaussianDerivativeWeight 0 s)) ≤
      |a| * Real.sqrt (xiGaussianOrientationMonomialEnvelope 0 s t) +
        |b| * Real.sqrt (xiGaussianOrientationMonomialEnvelope 1 s t) +
          |c| * Real.sqrt (xiGaussianOrientationMonomialEnvelope 2 s t) := by
  have ht := t.property
  let w : ℕ → ℝ := fun j => Real.sqrt (xiGaussianDerivativeWeight j s)
  let r : ℕ → ℝ := fun j => Real.sqrt (xiGaussianOrientationMonomialEnvelope j s t)
  have hw (j : ℕ) : 0 ≤ w j := Real.sqrt_nonneg _
  have hr (j : ℕ) : 0 ≤ r j := Real.sqrt_nonneg _
  have hw2 (j : ℕ) : w j ^ 2 = xiGaussianDerivativeWeight j s :=
    Real.sq_sqrt (xiGaussianDerivativeWeight_pos j s).le
  have hr2 (j : ℕ) : r j ^ 2 = xiGaussianOrientationMonomialEnvelope j s t :=
    Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg j s t)
  have hA1 : xiGaussianOrientationMonomialEnvelope 1 s t =
      2 * xiGaussianDerivativeWeight 0 s + (t : ℝ) ^ 2 / 2 * xiGaussianDerivativeWeight 1 s := by
    unfold xiGaussianOrientationMonomialEnvelope xiGaussianDerivativeWeight
    ring
  have hA2 : xiGaussianOrientationMonomialEnvelope 2 s t =
      8 * xiGaussianDerivativeWeight 1 s + (t : ℝ) ^ 2 / 2 * xiGaussianDerivativeWeight 2 s := by
    unfold xiGaussianOrientationMonomialEnvelope xiGaussianDerivativeWeight
    ring
  have hr1 : w 0 + (t : ℝ) / 2 * w 1 ≤ r 1 := by
    have h := hr2 1
    rw [hA1, ← hw2 0, ← hw2 1] at h
    apply (sq_le_sq₀ (add_nonneg (hw 0) (mul_nonneg (by positivity) (hw 1))) (hr 1)).mp
    nlinarith only [h, sq_nonneg (w 0 - (t : ℝ) / 2 * w 1)]
  have hr2' : 2 * w 1 + (t : ℝ) / 2 * w 2 ≤ r 2 := by
    have h := hr2 2
    rw [hA2, ← hw2 1, ← hw2 2] at h
    apply (sq_le_sq₀ (add_nonneg (mul_nonneg (by positivity) (hw 1))
      (mul_nonneg (by positivity) (hw 2))) (hr 2)).mp
    nlinarith only [h, sq_nonneg (2 * w 1 - (t : ℝ) / 2 * w 2)]
  have hab : |b - (t : ℝ) / 2 * a| ≤ |b| + (t : ℝ) / 2 * |a| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_div, abs_of_nonneg t.property,
      abs_of_pos (by positivity : (0 : ℝ) < 2)] using abs_add_le b (-((t : ℝ) / 2 * a))
  have hbc : |2 * c - (t : ℝ) / 2 * b| ≤ 2 * |c| + (t : ℝ) / 2 * |b| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_div, abs_of_nonneg t.property,
      abs_of_pos (by positivity : (0 : ℝ) < 2)] using abs_add_le (2 * c) (-((t : ℝ) / 2 * b))
  have htc : |(t : ℝ) / 2 * c| = (t : ℝ) / 2 * |c| := by
    rw [abs_mul, abs_of_nonneg (div_nonneg t.property (by positivity))]
  have h₁ := mul_le_mul_of_nonneg_left hr1 (abs_nonneg b)
  have h₂ := mul_le_mul_of_nonneg_left hr2' (abs_nonneg c)
  have hb₀ := mul_le_mul_of_nonneg_right hab (hw 0)
  have hb₁ := mul_le_mul_of_nonneg_right hbc (hw 1)
  unfold xiGaussianThirdDerivativeRoot
  rw [htc]
  change _ + |a| * (r 0 - (t : ℝ) / 2 * w 0) ≤ |a| * r 0 + |b| * r 1 + |c| * r 2
  nlinarith only [h₁, h₂, hb₀, hb₁]

/-- A nonnegative amount is subtracted from the old full three-monomial phase envelope. -/
theorem xiGaussianThirdDerivativeEnvelope_add_saving_le (a b c : ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : ℝ // 0 ≤ t}) :
    xiGaussianThirdDerivativeRoot a b c s t ^ 2 +
      a ^ 2 * (t : ℝ) ^ 2 / 4 * xiGaussianDerivativeWeight 0 s ≤
        xiGaussianFiniteRootEnvelope ![a, b, c] s t := by
  let u := (t : ℝ) / 2 * Real.sqrt (xiGaussianDerivativeWeight 0 s)
  let r := Real.sqrt (xiGaussianOrientationMonomialEnvelope 0 s t)
  let S := |b| * Real.sqrt (xiGaussianOrientationMonomialEnvelope 1 s t) +
    |c| * Real.sqrt (xiGaussianOrientationMonomialEnvelope 2 s t)
  have ht := t.property
  have hp := xiGaussianThirdDerivativeRoot_nonneg a b c s t
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hru : r ^ 2 = 2 * u ^ 2 := by
    dsimp only [r, u]
    rw [Real.sq_sqrt (xiGaussianOrientationMonomialEnvelope_nonneg 0 s t),
      mul_pow, Real.sq_sqrt (xiGaussianDerivativeWeight_pos 0 s).le]
    unfold xiGaussianOrientationMonomialEnvelope xiGaussianDerivativeWeight
    ring
  have hur : u ≤ r := (sq_le_sq₀ hu hr).mp (by nlinarith only [hru, sq_nonneg u])
  have hT : xiGaussianThirdDerivativeRoot a b c s t ≤ |a| * u + S := by
    have h := xiGaussianThirdDerivativeRoot_add_saving_le a b c s t
    dsimp only [u, S]
    nlinarith only [h]
  have hsq := (sq_le_sq₀ hp (add_nonneg (mul_nonneg (abs_nonneg a) hu) hS)).mpr hT
  have he : (|a| * r) ^ 2 - (|a| * u) ^ 2 =
      a ^ 2 * (t : ℝ) ^ 2 / 4 * xiGaussianDerivativeWeight 0 s := by
    simp only [mul_pow, hru, sq_abs]
    dsimp only [u]
    rw [mul_pow, Real.sq_sqrt (xiGaussianDerivativeWeight_pos 0 s).le]
    ring
  have hcross := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hur (abs_nonneg a)) hS
  have hFin : xiGaussianFiniteRootEnvelope ![a, b, c] s t =
      (|a| * r + S) ^ 2 := by
    simp [xiGaussianFiniteRootEnvelope, Fin.sum_univ_three, r, S, add_assoc]
  rw [hFin]
  nlinarith only [hsq, he, hcross]

end RHTower
