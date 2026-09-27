import GaloisForLFunctions.RHTower.XiGaussianDerivativePhase

/-!
# Arithmetic orientation bound for the signed Gaussian derivative

The polynomial derivative and the heat derivative are combined before the
coefficient envelope. Every actual spectral copy is retained in the bound.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianDerivativeWeight (j : ℕ) (s : {s : ℝ // 0 < s}) : ℝ :=
  ((2 * j + 4).factorial : ℝ) * (2 / (s : ℝ)) ^ (2 * j + 4)

theorem xiGaussianDerivativeWeight_pos (j : ℕ) (s : {s : ℝ // 0 < s}) :
    0 < xiGaussianDerivativeWeight j s := by
  have hs := s.property
  have hf : (0 : ℝ) < ((2 * j + 4).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * j + 4)
  unfold xiGaussianDerivativeWeight
  positivity

def xiGaussianDerivativeRootEnvelope (Q : Polynomial ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range ((xiGaussianDerivativePolynomial Q t).natDegree + 1),
    ‖(xiGaussianDerivativePolynomial Q t).coeff j‖ *
      Real.sqrt (xiGaussianDerivativeWeight j s)) ^ 2

theorem xiGaussianDerivativeRootEnvelope_nonneg (Q : Polynomial ℝ)
    (s : {s : ℝ // 0 < s}) (t : ℝ) :
    0 ≤ xiGaussianDerivativeRootEnvelope Q s t := sq_nonneg _

/-- The factorial estimate acts on the coefficients after their signed cancellation. -/
theorem xiGaussianDerivativeNorm_heat_le_root (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)})
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t.1)
        ‖xiSpectralPoint q.1 ^ 2‖ ^ 2 * ‖xiSpectralPoint q.1 ^ 2‖ ^ 4 *
          Real.exp (-((t.1 : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianDerivativeRootEnvelope Q s t.1 := by
  let D := xiGaussianDerivativePolynomial Q t.1
  let z := xiSpectralPoint q.1 ^ 2
  let r := ‖z‖
  let E := Real.exp (-((t.1 : ℝ) / 2 * z.re))
  let e := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hE : E ^ 2 = Real.exp (-((t.1 : ℝ) * z.re)) := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hroot (j : ℕ) : r ^ (j + 2) * E ≤
      Real.sqrt e * Real.sqrt (xiGaussianDerivativeWeight j s) := by
    have hb := xiSpectralSq_norm_pow_heat_le_residual_factorial F (2 * j + 4) s t q
    have hs : (r ^ (j + 2) * E) ^ 2 ≤ e * xiGaussianDerivativeWeight j s := by
      rw [mul_pow, ← pow_mul, hE, show (j + 2) * 2 = 2 * j + 4 by omega]
      exact hb
    calc
      _ = Real.sqrt ((r ^ (j + 2) * E) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)).symm
      _ ≤ Real.sqrt (e * xiGaussianDerivativeWeight j s) := Real.sqrt_le_sqrt hs
      _ = _ := Real.sqrt_mul he _
  have hsum : evalRealPolynomialNormBound D r * r ^ 2 * E ≤
      Real.sqrt e * (∑ j ∈ Finset.range (D.natDegree + 1),
        ‖D.coeff j‖ * Real.sqrt (xiGaussianDerivativeWeight j s)) := by
    calc
      _ = ∑ j ∈ Finset.range (D.natDegree + 1), ‖D.coeff j‖ * (r ^ (j + 2) * E) := by
        simp only [evalRealPolynomialNormBound, Finset.sum_mul, pow_add]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j ∈ Finset.range (D.natDegree + 1),
          ‖D.coeff j‖ * (Real.sqrt e * Real.sqrt (xiGaussianDerivativeWeight j s)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hroot j) (norm_nonneg _)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsq := (sq_le_sq₀
    (mul_nonneg (mul_nonneg (evalRealPolynomialNormBound_nonneg _ (norm_nonneg _))
      (sq_nonneg _)) (Real.exp_pos _).le) (by positivity)).mpr hsum
  simp only [mul_pow, ← pow_mul, Real.sq_sqrt he] at hsq
  change evalRealPolynomialNormBound D r ^ 2 * r ^ 4 * E ^ 2 ≤
    e * (∑ j ∈ Finset.range (D.natDegree + 1),
      ‖D.coeff j‖ * Real.sqrt (xiGaussianDerivativeWeight j s)) ^ 2 at hsq
  rw [hE] at hsq
  exact hsq

/-- Actual Xi phase, with the full Gaussian derivative kept inside the coefficient norm. -/
theorem xiGaussianImaginaryAtom_le_derivative_orientation (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom Q t.1 q ≤
      (Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianDerivativeRootEnvelope Q s t.1) * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · rw [xiGaussianImaginaryChannelAtom_of_real _ t.1 ⟨q, hreal⟩]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (xiGaussianDerivativeRootEnvelope_nonneg Q s t.1)) (sq_nonneg _)
  let z := xiSpectralPoint q ^ 2
  let A := heatPhaseAmplitude (evalRealPolynomial Q z) t.1 z
  have hI : xiGaussianImaginaryChannelAtom Q t.1 q = A.im ^ 2 := by
    have hA : A ^ 2 = xiPolynomialGaussianHeatTerm Q t.1 q := by
      rw [heatPhaseAmplitude_sq]
      rfl
    rw [xiGaussianImaginaryChannelAtom, ← hA, norm_pow, Complex.sq_norm,
      Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  have hz : z ≠ 0 := pow_ne_zero _ (xiSpectralPoint_ne_zero q)
  have hu : z⁻¹ = xiZeroCopyReciprocalSquare q := by
    dsimp only [z, xiZeroCopyReciprocalSquare]
    rw [inv_pow]
  have hy : (xiZeroCopyReciprocalSquare q).im ^ 2 * ‖z‖ ^ 4 = z.im ^ 2 := by
    rw [← hu, Complex.inv_im, ← Complex.sq_norm]
    field_simp [(norm_pos_iff.mpr hz).ne']
  have hp := xiGaussianPolynomialAmplitude_im_sq_le_derivative Q t.1 z
  have hb := mul_le_mul_of_nonneg_left
    (xiGaussianDerivativeNorm_heat_le_root F Q s t ⟨q, hreal⟩)
      (sq_nonneg (xiZeroCopyReciprocalSquare q).im)
  rw [hI]
  calc
    _ ≤ z.im ^ 2 * Real.exp (-((t.1 : ℝ) * z.re)) *
        evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t.1) ‖z‖ ^ 2 := hp
    _ = (xiZeroCopyReciprocalSquare q).im ^ 2 *
        (evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t.1) ‖z‖ ^ 2 *
          ‖z‖ ^ 4 * Real.exp (-((t.1 : ℝ) * z.re))) := by rw [← hy]; ring
    _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

theorem xiGaussianImaginaryChannel_le_derivative_budget (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t.1 q) ≤
      Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
        xiGaussianDerivativeRootEnvelope Q s t.1 * xiResidualOrientationBudget F := by
  let C := Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiCriticalResidualPhaseGap F)) *
    xiGaussianDerivativeRootEnvelope Q s t.1
  have h := (summable_xiGaussianImaginaryChannelAtom Q t.1).tsum_le_tsum
    (xiGaussianImaginaryAtom_le_derivative_orientation F Q s t)
    (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left] at h
  change _ ≤ C * xiThermalOrientationEnergy at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (xiThermalOrientationEnergy_le_residualOrientationBudget F)
      (mul_nonneg (Real.exp_pos _).le (xiGaussianDerivativeRootEnvelope_nonneg Q s t.1)))

end RHTower
