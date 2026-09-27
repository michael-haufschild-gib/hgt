import GaloisForLFunctions.RHTower.XiGaussianDerivativeOrientation
import GaloisForLFunctions.HTGeometry.ShiftedPolynomialExponentialDomination

/-!
# Signed derivative phase control with the entire residual decay rate

The shifted factorial envelope retains `exp (-t * G)` at every positive
heat time. The polynomial and heat derivatives stay combined before norms.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianFullGapPowerEnvelope (F : Finset XiZeroCopy) (k : ℕ)
    (t : {t : ℝ // 0 < t}) : ℝ :=
  2 ^ k * shiftedFactorialHeatEnvelope k
    ⟨xiCriticalResidualPhaseGap F, (xiCriticalResidualPhaseGap_pos F).le⟩ t

theorem xiGaussianFullGapPowerEnvelope_nonneg (F : Finset XiZeroCopy) (k : ℕ)
    (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianFullGapPowerEnvelope F k t :=
  mul_nonneg (by positivity) (shiftedFactorialHeatEnvelope_nonneg _ _ _)

theorem xiSpectralSq_norm_pow_heat_le_fullGap (F : Finset XiZeroCopy) (k : ℕ)
    (t : {t : ℝ // 0 < t}) (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    ‖xiSpectralPoint q.1 ^ 2‖ ^ k * Real.exp (-((t : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
      Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) * xiGaussianFullGapPowerEnvelope F k t := by
  let A := (xiSpectralPoint q.1 ^ 2).re
  have hsector : ‖xiSpectralPoint q.1 ^ 2‖ ≤ 2 * A := by
    rw [norm_pow]
    simpa only [Complex.sq_norm, A] using
      (xiSpectralPoint_normSq_lt_two_mul_sq_re q.1).le
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hsector k) (Real.exp_pos (-((t : ℝ) * A))).le
  have hb := mul_le_mul_of_nonneg_left
    (pow_mul_exp_neg_le_shiftedFactorial k
      ⟨xiCriticalResidualPhaseGap F, (xiCriticalResidualPhaseGap_pos F).le⟩ t
      ⟨A, (xiSpectralSq_re_gt_residualPhaseGap F q).le⟩)
    (show 0 ≤ (2 : ℝ) ^ k by positivity)
  rw [mul_pow] at hp
  exact hp.trans (by simpa only [xiGaussianFullGapPowerEnvelope, mul_assoc, mul_comm,
    mul_left_comm] using hb)

def xiGaussianFullGapDerivativeEnvelope (F : Finset XiZeroCopy) (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) : ℝ :=
  (∑ j ∈ Finset.range ((xiGaussianDerivativePolynomial Q t).natDegree + 1),
    ‖(xiGaussianDerivativePolynomial Q t).coeff j‖ *
      Real.sqrt (xiGaussianFullGapPowerEnvelope F (2 * j + 4) t)) ^ 2

theorem xiGaussianFullGapDerivativeEnvelope_nonneg (F : Finset XiZeroCopy) (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) : 0 ≤ xiGaussianFullGapDerivativeEnvelope F Q t := sq_nonneg _

theorem xiGaussianDerivativeNorm_heat_le_fullGap (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t})
    (q : {q : XiZeroCopy // (xiSpectralPoint q).im ≠ 0}) :
    evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t)
        ‖xiSpectralPoint q.1 ^ 2‖ ^ 2 * ‖xiSpectralPoint q.1 ^ 2‖ ^ 4 *
          Real.exp (-((t : ℝ) * (xiSpectralPoint q.1 ^ 2).re)) ≤
      Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
        xiGaussianFullGapDerivativeEnvelope F Q t := by
  let D := xiGaussianDerivativePolynomial Q t
  let z := xiSpectralPoint q.1 ^ 2
  let r := ‖z‖
  let E := Real.exp (-((t : ℝ) / 2 * z.re))
  let e := Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hE : E ^ 2 = Real.exp (-((t : ℝ) * z.re)) := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hroot (j : ℕ) : r ^ (j + 2) * E ≤
      Real.sqrt e * Real.sqrt (xiGaussianFullGapPowerEnvelope F (2 * j + 4) t) := by
    have hb := xiSpectralSq_norm_pow_heat_le_fullGap F (2 * j + 4) t q
    have hs : (r ^ (j + 2) * E) ^ 2 ≤ e * xiGaussianFullGapPowerEnvelope F (2 * j + 4) t := by
      rw [mul_pow, ← pow_mul, hE, show (j + 2) * 2 = 2 * j + 4 by omega]
      exact hb
    calc
      _ = Real.sqrt ((r ^ (j + 2) * E) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)).symm
      _ ≤ Real.sqrt (e * xiGaussianFullGapPowerEnvelope F (2 * j + 4) t) := Real.sqrt_le_sqrt hs
      _ = _ := Real.sqrt_mul he _
  have hsum : evalRealPolynomialNormBound D r * r ^ 2 * E ≤
      Real.sqrt e * (∑ j ∈ Finset.range (D.natDegree + 1),
        ‖D.coeff j‖ * Real.sqrt (xiGaussianFullGapPowerEnvelope F (2 * j + 4) t)) := by
    calc
      _ = ∑ j ∈ Finset.range (D.natDegree + 1), ‖D.coeff j‖ * (r ^ (j + 2) * E) := by
        simp only [evalRealPolynomialNormBound, Finset.sum_mul, pow_add]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j ∈ Finset.range (D.natDegree + 1),
          ‖D.coeff j‖ * (Real.sqrt e * Real.sqrt (xiGaussianFullGapPowerEnvelope F (2 * j + 4) t)) :=
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
      ‖D.coeff j‖ * Real.sqrt (xiGaussianFullGapPowerEnvelope F (2 * j + 4) t)) ^ 2 at hsq
  rw [hE] at hsq
  exact hsq

/-- The full Gaussian amplitude is bounded at the complete residual exponential rate. -/
theorem xiGaussianImaginaryAtom_le_fullGap_derivative (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (q : XiZeroCopy) :
    xiGaussianImaginaryChannelAtom Q t q ≤
      (Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
        xiGaussianFullGapDerivativeEnvelope F Q t) * (xiZeroCopyReciprocalSquare q).im ^ 2 := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · rw [xiGaussianImaginaryChannelAtom_of_real _ t ⟨q, hreal⟩]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (xiGaussianFullGapDerivativeEnvelope_nonneg F Q t)) (sq_nonneg _)
  let z := xiSpectralPoint q ^ 2
  let A := heatPhaseAmplitude (evalRealPolynomial Q z) t z
  have hI : xiGaussianImaginaryChannelAtom Q t q = A.im ^ 2 := by
    have hA : A ^ 2 = xiPolynomialGaussianHeatTerm Q t q := by
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
  have hp := xiGaussianPolynomialAmplitude_im_sq_le_derivative Q t z
  have hb := mul_le_mul_of_nonneg_left
    (xiGaussianDerivativeNorm_heat_le_fullGap F Q t ⟨q, hreal⟩)
      (sq_nonneg (xiZeroCopyReciprocalSquare q).im)
  rw [hI]
  calc
    _ ≤ z.im ^ 2 * Real.exp (-((t : ℝ) * z.re)) *
        evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t) ‖z‖ ^ 2 := hp
    _ = (xiZeroCopyReciprocalSquare q).im ^ 2 *
        (evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t) ‖z‖ ^ 2 *
          ‖z‖ ^ 4 * Real.exp (-((t : ℝ) * z.re))) := by rw [← hy]; ring
    _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb

theorem xiGaussianImaginaryChannel_le_fullGap_derivative (F : Finset XiZeroCopy)
    (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q) ≤
      Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
        xiGaussianFullGapDerivativeEnvelope F Q t * xiResidualOrientationBudget F := by
  let C := Real.exp (-((t : ℝ) * xiCriticalResidualPhaseGap F)) *
    xiGaussianFullGapDerivativeEnvelope F Q t
  have h := (summable_xiGaussianImaginaryChannelAtom Q t).tsum_le_tsum
    (xiGaussianImaginaryAtom_le_fullGap_derivative F Q t)
    (summable_xiThermalOrientationTerm.mul_left C)
  rw [tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (xiThermalOrientationEnergy_le_residualOrientationBudget F)
    (mul_nonneg (Real.exp_pos _).le (xiGaussianFullGapDerivativeEnvelope_nonneg F Q t)))

end RHTower
