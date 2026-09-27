import GaloisForLFunctions.RHTower.XiCriticalResidualSourceImprovement

/-!
# The adaptive residual gap suppresses transverse orientation

The full off-critical fourth trace overestimates the phase carried by zeros
near the critical line. The strip width and adaptive height gap instead
charge their reciprocal-square imaginary energy by
`129 / (128 * G_F - 129)` times the off-critical source atom.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

theorem thirtyTwo_lt_xiCriticalResidualPhaseGap (F : Finset XiZeroCopy) :
    (32 : ℝ) < xiCriticalResidualPhaseGap F := by
  have h : (32 : ℝ) < xiGaussianCertifiedPhaseGap := by
    rw [xiGaussianCertifiedPhaseGap_eq]
    linarith
  exact h.trans_le (xiGaussianCertifiedPhaseGap_le_residualPhaseGap F)

theorem xiResidualOrientationDenominator_pos (F : Finset XiZeroCopy) :
    0 < 128 * xiCriticalResidualPhaseGap F - 129 := by
  linarith only [thirtyTwo_lt_xiCriticalResidualPhaseGap F]

/-- The spectral strip and adaptive gap bound the actual transverse reciprocal energy. -/
theorem xiThermalOrientationTerm_mul_residualGap_le_offAtom
    (F : Finset XiZeroCopy) (q : XiZeroCopy) :
    (128 * xiCriticalResidualPhaseGap F - 129) *
        (xiZeroCopyReciprocalSquare q).im ^ 2 ≤ 129 * xiFourthTraceOffAtom q := by
  by_cases hreal : (xiSpectralPoint q).im = 0
  · have hx : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using hreal
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare, hx]
      simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_im]
    simp only [xiFourthTraceOffAtom, if_pos hreal, him,
      zero_pow (by omega : 2 ≠ 0), mul_zero, le_refl]
  · let z := xiSpectralPoint q ^ 2
    let A := z.re
    let B := z.im
    have hgap : xiCriticalResidualPhaseGap F < A := xiSpectralSq_re_gt_residualPhaseGap F ⟨q, hreal⟩
    have hA : 0 < A := xiSpectralSq_re_pos q
    have hA32 : 32 < A := (thirtyTwo_lt_xiCriticalResidualPhaseGap F).trans hgap
    have hi := xiSpectralPoint_im_sq_lt_quarter q
    have hxy := mul_le_mul_of_nonneg_left hi.le (sq_nonneg (xiSpectralPoint q).re)
    have hsector : 128 * B ^ 2 ≤ 129 * A := by
      have hAr : A = (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 := by
        simp only [A, z, pow_two, Complex.mul_re]
      have hBr : B ^ 2 = 4 * (xiSpectralPoint q).re ^ 2 * (xiSpectralPoint q).im ^ 2 := by
        simp only [B, z, pow_two, Complex.mul_im]
        ring
      rw [hBr]
      nlinarith only [hxy, hi, hAr, hA32]
    have hscaled : 128 * xiCriticalResidualPhaseGap F * B ^ 2 ≤ 129 * A ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_right hgap.le (show 0 ≤ 128 * B ^ 2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right hsector hA.le
      nlinarith only [h₁, h₂]
    have hweight := mul_le_mul_of_nonneg_right hscaled
      (sq_nonneg ((Complex.normSq z)⁻¹))
    have hu : xiZeroCopyReciprocalSquare q = z⁻¹ := by
      dsimp only [xiZeroCopyReciprocalSquare, z]
      rw [inv_pow]
    rw [xiFourthTraceOffAtom, if_neg hreal, hu]
    simp only [pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    change (128 * xiCriticalResidualPhaseGap F - 129) *
        ((-B / Complex.normSq z) * (-B / Complex.normSq z)) ≤
      129 * ((A / Complex.normSq z) * (A / Complex.normSq z) -
        (-B / Complex.normSq z) * (-B / Complex.normSq z))
    simp only [div_eq_mul_inv] at *
    nlinarith only [hweight]

/-- Every actual reciprocal orientation atom is controlled by the unspent off-critical source. -/
theorem xiThermalOrientationTerm_le_residual_source_weight
    (F : Finset XiZeroCopy) (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (129 / (128 * xiCriticalResidualPhaseGap F - 129)) * xiFourthTraceOffAtom q := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (xiResidualOrientationDenominator_pos F)).mpr
  have h := xiThermalOrientationTerm_mul_residualGap_le_offAtom F q
  simpa only [mul_comm] using h

def xiResidualOrientationBudget (F : Finset XiZeroCopy) : ℝ :=
  129 * xiCriticalFourthTraceResidual F / (128 * xiCriticalResidualPhaseGap F - 129)

theorem xiResidualOrientationBudget_pos (F : Finset XiZeroCopy) :
    0 < xiResidualOrientationBudget F :=
  div_pos (mul_pos (by positivity) (xiCriticalFourthTraceResidual_pos F))
    (xiResidualOrientationDenominator_pos F)

/-- Complete transverse orientation is bounded independently of polynomial coefficients and heat. -/
theorem xiThermalOrientationEnergy_le_residualOrientationBudget (F : Finset XiZeroCopy) :
    xiThermalOrientationEnergy ≤ xiResidualOrientationBudget F := by
  let k : ℝ := 129 / (128 * xiCriticalResidualPhaseGap F - 129)
  have hk : 0 ≤ k := (div_pos (by positivity) (xiResidualOrientationDenominator_pos F)).le
  have h := summable_xiThermalOrientationTerm.tsum_le_tsum
    (xiThermalOrientationTerm_le_residual_source_weight F) (summable_xiFourthTraceOffAtom.mul_left k)
  rw [tsum_mul_left] at h
  calc
    _ ≤ k * ∑' q : XiZeroCopy, xiFourthTraceOffAtom q := h
    _ ≤ k * xiCriticalFourthTraceResidual F :=
      mul_le_mul_of_nonneg_left (tsum_xiFourthTraceOffAtom_le_residual F) hk
    _ = _ := by unfold k xiResidualOrientationBudget; ring

end RHTower
