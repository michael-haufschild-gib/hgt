/-
# Chen--Gupta--Li Proposition 5.1 axial source power saving

Closes the literal CGL source argument on one `S₁` axis.  The internally
chosen order `25·d`, where `d` is the certified epsilon denominator, absorbs
every finite row, modulus, Fourier-scale, and height factor into `X⁻¹⁰`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialSourceScale

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The absolute punctured-frequency sum on the third CGL `S₁` axis has the
paper's `X⁻¹⁰` saving, with a closed cutoff/epsilon constant.  The required
all-order Fourier decay is chosen internally from the literal source epsilon
certificate; callers supply no raw analytic premise. -/
theorem cglProposition51_axialFrequencyTerm_norm_tsum_le_literalEpsilonSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N)
    (w : CGLRealSmoothBump) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      (9 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.epsilonDenominator * 25) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
          cglProposition51PuncturedInverseSquareMass)) /
        S.base ^ 10 := by
  let T := S.toPaperSourcePacket
  let X := S.base
  let d := S.epsilonDenominator
  let C : ℝ := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump (d * 25) *
    cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
    cglProposition51PuncturedInverseSquareMass
  have hTbase : T.base = X := by rfl
  have hXone : 1 ≤ X := by
    dsimp [X]
    linarith [S.base_five]
  have hX : 0 ≤ X := le_trans zero_le_one hXone
  have hC : 0 ≤ C := by
    have hBn : 0 ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump (d * 25) :=
      cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump _
    have hB0 : 0 ≤ cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 :=
      cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump _
    have hB2 : 0 ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 /
        (2 * Real.pi) ^ 2 :=
      div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2) (sq_nonneg _)
    have hmass : 0 ≤ cglProposition51PuncturedInverseSquareMass := by
      unfold cglProposition51PuncturedInverseSquareMass
      exact tsum_nonneg fun m => by positivity
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg hBn hB0) hB2) hmass
  have hR : (R : ℝ) ≤ X ^ 3 := by
    simpa [T, X, CGLLemma45LiteralEpsilonSourcePacket.toPaperSourcePacket] using
      cglLemma45PaperSourcePacket_rowCount_le_cube T
  have hR3 : (R : ℝ) ^ 3 ≤ X ^ 9 := by
    calc
      (R : ℝ) ^ 3 ≤ (X ^ 3) ^ 3 := pow_le_pow_left₀ (by positivity) hR _
      _ = X ^ 9 := by ring
  have hQ : ((cglLemma45FibreModulus q).value : ℝ) ≤ X := by
    simpa [T, X, CGLLemma45LiteralEpsilonSourcePacket.toPaperSourcePacket] using
      cglProposition51_paperSource_modulus_le_base T
  have hQ3 : ((cglLemma45FibreModulus q).value : ℝ) ^ 3 ≤ X ^ 3 :=
    pow_le_pow_left₀ (by positivity) hQ _
  have htail := cglProposition51_axialAnalyticTailProduct_le_sourceScale T w (d * 25)
  have hspacingPow : X ^ 25 ≤ P.spacing ^ (d * 25) := by
    have h := pow_le_pow_left₀ (pow_nonneg hX 1)
      (cglLemma45LiteralEpsilonSourcePacket_spacing_power S) 25
    simpa [X, d, pow_mul] using h
  have hrecip : 1 / P.spacing ^ (d * 25) ≤ 1 / X ^ 25 := by
    apply one_div_le_one_div_of_le
    · exact pow_pos (lt_of_lt_of_le zero_lt_one hXone) _
    · exact hspacingPow
  have hratio : X ^ 15 / P.spacing ^ (d * 25) ≤ 1 / X ^ 10 := by
    calc
      X ^ 15 / P.spacing ^ (d * 25) = X ^ 15 * (1 / P.spacing ^ (d * 25)) := by ring
      _ ≤ X ^ 15 * (1 / X ^ 25) := by
        exact mul_le_mul_of_nonneg_left hrecip (pow_nonneg hX _)
      _ = X ^ 15 / X ^ 25 := by ring
      _ ≤ 1 / X ^ 10 :=
        cglBasePowerRatio_le_reciprocal X hXone 15 10 25 (by norm_num)
  have hprod :
      cglProposition51FibreAxialAnalyticBudget P w N (d * 25) *
        (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
          (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
            cglProposition51PuncturedInverseSquareMass) ≤
        9 * C * (X ^ 3 / P.spacing ^ (d * 25)) := by
    rw [hTbase] at htail
    simpa [C, d] using htail
  have hanalytic : 0 ≤ cglProposition51FibreAxialAnalyticBudget P w N (d * 25) := by
    unfold cglProposition51FibreAxialAnalyticBudget
    apply mul_nonneg
    · apply mul_nonneg
      · exact (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
      · exact div_nonneg (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump _)
          (pow_nonneg P.spacing_pos.le _)
    · exact mul_nonneg (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
        (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0)
  have htailNonneg : 0 ≤
      ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass := by
    have hB2 : 0 ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 /
        (2 * Real.pi) ^ 2 :=
      div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2) (sq_nonneg _)
    have htimeone : 1 ≤ T.time := T.time_one
    have htime : 0 ≤ 1 + 2 * T.time := by linarith
    have hinv : 0 ≤ (cglAffineFourierScale N (cglLemma45FibreModulus q))⁻¹ :=
      inv_nonneg.mpr (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
    have hmass : 0 ≤ cglProposition51PuncturedInverseSquareMass := by
      unfold cglProposition51PuncturedInverseSquareMass
      exact tsum_nonneg fun m => by positivity
    simp only [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (mul_nonneg hB2 (pow_nonneg htime _)) hinv) hmass
  have hprodNonneg : 0 ≤ cglProposition51FibreAxialAnalyticBudget P w N (d * 25) *
      (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass) := mul_nonneg hanalytic htailNonneg
  have htotal :
      (R : ℝ) ^ 3 * ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
        (cglProposition51FibreAxialAnalyticBudget P w N (d * 25) *
          (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
            (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
              cglProposition51PuncturedInverseSquareMass)) ≤
        X ^ 9 * X ^ 3 * (9 * C * (X ^ 3 / P.spacing ^ (d * 25))) := by
    calc
      _ ≤ X ^ 9 * X ^ 3 *
          (cglProposition51FibreAxialAnalyticBudget P w N (d * 25) *
            (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
              (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
                cglProposition51PuncturedInverseSquareMass)) := by
          gcongr
      _ ≤ _ := by gcongr
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      (R : ℝ) ^ 3 * ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
        cglProposition51FibreAxialAnalyticBudget P w N (d * 25) *
          (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
            (1 + 2 * T.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
              cglProposition51PuncturedInverseSquareMass) :=
      cglProposition51_axialFrequencyTerm_norm_tsum_le_heightRowBudget T w (d * 25)
    _ ≤ (X ^ 9) * (X ^ 3) *
        (9 * C * (X ^ 3 / P.spacing ^ (d * 25))) := by
      simpa only [mul_assoc] using htotal
    _ = (9 * C) * (X ^ 15 / P.spacing ^ (d * 25)) := by ring
    _ ≤ (9 * C) * (1 / X ^ 10) := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by
      dsimp [C, X, d]
      ring

end RHTower
