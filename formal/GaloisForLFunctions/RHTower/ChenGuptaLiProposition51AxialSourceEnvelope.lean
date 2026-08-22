/-
# Chen--Gupta--Li Proposition 5.1 axial source envelope

Combines the exact axial finite aggregation with literal source-height control
to give one uniform finite-row envelope for a full axial `S₁` frequency sum.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialHeight

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The certified equal-character off-diagonal carrier injects into all cubic
row triples, hence has cardinality at most `R³`. -/
theorem cglProposition51_fibreEqualCharacterOffDiagonalTriple_card_le_cube
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R) :
    Fintype.card (CGLLemma45FibreEqualCharacterOffDiagonalTriple P) ≤ R ^ 3 := by
  calc
    Fintype.card (CGLLemma45FibreEqualCharacterOffDiagonalTriple P) ≤
        Fintype.card (Fin R × Fin R × Fin R) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = R ^ 3 := by simp [pow_three]

/-- A full punctured axial CGL coefficient sum is bounded by the cubic row
count times one source-height-controlled row-tail budget. -/
theorem cglProposition51_axialFrequencyTerm_norm_tsum_le_heightRowBudget
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N)
    (w : CGLRealSmoothBump) (n : ℕ) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      (R : ℝ) ^ 3 * ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
        cglProposition51FibreAxialAnalyticBudget P w N n *
          (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
            (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
              cglProposition51PuncturedInverseSquareMass) := by
  let U := CGLLemma45FibreEqualCharacterOffDiagonalTriple P
  let B : ℝ := ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
    cglProposition51FibreAxialAnalyticBudget P w N n *
      (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass)
  have hQ : 0 ≤ ((cglLemma45FibreModulus q).value : ℝ) ^ 3 := by positivity
  have hbudget : 0 ≤ cglProposition51FibreAxialAnalyticBudget P w N n := by
    unfold cglProposition51FibreAxialAnalyticBudget
    apply mul_nonneg
    · apply mul_nonneg
      · exact (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
      · exact div_nonneg (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump n)
          (pow_nonneg P.spacing_pos.le _)
    · exact mul_nonneg (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
        (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0)
  have htail : 0 ≤ ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 /
      (2 * Real.pi) ^ 2) * (1 + 2 * S.time) ^ 2 /
        cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass := by
    have hC : 0 ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 /
        (2 * Real.pi) ^ 2 :=
      div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2) (sq_nonneg _)
    have htime : 0 ≤ 1 + 2 * S.time := by linarith [S.time_one]
    have hpowtime : 0 ≤ (1 + 2 * S.time) ^ 2 := pow_nonneg htime _
    have hinvscale : 0 ≤ (cglAffineFourierScale N (cglLemma45FibreModulus q))⁻¹ :=
      inv_nonneg.mpr (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
    have hmass : 0 ≤ cglProposition51PuncturedInverseSquareMass := by
      unfold cglProposition51PuncturedInverseSquareMass
      exact tsum_nonneg fun m => by positivity
    simp only [div_eq_mul_inv]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hpowtime) hinvscale) hmass
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hQ hbudget) htail
  have hterm (u : U) :
      ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
          cglProposition51FibreAxialAnalyticBudget P w N n *
            cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
              (P.ordinate u.1.2.2 - P.ordinate u.1.1) ≤ B := by
    dsimp [B]
    gcongr
    exact cglProposition51_axialFrequencyTailMass_le_timeBudget S w u
  have hcard : (Fintype.card U : ℝ) ≤ (R : ℝ) ^ 3 := by
    exact_mod_cast cglProposition51_fibreEqualCharacterOffDiagonalTriple_card_le_cube P
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ ≤
      ∑ u : U, ((cglLemma45FibreModulus q).value : ℝ) ^ 3 *
          cglProposition51FibreAxialAnalyticBudget P w N n *
            cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
              (P.ordinate u.1.2.2 - P.ordinate u.1.1) :=
      cglProposition51_axialFrequencyTerm_norm_tsum_le_equalCharacterTailBudget P w N n
    _ ≤ ∑ _u : U, B := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u
    _ = (Fintype.card U : ℝ) * B := by simp
    _ ≤ (R : ℝ) ^ 3 * B := by
      exact mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by ring

end RHTower
