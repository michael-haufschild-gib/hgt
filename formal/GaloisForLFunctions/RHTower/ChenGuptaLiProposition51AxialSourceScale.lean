/-
# Chen--Gupta--Li Proposition 5.1 axial source-scale algebra

Reduces the height-controlled axial row envelope to one explicit source-scale
factor: a fixed cutoff constant times `X³ / spacingⁿ`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialSourceEnvelope

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The positive CGL modulus is at most the literal paper source scale. -/
theorem cglProposition51_paperSource_modulus_le_base
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) :
    ((cglLemma45FibreModulus q).value : ℝ) ≤ S.base := by
  have h : (q + 1 : ℝ) ≤ S.base := by
    calc
      (q + 1 : ℝ) = (q + 1 : ℝ) * 1 := by ring
      _ ≤ (q + 1 : ℝ) * S.time := by
        exact mul_le_mul_of_nonneg_left S.time_one (by positivity)
      _ = S.base := S.base_eq_modulus_mul_time.symm
  simpa only [cglLemma45FibreModulus, Nat.cast_add, Nat.cast_one] using h

/-- The height factor in the remaining axial Fourier tail is at most
`9 X²` at the literal paper source scale `X`. -/
theorem cglProposition51_source_time_factor_le_nine_mul_base_sq
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) :
    (1 + 2 * S.time) ^ 2 ≤ 9 * S.base ^ 2 := by
  have htime : S.time ≤ S.base := cglLemma45PaperSourcePacket_time_le_base S
  have hbase : 1 ≤ S.base := by linarith [S.base_five]
  have hmain : 1 + 2 * S.time ≤ 3 * S.base := by linarith
  have hleft : 0 ≤ 1 + 2 * S.time := by linarith [S.time_one]
  calc
    (1 + 2 * S.time) ^ 2 ≤ (3 * S.base) ^ 2 :=
      pow_le_pow_left₀ hleft hmain _
    _ = 9 * S.base ^ 2 := by ring

/-- Product of the two zero-coordinate analytic factors and the remaining
nonzero-frequency tail is bounded by a closed cutoff constant times
`9 X³ / spacingⁿ`. -/
theorem cglProposition51_axialAnalyticTailProduct_le_sourceScale
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N)
    (w : CGLRealSmoothBump) (n : ℕ) :
    cglProposition51FibreAxialAnalyticBudget P w N n *
      (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass) ≤
      9 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
          cglProposition51PuncturedInverseSquareMass) *
        (S.base ^ 3 / P.spacing ^ n) := by
  let F := cglAffineFourierScale N (cglLemma45FibreModulus q)
  let Bn := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump n
  let B0 := cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0
  let B2 := cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2
  let M := cglProposition51PuncturedInverseSquareMass
  let H := 1 + 2 * S.time
  let X := S.base
  have hFpos : 0 < F := by
    simpa [F] using cglAffineFourierScale_pos N (cglLemma45FibreModulus q)
  have hFle : F ≤ X := by
    simpa [F, X, CGLLemma45PaperSourcePacket.toSourceScale] using S.toSourceScale.fourierScale_le
  have hHsq : H ^ 2 ≤ 9 * X ^ 2 := by
    simpa [H, X] using cglProposition51_source_time_factor_le_nine_mul_base_sq S
  have hBn : 0 ≤ Bn :=
    cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump n
  have hB0 : 0 ≤ B0 :=
    cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0
  have hB2 : 0 ≤ B2 :=
    div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2) (sq_nonneg _)
  have hM : 0 ≤ M := by
    unfold M cglProposition51PuncturedInverseSquareMass
    exact tsum_nonneg fun m => by positivity
  have hC : 0 ≤ Bn * B0 * B2 * M := by positivity
  have hX : 0 ≤ X := by
    dsimp [X]
    linarith [S.base_five]
  have hspacing : 0 < P.spacing ^ n := pow_pos P.spacing_pos _
  have hcore : F * H ^ 2 / P.spacing ^ n ≤ 9 * X ^ 3 / P.spacing ^ n := by
    apply div_le_div_of_nonneg_right _ hspacing.le
    calc
      F * H ^ 2 ≤ X * (9 * X ^ 2) := by gcongr
      _ = 9 * X ^ 3 := by ring
  have heq :
      cglProposition51FibreAxialAnalyticBudget P w N n *
        (((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
          (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
            cglProposition51PuncturedInverseSquareMass) =
        (Bn * B0 * B2 * M) * (F * H ^ 2 / P.spacing ^ n) := by
    dsimp [F, Bn, B0, B2, M, H]
    unfold cglProposition51FibreAxialAnalyticBudget
    field_simp [ne_of_gt hFpos, ne_of_gt P.spacing_pos]
  rw [heq]
  calc
    (Bn * B0 * B2 * M) * (F * H ^ 2 / P.spacing ^ n) ≤
      (Bn * B0 * B2 * M) * (9 * X ^ 3 / P.spacing ^ n) :=
        mul_le_mul_of_nonneg_left hcore hC
    _ = _ := by ring

end RHTower
