/-
# Chen--Gupta--Li Proposition 5.1 axial height control

Transfers the literal CGL source height window to the remaining third-axis
Fourier tail of a surviving equal-character row triple.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialAggregate

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- In a literal CGL height-`T` source packet, the remaining third ordinate
gap on every surviving triple has size at most `2T`. -/
theorem cglProposition51_axialThirdGap_abs_le_doubleTime
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    |P.ordinate u.1.2.2 - P.ordinate u.1.1| ≤ 2 * S.time := by
  have htriangle : ‖P.ordinate u.1.2.2 - P.ordinate u.1.1‖ ≤
      ‖P.ordinate u.1.2.2‖ + ‖P.ordinate u.1.1‖ := norm_sub_le _ _
  have hthird := S.ordinate_bound u.1.2.2
  have hfirst := S.ordinate_bound u.1.1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at htriangle
  rw [Real.norm_eq_abs] at hthird hfirst
  nlinarith

/-- The exact nonzero-frequency Fourier-tail mass is uniformly controlled by
the source height window for every surviving axial row triple. -/
theorem cglProposition51_axialFrequencyTailMass_le_timeBudget
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N)
    (w : CGLRealSmoothBump)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
        (P.ordinate u.1.2.2 - P.ordinate u.1.1) ≤
      ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass := by
  have hgap := cglProposition51_axialThirdGap_abs_le_doubleTime S u
  have hbase : 0 ≤ 1 + |P.ordinate u.1.2.2 - P.ordinate u.1.1| := by positivity
  have htime : 0 ≤ 1 + 2 * S.time := by linarith [S.time_one]
  have hpow : (1 + |P.ordinate u.1.2.2 - P.ordinate u.1.1|) ^ 2 ≤
      (1 + 2 * S.time) ^ 2 := by
    nlinarith
  have hconst : 0 ≤ cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 /
      (2 * Real.pi) ^ 2 := by
    exact div_nonneg (cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump 2)
      (sq_nonneg _)
  have hscale : 0 < cglAffineFourierScale N (cglLemma45FibreModulus q) :=
    cglAffineFourierScale_pos N (cglLemma45FibreModulus q)
  have hmass : 0 ≤ cglProposition51PuncturedInverseSquareMass := by
    unfold cglProposition51PuncturedInverseSquareMass
    exact tsum_nonneg fun m => by positivity
  calc
    cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
        (P.ordinate u.1.2.2 - P.ordinate u.1.1) ≤
      ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + |P.ordinate u.1.2.2 - P.ordinate u.1.1|) ^ 2 /
          cglAffineFourierScale N (cglLemma45FibreModulus q)) *
            cglProposition51PuncturedInverseSquareMass :=
      cglProposition51_axialFrequencyTailMass_le w N (cglLemma45FibreModulus q) _
    _ ≤ ((cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ 2) *
        (1 + 2 * S.time) ^ 2 / cglAffineFourierScale N (cglLemma45FibreModulus q)) *
          cglProposition51PuncturedInverseSquareMass := by
      gcongr

end RHTower
