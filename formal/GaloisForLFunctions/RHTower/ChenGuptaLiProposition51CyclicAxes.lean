/-
# Chen--Gupta--Li Proposition 5.1 cyclic axis transport

Transports the closed third-axis source estimate through the exact cyclic
symmetry of the full CGL coefficient.  This supplies the corresponding bounds
on all three one-nonzero-coordinate rays without duplicating the analytic
argument.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51Cyclic

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The first coordinate ray in the source `S₁` frequency carrier. -/
def cglProposition51FirstAxialFrequencyVector (m : ℤ) : (ℤ × ℤ) × ℤ := ((m, 0), 0)

/-- The second coordinate ray in the source `S₁` frequency carrier. -/
def cglProposition51SecondAxialFrequencyVector (m : ℤ) : (ℤ × ℤ) × ℤ := ((0, m), 0)

/-- Exact transport from the first `S₁` ray to the closed third-axis coefficient. -/
theorem cglProposition51_firstAxis_term_eq_thirdAxis
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (w : CGLRealSmoothBump) (m : ℤ) :
    cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m) =
      cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m) := by
  simpa [cglProposition51FirstAxialFrequencyVector, cglProposition51AxialFrequencyVector,
    cglProposition51RotateFrequency] using
    cglProposition51_offDiagonalFrequencyTerm_rotate w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m)

/-- Exact transport from the second `S₁` ray to the closed third-axis coefficient. -/
theorem cglProposition51_secondAxis_term_eq_thirdAxis
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (w : CGLRealSmoothBump) (m : ℤ) :
    cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m) =
      cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m) := by
  calc
    cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m) =
      cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m) := by
      simpa [cglProposition51FirstAxialFrequencyVector, cglProposition51SecondAxialFrequencyVector,
        cglProposition51RotateFrequency] using
        cglProposition51_offDiagonalFrequencyTerm_rotate w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m)
    _ = _ := cglProposition51_firstAxis_term_eq_thirdAxis w m

/-- The absolute punctured-frequency sum on the first `S₁` ray has the same
closed literal source power saving as the third ray. -/
theorem cglProposition51_firstAxis_norm_tsum_le_literalEpsilonSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N)
    (w : CGLRealSmoothBump) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m.val)‖ ≤
      (9 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.epsilonDenominator * 25) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
          cglProposition51PuncturedInverseSquareMass)) /
        S.base ^ (10 : ℕ) := by
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m.val)‖ =
      ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ := by
        apply tsum_congr
        intro m
        exact congrArg norm (cglProposition51_firstAxis_term_eq_thirdAxis w m.val)
    _ ≤ _ := cglProposition51_axialFrequencyTerm_norm_tsum_le_literalEpsilonSourcePower S w

/-- The absolute punctured-frequency sum on the second `S₁` ray has the same
closed literal source power saving as the third ray. -/
theorem cglProposition51_secondAxis_norm_tsum_le_literalEpsilonSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N)
    (w : CGLRealSmoothBump) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m.val)‖ ≤
      (9 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.epsilonDenominator * 25) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
          cglProposition51PuncturedInverseSquareMass)) /
        S.base ^ (10 : ℕ) := by
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m.val)‖ =
      ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖ := by
        apply tsum_congr
        intro m
        exact congrArg norm (cglProposition51_secondAxis_term_eq_thirdAxis w m.val)
    _ ≤ _ := cglProposition51_axialFrequencyTerm_norm_tsum_le_literalEpsilonSourcePower S w

end RHTower
