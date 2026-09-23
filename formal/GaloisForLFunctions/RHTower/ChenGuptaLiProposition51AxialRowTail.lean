/-
# Chen--Gupta--Li Proposition 5.1 axial row tail

Sums the pointwise cubic-modulus row estimate over all nonzero axial
frequencies.  The result keeps the exact closed one-dimensional Fourier-tail
mass, ready for the finite equal-character triple aggregation.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51AxialRowBound

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The norm family of one surviving equal-character axial row triple is
summable over punctured integer frequencies. -/
theorem cglProposition51_axialRowTerm_norm_summable
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) u.1 m.val‖ := by
  let C : ℝ := ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
    cglProposition51FibreAxialAnalyticBudget P w N n
  have hmajor := (cglProposition51_axialFrequencyTail_summable w N
    (cglLemma45FibreModulus q) (P.ordinate u.1.2.2 - P.ordinate u.1.1)).mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hmajor
  simpa [C, mul_assoc] using norm_cglProposition51AxialRowTerm_fibre_le P w N n u m

/-- The absolute nonzero-frequency sum of one surviving equal-character axial
row triple is bounded by its cubic modulus factor times the certified analytic
budget and exact Fourier-tail mass. -/
theorem cglProposition51_axialRowTerm_tsum_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    ∑' m : CGLProposition51PuncturedFrequency,
      ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) u.1 m.val‖ ≤
      ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
        cglProposition51FibreAxialAnalyticBudget P w N n *
          cglProposition51AxialFrequencyTailMass w N (cglLemma45FibreModulus q)
            (P.ordinate u.1.2.2 - P.ordinate u.1.1) := by
  let C : ℝ := ((cglLemma45FibreModulus q).value : ℝ) ^ (3 : ℕ) *
    cglProposition51FibreAxialAnalyticBudget P w N n
  have hmajor := (cglProposition51_axialFrequencyTail_summable w N
    (cglLemma45FibreModulus q) (P.ordinate u.1.2.2 - P.ordinate u.1.1)).mul_left C
  have hleft := cglProposition51_axialRowTerm_norm_summable P w N n u
  calc
    ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglProposition51AxialRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) u.1 m.val‖ ≤
      ∑' m : CGLProposition51PuncturedFrequency,
        C * ‖cglProposition51AxialNonzeroFourierAmplitude w N
          (cglLemma45FibreModulus q) (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖ :=
        hleft.tsum_le_tsum (fun m => by
          simpa [C, mul_assoc] using norm_cglProposition51AxialRowTerm_fibre_le P w N n u m) hmajor
    _ = C * ∑' m : CGLProposition51PuncturedFrequency,
        ‖cglProposition51AxialNonzeroFourierAmplitude w N
          (cglLemma45FibreModulus q) (P.ordinate u.1.2.2 - P.ordinate u.1.1) m‖ :=
        tsum_mul_left
    _ = _ := by rfl

end RHTower
