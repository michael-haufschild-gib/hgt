/-
# Chen--Gupta--Li Lemma 4.5

The exact cubic trace expansion together with its literal real-parameter
zero-frequency error certificate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45OffDiagonalSplit
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45RealSourceScale

noncomputable section

namespace RHTower

open scoped BigOperators

/-- **Chen--Gupta--Li, Lemma 4.5.** For a certified finite packet in the
literal real `qT`/`ε` regime, the cubic trace has the paper's diagonal,
nonzero-frequency, and zero-frequency decomposition; the latter carries the
explicit `X⁻¹⁰⁰` bound obtained from the source separation. -/
theorem cglLemma45_literalEpsilon_expansion_and_zeroBound
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) (w : CGLRealSmoothBump) :
    cglCharacterDyadicWeightedGramCubicTrace N.value (q + 1) R
        (cglSmoothBumpDyadicWeight w.toCGLSmoothBump N) (cglLemma45FibreRows P) =
      (R : ℂ) * cglLemma45DiagonalPoissonMass w N (cglLemma45FibreModulus q) ^ (3 : ℕ) +
        cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) 0 +
        ∑' m : {m : (ℤ × ℤ) × ℤ // m ∉ ({0} : Finset ((ℤ × ℤ) × ℤ))},
          cglLemma45OffDiagonalNonzeroFrequencyTerm w N (cglLemma45FibreModulus q) R
            (cglLemma45FibreRows P) m ∧
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.epsilonDenominator * 115) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          S.base ^ (100 : ℕ) := by
  constructor
  · exact cglLemma45_cubicTrace_eq_diagonal_add_zeroOffDiagonal_add_nonzero w N
      (cglLemma45FibreModulus q) R (cglLemma45FibreRows P)
  · simpa using
      norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_literalEpsilonSourcePower S w 100

end RHTower
