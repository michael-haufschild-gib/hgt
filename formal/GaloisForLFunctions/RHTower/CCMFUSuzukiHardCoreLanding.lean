import GaloisForLFunctions.RHTower.CCMFUSuzukiAdaptiveCofinalLanding
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedQuantileTransport

/-!
# Source-adaptive Suzuki landing on the CCM-FU hard currents

The explicit variation-adaptive positive Suzuki producer differs by at most `exp 1 / (2 * H^2)`
from each of the two exact source-level frontier coordinates already isolated in the corpus: the
matched-coverage decomposition and the completed quantile-transport decomposition.  At lower wall
one, uniform boundedness of the finite Suzuki producer is equivalent to uniform boundedness of
either hard current.
-/

open Filter Topology MeasureTheory

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Quantitative source-faithful landing on the matched-coverage core.  Local quadrature, outgoing
coverage, and incoming polar terms remain assembled before taking the absolute value. -/
theorem abs_sourceAdaptivePositiveLogChord_sub_matchedCoverageCore_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hH1 : 1 ≤ H) :
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H
          (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H) -
        (ccmThirdGradeCesaroPhysicalMatchedQuadratureBlock b H +
          ccmThirdGradeCesaroMatchedCoverageSeam b H -
            ccmThirdGradeCesaroIncomingPolarTail b H)| ≤
      Real.exp 1 / (2 * H ^ 2) := by
  rw [← ccmGuinandWeilPrimePolarTriangularWindow_eq_matchedBlock_add_coverageSeam_sub_incoming
    hb hbH]
  exact abs_positiveLogChordSourceAdaptiveApprox_sub_literal_le hb hbH hH1

/-- Quantitative source-faithful landing on the completed oriented quantile current.  Internal and
terminal transports remain coupled through the completed transport coordinate. -/
theorem abs_sourceAdaptivePositiveLogChord_sub_completedQuantileCore_le
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (hH1 : 1 ≤ H) :
    |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox b H
          (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock b H) -
        (ccmThirdGradeCesaroCompletedQuantileTransport b H -
          ccmThirdGradeCesaroLowerOutgoingCorrection b H -
            ccmThirdGradeCesaroIncomingPolarTail b H)| ≤
      Real.exp 1 / (2 * H ^ 2) := by
  rw [← GaloisForLFunctions.RHTower.ccmGuinandWeilPrimePolarTriangularWindow_eq_completedQuantileTransport
    hb hbH]
  exact abs_positiveLogChordSourceAdaptiveApprox_sub_literal_le hb hbH hH1

/-- At the canonical base wall, uniform boundedness of the actual finite Suzuki producer is exactly
uniform boundedness of the sole outgoing matched-coverage seam. -/
theorem uniformlyBounded_sourceAdaptivePositiveLogChord_iff_matchedCoverageSeam :
    (∃ C : ℝ, ∀ H : ℝ, 1 ≤ H →
      |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox 1 H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock 1 H)| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, 1 ≤ H →
      |ccmThirdGradeCesaroMatchedCoverageSeam 1 H| ≤ C) := by
  have hA := uniformlyBounded_sourceAdaptivePositiveLogChord_iff_literal
    (b := (1 : ℝ)) (by norm_num)
  simp only [max_self] at hA
  exact hA.trans
    (uniformlyBounded_primePolarTriangularWindow_iff_matchedCoverageSeam
      (b := (1 : ℝ)) (by norm_num))

/-- At the canonical base wall, uniform boundedness of the actual finite Suzuki producer is exactly
uniform boundedness of the completed oriented quantile current. -/
theorem uniformlyBounded_sourceAdaptivePositiveLogChord_iff_completedQuantileTransport :
    (∃ C : ℝ, ∀ H : ℝ, 1 ≤ H →
      |ccmFUSuzukiPositiveConnectedLogChordTriangularCompletedApprox 1 H
        (ccmFUSuzukiPositiveLogChordSourceAdaptiveClock 1 H)| ≤ C) ↔
    (∃ C : ℝ, ∀ H : ℝ, 1 ≤ H →
      |ccmThirdGradeCesaroCompletedQuantileTransport 1 H| ≤ C) := by
  have hA := uniformlyBounded_sourceAdaptivePositiveLogChord_iff_literal
    (b := (1 : ℝ)) (by norm_num)
  simp only [max_self] at hA
  exact hA.trans
    (GaloisForLFunctions.RHTower.uniformlyBounded_primePolarTriangularWindow_iff_completedQuantileTransport
      (b := (1 : ℝ)) (by norm_num))

end

end RHTower
