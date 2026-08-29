import GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAbelCompleteness
import GaloisForLFunctions.PNTPlus.Auxiliary

/-!
# Concrete compact-Weil close-pair collision

The generic close-pair derivative law requires differentiability because arbitrary
Hilbert-valued functions need not be differentiable. This module discharges that obligation for
the corpus-owned compactly supported Guinand--Weil polar Laplace profile. Its compact-support
integral construction proves complex differentiability at every point; restriction to the real
spectral axis therefore supplies the derivative internally.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- Compact-support polar Laplace profile restricted to the real spectral axis. -/
def ccmGuinandWeilPolarCompactLaplaceReal (x : ℝ) : ℂ :=
  ccmGuinandWeilPolarCompactLaplace 1 x

/-- The two-channel Hilbert decomposition for the actual compact-Weil profile. -/
theorem ccmGuinandWeilPolarCompactLaplaceReal_samplingEnergy_split (x h : ℝ) :
    compactWeilClosePairSamplingEnergy ccmGuinandWeilPolarCompactLaplaceReal x h =
      (1 / 2 : ℝ) *
          ‖ccmGuinandWeilPolarCompactLaplaceReal x +
            ccmGuinandWeilPolarCompactLaplaceReal (x + h)‖ ^ 2 +
        (1 / 2 : ℝ) *
          compactWeilClosePairDifferenceEnergy ccmGuinandWeilPolarCompactLaplaceReal x h := by
  exact compactWeilClosePair_samplingEnergy_split _ _ _

/-- Exact reporter collision for the actual compact-Weil profile. -/
theorem ccmGuinandWeilPolarCompactLaplaceReal_samplingEnergy_collision (x : ℝ) :
    compactWeilClosePairSamplingEnergy ccmGuinandWeilPolarCompactLaplaceReal x 0 =
      2 * ‖ccmGuinandWeilPolarCompactLaplaceReal x‖ ^ 2 := by
  exact compactWeilClosePair_samplingEnergy_collision _ _

/-- The actual compact-Weil profile is differentiable; no differentiability premise remains. -/
theorem differentiableAt_ccmGuinandWeilPolarCompactLaplaceReal (x : ℝ) :
    DifferentiableAt ℝ ccmGuinandWeilPolarCompactLaplaceReal x := by
  have hcomplex : DifferentiableAt ℂ (ccmGuinandWeilPolarCompactLaplace 1) (x : ℂ) :=
    differentiableAt_ccmGuinandWeilPolarCompactLaplace (by norm_num) _
  exact hcomplex.comp_ofReal

/-- Unconditional quadratic collision law for the actual compact-Weil profile. -/
theorem tendsto_ccmGuinandWeilPolarCompactLaplaceReal_differenceEnergy_div_sq (x : ℝ) :
    Tendsto
      (fun h : ℝ =>
        compactWeilClosePairDifferenceEnergy ccmGuinandWeilPolarCompactLaplaceReal x h / h ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (‖deriv ccmGuinandWeilPolarCompactLaplaceReal x‖ ^ 2)) := by
  exact tendsto_compactWeilClosePair_differenceEnergy_div_sq
    (differentiableAt_ccmGuinandWeilPolarCompactLaplaceReal x).hasDerivAt

end RHTower
