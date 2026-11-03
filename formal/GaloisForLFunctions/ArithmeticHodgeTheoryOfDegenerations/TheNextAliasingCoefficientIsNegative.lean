import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The next coefficient of the tilted-spline aliasing

The periodic numerator has four nonconstant cosine modes. Two integrations
by parts make their averages against compact C² windows smaller than the
quadratic inverse-frequency scale. The next rational-tail coefficient can
therefore be read without an oscillatory term at that scale.
-/

noncomputable section

open MeasureTheory Filter Topology Zeta23
open scoped FourierTransform

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticDegenerationTheory SpacingScaleHarmonicAnalysis

/-- The tilted numerator has precisely four nonconstant cosine modes. -/
theorem splineNumerator_cosine_expansion (x : ℝ) :
    let a := Real.sinh 1 ^ 2 + 1 / 2
    splineNumerator x = a ^ 4 + 3 * a ^ 2 / 4 + 3 / 128 +
      (-2 * a ^ 3 - 3 * a / 8) * Real.cos (2 * x) +
      (3 * a ^ 2 / 4 + 1 / 32) * Real.cos (4 * x) -
      a / 8 * Real.cos (6 * x) + 1 / 128 * Real.cos (8 * x) := by
  have hs : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
    nlinarith only [Real.cos_two_mul x, Real.sin_sq_add_cos_sq x]
  have h4 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul]
  have h6 : Real.cos (6 * x) = 4 * Real.cos (2 * x) ^ 3 - 3 * Real.cos (2 * x) := by
    rw [show 6 * x = 3 * (2 * x) by ring, Real.cos_three_mul]
  have h8 : Real.cos (8 * x) = 2 * Real.cos (4 * x) ^ 2 - 1 := by
    rw [show 8 * x = 2 * (4 * x) by ring, Real.cos_two_mul]
  dsimp only
  rw [splineNumerator, hs, h8, h6, h4]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
