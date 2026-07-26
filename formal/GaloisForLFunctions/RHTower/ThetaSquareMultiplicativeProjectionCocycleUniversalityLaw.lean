import GaloisForLFunctions.RHTower.XiThetaBoundaryCoboundary

/-!
# Theta-square multiplicative projection-cocycle universality

Square-rate theta atoms turn multiplication of positive indices into addition of logarithmic
translations.  Their physical `m⁻¹/²` weight transports the additive moving-boundary cocycle to an
exact multiplicative-index cocycle.

The resulting charge is simultaneously the correction in the positive-truncation theta seam and a
weighted conjugation coboundary of the fixed positive-half projection.  Hence composite square
indices create no extra seam curvature.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- Weighted positive-half boundary charge of the `m`th square-rate theta atom. -/
def thetaSquarePositiveBoundaryCharge (m : ℕ) (u : ℝ) : ℝ :=
  (m : ℝ) ^ (-(1 : ℝ) / 2) *
    forwardTranslationBoundary (2 * Real.log m) thetaLogMother u

/-- Each weighted square-index boundary charge is exactly a weighted conjugation coboundary of
the fixed positive-half projection. -/
theorem thetaSquarePositiveBoundaryCharge_eq_projectionConjugationDefect
    {m : ℕ} (hm : 1 < m) (u : ℝ) :
    thetaSquarePositiveBoundaryCharge m u =
      (m : ℝ) ^ (-(1 : ℝ) / 2) *
        positiveProjectionConjugationDefect (2 * Real.log m)
          (forwardLogTranslate (2 * Real.log m) thetaLogMother) u := by
  rw [thetaSquarePositiveBoundaryCharge,
    thetaSquareForwardBoundary_eq_conjugationDefect hm u]

/-- The same weighted charge is precisely the correction that intertwines positive truncation
with the actual square-rate theta atom. -/
theorem positiveThetaSquareLogAtom_add_boundaryCharge
    {m : ℕ} (hm : 1 < m) (u : ℝ) :
    positiveLogTruncation (thetaSquareLogAtom m) u +
        thetaSquarePositiveBoundaryCharge m u =
      (m : ℝ) ^ (-(1 : ℝ) / 2) *
        positiveLogTruncation thetaLogMother (u + 2 * Real.log m) := by
  simpa only [thetaSquarePositiveBoundaryCharge] using
    positiveThetaSquareLogAtom_translation_seam hm u

/-- **Theta-square multiplicative projection-cocycle law.**  Multiplication of square indices
composes their weighted moving boundaries through the additive logarithmic-translation cocycle.
The coefficient is exactly the product of the two physical theta weights. -/
theorem thetaSquarePositiveBoundaryCharge_mul
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (u : ℝ) :
    thetaSquarePositiveBoundaryCharge (m * n) u =
      (m : ℝ) ^ (-(1 : ℝ) / 2) * (n : ℝ) ^ (-(1 : ℝ) / 2) *
        (forwardTranslationBoundary (2 * Real.log m)
            (forwardLogTranslate (2 * Real.log n) thetaLogMother) u +
          forwardLogTranslate (2 * Real.log m)
            (forwardTranslationBoundary (2 * Real.log n) thetaLogMother) u) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hmnonneg : (0 : ℝ) ≤ m := by positivity
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  rw [thetaSquarePositiveBoundaryCharge, Nat.cast_mul,
    Real.mul_rpow hmnonneg hnnonneg, Real.log_mul hm0 hn0]
  rw [show 2 * (Real.log (m : ℝ) + Real.log (n : ℝ)) =
      2 * Real.log m + 2 * Real.log n by ring]
  rw [forwardTranslationBoundary_add thetaLogMother
    (mul_pos (by norm_num) (Real.log_pos hmR))
    (mul_pos (by norm_num) (Real.log_pos hnR)) u]

end RHTower
