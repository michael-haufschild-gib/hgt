import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Interpolating unweighted and coordinate-square error budgets

The scale is free. Both endpoint budgets are retained, so the estimate applies
to a complete amplitude without diagonalizing its coefficient quadratic form.
-/

noncomputable section
open scoped NNReal
namespace GaloisForLFunctions

/-- A three-halves weight is controlled by the two endpoint weights at any scale. -/
theorem threeHalvesWeight_le_two_endpoint_weights (x : ℝ≥0)
    (L : {L : ℝ // 0 < L}) :
    (x : ℝ) * Real.sqrt x * Real.sqrt (L : ℝ) ≤ (L : ℝ) ^ 2 + (x : ℝ) ^ 2 := by
  rcases le_total (x : ℝ) (L : ℝ) with h | h
  · have hs := Real.sqrt_le_sqrt h
    have hm := mul_le_mul hs le_rfl (Real.sqrt_nonneg (L : ℝ))
      (Real.sqrt_nonneg (L : ℝ))
    rw [← sq, Real.sq_sqrt L.property.le] at hm
    have hp := mul_le_mul h hm (by positivity) L.property.le
    nlinarith only [hp, sq_nonneg (x : ℝ)]
  · have hs := Real.sqrt_le_sqrt h
    have hm := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (x : ℝ))
    rw [← sq, Real.sq_sqrt x.coe_nonneg] at hm
    have hp := mul_le_mul_of_nonneg_left hm x.coe_nonneg
    nlinarith only [hp, sq_nonneg (L : ℝ)]

end GaloisForLFunctions
