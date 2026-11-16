import GaloisForLFunctions.HilbertMetric.Probability.BregmanCalibration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Bregman dissipation from a bounded monotone gradient

Symmetrizing a scalar Bregman remainder gives a gradient jump pairing.
The arctangent gradient is a monotone contraction, so its pairing lies
between the squared gradient jump and the squared original jump.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.HilbertMetric.Probability

/-- A convex potential with bounded gradient. -/
def arctanPotential (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, Real.arctan t

theorem deriv_arctanPotential (x : ℝ) : deriv arctanPotential x = Real.arctan x := by
  exact (intervalIntegral.integral_hasDerivAt_right
    (Real.continuous_arctan.intervalIntegrable 0 x)
    Real.continuous_arctan.stronglyMeasurable.stronglyMeasurableAtFilter
    Real.continuous_arctan.continuousAt).deriv

/-- The derivative bound is global, including the origin. -/
theorem arctan_contraction : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro x
  change ‖deriv Real.arctan x‖ ≤ (1 : ℝ)
  rw [Real.deriv_arctan, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (by positivity : 0 ≤ 1 + x ^ 2))]
  exact (div_le_one (by positivity : 0 < 1 + x ^ 2)).mpr (by nlinarith only [sq_nonneg x])

/-- The two tangent remainders cancel their potential values. -/
theorem scalarBregman_symm (φ : ℝ → ℝ) (a b : ℝ) :
    scalarBregman φ a b + scalarBregman φ b a =
      (a - b) * (deriv φ a - deriv φ b) := by
  unfold scalarBregman
  ring

theorem arctanBregman_symm (a b : ℝ) :
    scalarBregman arctanPotential a b + scalarBregman arctanPotential b a =
      (a - b) * (Real.arctan a - Real.arctan b) := by
  rw [scalarBregman_symm, deriv_arctanPotential, deriv_arctanPotential]

/-- Monotonicity and contraction give the two sharp jump comparisons. -/
theorem arctan_jump_bounds (a b : ℝ) :
    (Real.arctan a - Real.arctan b) ^ 2 ≤
        (a - b) * (Real.arctan a - Real.arctan b) ∧
      (a - b) * (Real.arctan a - Real.arctan b) ≤ (a - b) ^ 2 := by
  have hl : |Real.arctan a - Real.arctan b| ≤ |a - b| := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      arctan_contraction.norm_sub_le a b
  rcases le_total b a with h | h
  · have hx := sub_nonneg.mpr h
    have hy := sub_nonneg.mpr (Real.arctan_mono h)
    rw [abs_of_nonneg hx, abs_of_nonneg hy] at hl
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl hy]
    · nlinarith only [mul_le_mul_of_nonneg_left hl hx]
  · have hx := sub_nonpos.mpr h
    have hy := sub_nonpos.mpr (Real.arctan_mono h)
    rw [abs_of_nonpos hx, abs_of_nonpos hy] at hl
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_right hl (neg_nonneg.mpr hy)]
    · nlinarith only [mul_le_mul_of_nonneg_left hl (neg_nonneg.mpr hx)]

#print axioms deriv_arctanPotential
#print axioms arctan_contraction
#print axioms arctanBregman_symm
#print axioms arctan_jump_bounds

end GaloisForLFunctions.HilbertMetric.Probability
end
