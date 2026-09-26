import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exterior Euler factors and their phase-independent velocity bounds

The radius `1 + exp x` ranges over the exterior of the unit circle without
requiring a domain hypothesis.  The radial logarithmic velocity of an Euler
factor splits into one half plus one half of a reciprocal Poisson kernel.
For two exterior radii, their product controls a stronger uniform bound;
the exact excess is a positive factored expression.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A global coordinate on exterior radii. -/
def exteriorEulerRadius (x : ℝ) : ℝ := 1 + Real.exp x

/-- Squared distance from an exterior radial point to a unit phase. -/
def exteriorEulerDenom (x θ : ℝ) : ℝ :=
  exteriorEulerRadius x ^ 2 - 2 * exteriorEulerRadius x * Real.cos θ + 1

/-- Positive radial logarithmic speed of one exterior Euler factor. -/
def exteriorEulerSpeed (x θ : ℝ) : ℝ :=
  (exteriorEulerRadius x ^ 2 - exteriorEulerRadius x * Real.cos θ) /
    exteriorEulerDenom x θ

/-- Poisson kernel at the reciprocal radius, in real phase coordinates. -/
def exteriorEulerPoisson (x θ : ℝ) : ℝ :=
  (exteriorEulerRadius x ^ 2 - 1) / exteriorEulerDenom x θ

theorem exteriorEulerRadius_gt_one (x : ℝ) : 1 < exteriorEulerRadius x := by
  simpa [exteriorEulerRadius] using Real.exp_pos x

theorem exteriorEulerDenom_pos (x θ : ℝ) : 0 < exteriorEulerDenom x θ := by
  have hr := exteriorEulerRadius_gt_one x
  have hphase := mul_nonneg (show 0 ≤ 2 * exteriorEulerRadius x by linarith)
    (sub_nonneg.mpr (Real.cos_le_one θ))
  have hsquare := sq_pos_of_pos (show 0 < exteriorEulerRadius x - 1 by linarith)
  unfold exteriorEulerDenom
  nlinarith

/-- The half-unit baseline is exactly complemented by Poisson mass. -/
theorem exteriorEulerSpeed_eq_half_add_poisson (x θ : ℝ) :
    exteriorEulerSpeed x θ = (1 + exteriorEulerPoisson x θ) / 2 := by
  unfold exteriorEulerSpeed exteriorEulerPoisson
  field_simp [(exteriorEulerDenom_pos x θ).ne']
  unfold exteriorEulerDenom
  ring

theorem exteriorEulerPoisson_pos (x θ : ℝ) : 0 < exteriorEulerPoisson x θ := by
  apply div_pos _ (exteriorEulerDenom_pos x θ)
  have hr := exteriorEulerRadius_gt_one x
  nlinarith

theorem exteriorEulerSpeed_gt_half (x θ : ℝ) : 1 / 2 < exteriorEulerSpeed x θ := by
  rw [exteriorEulerSpeed_eq_half_add_poisson]
  linarith [exteriorEulerPoisson_pos x θ]

/-- Exact distance from the slowest phase, attained at phase pi. -/
theorem exteriorEulerSpeed_sub_min (x θ : ℝ) :
    exteriorEulerSpeed x θ - exteriorEulerRadius x / (exteriorEulerRadius x + 1) =
      exteriorEulerRadius x * (exteriorEulerRadius x - 1) * (1 + Real.cos θ) /
        (exteriorEulerDenom x θ * (exteriorEulerRadius x + 1)) := by
  have hr := exteriorEulerRadius_gt_one x
  unfold exteriorEulerSpeed
  field_simp [(exteriorEulerDenom_pos x θ).ne',
    show exteriorEulerRadius x + 1 ≠ 0 by linarith]
  unfold exteriorEulerDenom
  ring

theorem exteriorEulerSpeed_min_le (x θ : ℝ) :
    exteriorEulerRadius x / (exteriorEulerRadius x + 1) ≤ exteriorEulerSpeed x θ := by
  have hr := exteriorEulerRadius_gt_one x
  have hphase : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have h := div_nonneg
    (mul_nonneg (mul_nonneg (show 0 ≤ exteriorEulerRadius x by linarith)
      (show 0 ≤ exteriorEulerRadius x - 1 by linarith)) hphase)
    (mul_nonneg (exteriorEulerDenom_pos x θ).le
      (show 0 ≤ exteriorEulerRadius x + 1 by linarith))
  rw [← exteriorEulerSpeed_sub_min] at h
  linarith

/-- The extremal phase is attained, not merely an estimate. -/
theorem exteriorEulerSpeed_pi (x : ℝ) :
    exteriorEulerSpeed x Real.pi = exteriorEulerRadius x / (exteriorEulerRadius x + 1) := by
  have h := exteriorEulerSpeed_sub_min x Real.pi
  simp only [Real.cos_pi, add_neg_cancel, mul_zero, zero_div] at h
  exact sub_eq_zero.mp h

/-- The product-only floor has an explicit strictly positive surplus. -/
theorem exteriorEuler_pair_min_excess (x y : ℝ) :
    exteriorEulerRadius x / (exteriorEulerRadius x + 1) +
        exteriorEulerRadius y / (exteriorEulerRadius y + 1) -
        (3 * (exteriorEulerRadius x * exteriorEulerRadius y) + 1) /
          (2 * (exteriorEulerRadius x * exteriorEulerRadius y + 1)) =
      (exteriorEulerRadius x - 1) * (exteriorEulerRadius y - 1) *
          (exteriorEulerRadius x * exteriorEulerRadius y - 1) /
        (2 * (exteriorEulerRadius x + 1) * (exteriorEulerRadius y + 1) *
          (exteriorEulerRadius x * exteriorEulerRadius y + 1)) := by
  have hx := exteriorEulerRadius_gt_one x
  have hy := exteriorEulerRadius_gt_one y
  have hxy : 0 < exteriorEulerRadius x * exteriorEulerRadius y :=
    mul_pos (by linarith) (by linarith)
  field_simp [show exteriorEulerRadius x + 1 ≠ 0 by linarith,
    show exteriorEulerRadius y + 1 ≠ 0 by linarith,
    show exteriorEulerRadius x * exteriorEulerRadius y + 1 ≠ 0 by linarith]
  ring

/-- Two exterior factors beat a floor determined solely by their radial product,
even when their phases are unrelated. -/
theorem exteriorEuler_pair_product_floor (x y θ φ : ℝ) :
    (3 * (exteriorEulerRadius x * exteriorEulerRadius y) + 1) /
        (2 * (exteriorEulerRadius x * exteriorEulerRadius y + 1)) <
      exteriorEulerSpeed x θ + exteriorEulerSpeed y φ := by
  have hx := exteriorEulerRadius_gt_one x
  have hy := exteriorEulerRadius_gt_one y
  have hxy : 1 < exteriorEulerRadius x * exteriorEulerRadius y := by nlinarith
  have hnum : 0 < (exteriorEulerRadius x - 1) * (exteriorEulerRadius y - 1) *
      (exteriorEulerRadius x * exteriorEulerRadius y - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hden : 0 < 2 * (exteriorEulerRadius x + 1) * (exteriorEulerRadius y + 1) *
      (exteriorEulerRadius x * exteriorEulerRadius y + 1) := by positivity
  have hexcess := div_pos hnum hden
  rw [← exteriorEuler_pair_min_excess] at hexcess
  linarith [exteriorEulerSpeed_min_le x θ, exteriorEulerSpeed_min_le y φ]

/-- The polynomial cancellation underlying the dyadic prefactor identity. -/
theorem dyadicEuler_grand_cancellation (y C : ℝ) :
    (2 * y * C - 4) * (y ^ 2 - 2 * y * C + 1) +
        (y * C - y ^ 2) * (y ^ 2 - 4 * y * C + 4) +
        (y ^ 2 - 4 * y * C + 4) * (y ^ 2 - 2 * y * C + 1) =
      y * (C * y ^ 2 - 3 * y + 2 * C) := by ring

end

end GaloisForLFunctions.HTGeometry
