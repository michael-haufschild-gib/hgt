import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Relative steps and discrete logarithmic curvature

Positive coordinates are parametrized by their logarithms. The comparison of two
successive percentage gaps is exactly the sign of a second logarithmic difference.
Reflection of values, reversal of order, and reciprocal duality have distinct laws.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators

/-- Relative displacement, with the usual totalized field division. -/
def relativeStep (a b : ℝ) : ℝ := (b - a) / a

/-- Relative displacement in positive logarithmic coordinates. -/
def logRelativeStep (x y : ℝ) : ℝ := Real.exp (y - x) - 1

/-- The second logarithmic difference of three adjacent coordinates. -/
def logStepCurvature (x y z : ℝ) : ℝ := z - 2 * y + x

/-- The denominator-free adjacent Hankel determinant. -/
def stepDeterminant (a b c : ℝ) : ℝ := a * c - b ^ (2 : ℕ)

theorem relativeStep_neg (a b : ℝ) : relativeStep (-a) (-b) = relativeStep a b := by
  unfold relativeStep
  rw [show -b - -a = -(b - a) by ring]
  simp only [neg_div_neg_eq]

theorem relativeStep_exp (x y : ℝ) :
    relativeStep (Real.exp x) (Real.exp y) = logRelativeStep x y := by
  simp [relativeStep, logRelativeStep, sub_div, Real.exp_sub, Real.exp_ne_zero]

theorem logRelativeStep_translate (x y t : ℝ) :
    logRelativeStep (x + t) (y + t) = logRelativeStep x y := by
  unfold logRelativeStep
  congr 2; ring

/-- Multiplicative composition retains the cross term lost by additive gap models. -/
theorem logRelativeStep_compose (x y z : ℝ) :
    logRelativeStep x z = logRelativeStep x y + logRelativeStep y z +
      logRelativeStep x y * logRelativeStep y z := by
  have he : Real.exp (y - x) * Real.exp (z - y) = Real.exp (z - x) := by
    rw [← Real.exp_add]
    congr 1; ring
  unfold logRelativeStep
  nlinarith [he]

/-- Relative acceleration factors into positive scale and exponential curvature. -/
theorem logRelativeStep_difference (x y z : ℝ) :
    logRelativeStep y z - logRelativeStep x y =
      Real.exp (y - x) * (Real.exp (logStepCurvature x y z) - 1) := by
  have he : Real.exp (y - x) * Real.exp (logStepCurvature x y z) =
      Real.exp (z - y) := by
    rw [← Real.exp_add]
    unfold logStepCurvature
    congr 1; ring
  unfold logRelativeStep
  nlinarith [he]

theorem logRelativeStep_lt_iff (x y z : ℝ) :
    logRelativeStep x y < logRelativeStep y z ↔ 0 < logStepCurvature x y z := by
  simp only [logRelativeStep, sub_lt_sub_iff_right, Real.exp_lt_exp]
  unfold logStepCurvature
  constructor <;> intro h <;> linarith

theorem logRelativeStep_le_iff (x y z : ℝ) :
    logRelativeStep x y ≤ logRelativeStep y z ↔ 0 ≤ logStepCurvature x y z := by
  simp only [logRelativeStep, sub_le_sub_iff_right, Real.exp_le_exp]
  unfold logStepCurvature
  constructor <;> intro h <;> linarith

theorem logRelativeStep_eq_iff (x y z : ℝ) :
    logRelativeStep x y = logRelativeStep y z ↔ logStepCurvature x y z = 0 := by
  simp only [logRelativeStep, sub_left_inj, Real.exp_injective.eq_iff]
  unfold logStepCurvature
  constructor <;> intro h <;> linarith

/-- Geometric trends change gap size but preserve every comparison sign. -/
theorem logStepCurvature_affine_gauge (x y z a b : ℝ) :
    logStepCurvature (x + b) (y + a + b) (z + 2 * a + b) =
      logStepCurvature x y z := by
  unfold logStepCurvature
  ring

theorem logStepCurvature_reverse (x y z : ℝ) :
    logStepCurvature z y x = logStepCurvature x y z := by
  unfold logStepCurvature
  ring

/-- Reciprocating positive values negates logarithmic curvature. -/
theorem logStepCurvature_reciprocal (x y z : ℝ) :
    logStepCurvature (-x) (-y) (-z) = -logStepCurvature x y z := by
  unfold logStepCurvature
  ring

theorem logRelativeStep_reciprocal_order (x y z : ℝ) :
    logRelativeStep (-x) (-y) < logRelativeStep (-y) (-z) ↔
      logRelativeStep y z < logRelativeStep x y := by
  simp only [logRelativeStep, sub_lt_sub_iff_right, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Reversing the entire three-point path preserves its expansion/contraction comparison. -/
theorem logRelativeStep_reverse_order (x y z : ℝ) :
    logRelativeStep z y < logRelativeStep y x ↔
      logRelativeStep x y < logRelativeStep y z := by
  rw [logRelativeStep_lt_iff, logRelativeStep_lt_iff, logStepCurvature_reverse]

theorem stepDeterminant_neg (a b c : ℝ) :
    stepDeterminant (-a) (-b) (-c) = stepDeterminant a b c := by
  unfold stepDeterminant
  ring

theorem stepDeterminant_scale (a b c t : ℝ) :
    stepDeterminant (t * a) (t * b) (t * c) = t ^ (2 : ℕ) * stepDeterminant a b c := by
  unfold stepDeterminant
  ring

/-- Adding a baseline changes the determinant through the ordinary second difference. -/
theorem stepDeterminant_translate (a b c t : ℝ) :
    stepDeterminant (a + t) (b + t) (c + t) =
      stepDeterminant a b c + t * (c - 2 * b + a) := by
  unfold stepDeterminant
  ring

/-- Every complete block of curvature is an endpoint slope difference. -/
theorem sum_logStepCurvature (u : ℕ → ℝ) (start count : ℕ) :
    (∑ k ∈ Finset.range count,
      logStepCurvature (u (start + k)) (u (start + k + 1)) (u (start + k + 2))) =
      (u (start + count + 1) - u (start + count)) - (u (start + 1) - u start) := by
  induction count with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_assoc]
    unfold logStepCurvature
    ring

end
end GaloisForLFunctions.HTGeometry
