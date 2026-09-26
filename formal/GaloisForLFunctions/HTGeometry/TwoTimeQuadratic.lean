import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The negative two-coordinate quadratic form

The diagonal form with two negative signs is negative definite. Its sum and
difference coordinates also distinguish simultaneous motion from opposing
motion: simultaneous translation preserves the difference, while opposing
translation preserves the sum.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- The diagonal quadratic form with two negative directions. -/
def twoTimeQuadratic (p : ℝ × ℝ) : ℝ := -(p.1 ^ (2 : ℕ) + p.2 ^ (2 : ℕ))

/-- The diagonal tensor with two negative entries. -/
def twoTimeMetricMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -1]

/-- Matrix evaluation recovers the two-negative-direction quadratic form. -/
theorem twoTimeMetricMatrix_quadratic (v : Fin 2 → ℝ) :
    dotProduct v (twoTimeMetricMatrix.mulVec v) =
      twoTimeQuadratic (v 0, v 1) := by
  simp [twoTimeMetricMatrix, twoTimeQuadratic, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The form is nonpositive on every pair. -/
theorem twoTimeQuadratic_nonpos (p : ℝ × ℝ) : twoTimeQuadratic p ≤ 0 := by
  unfold twoTimeQuadratic
  nlinarith [sq_nonneg p.1, sq_nonneg p.2]

/-- The only null vector of the two-negative-direction form is zero. -/
theorem twoTimeQuadratic_eq_zero_iff (p : ℝ × ℝ) :
    twoTimeQuadratic p = 0 ↔ p = (0, 0) := by
  constructor
  · intro h
    have hx : p.1 = 0 := by
      unfold twoTimeQuadratic at h
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    have hy : p.2 = 0 := by
      unfold twoTimeQuadratic at h
      nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    exact Prod.ext hx hy
  · intro h
    rw [h]
    simp [twoTimeQuadratic]

/-- Sum and difference coordinates diagonalize the same negative form. -/
theorem twoTimeQuadratic_sum_difference (p : ℝ × ℝ) :
    twoTimeQuadratic p =
      -((p.1 + p.2) ^ (2 : ℕ) + (p.1 - p.2) ^ (2 : ℕ)) / 2 := by
  unfold twoTimeQuadratic
  ring

/-- Equal translation of both coordinates preserves their difference. -/
theorem simultaneousShift_difference (p : ℝ × ℝ) (t : ℝ) :
    (p.1 + t) - (p.2 + t) = p.1 - p.2 := by
  ring

/-- Opposing translation preserves the sum, rather than the difference. -/
theorem opposingShift_sum (p : ℝ × ℝ) (t : ℝ) :
    (p.1 + t) + (p.2 - t) = p.1 + p.2 := by
  ring

/-- The two-negative-direction form changes under simultaneous translation. -/
theorem twoTimeQuadratic_simultaneousShift (p : ℝ × ℝ) (t : ℝ) :
    twoTimeQuadratic (p.1 + t, p.2 + t) =
      twoTimeQuadratic p - 2 * t * (p.1 + p.2) - 2 * t ^ (2 : ℕ) := by
  unfold twoTimeQuadratic
  ring

end GaloisForLFunctions.HTGeometry
