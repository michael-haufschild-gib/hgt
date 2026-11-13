import GaloisForLFunctions.HTGeometry.AtomicJumpForm

/-!
# Positive levels relative to a positive barrier

Changing to the quotient by a positive barrier preserves monotonicity of
level truncation. The resulting two-point inequality controls prime rows,
while an exact difference identity separates the Gamma jump correction.
-/

set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry

/-- A positive barrier commutes with truncation after dividing by its value. -/
theorem barrier_mul_truncPos {p : ℝ} (hp : 0 < p) (t x : ℝ) :
    p * truncPos t (x / p) = max (x - t * p) 0 := by
  unfold truncPos
  by_cases h : 0 ≤ x - t * p
  · have hh : 0 ≤ x / p - t := by
      apply sub_nonneg.mpr
      exact (le_div_iff₀ hp).mpr (by linarith only [h])
    rw [max_eq_left h, max_eq_left hh]
    field_simp [hp.ne']
    ring
  · have hx : x - t * p ≤ 0 := (lt_of_not_ge h).le
    have hh : x / p - t ≤ 0 := by
      apply sub_nonpos.mpr
      exact (div_le_iff₀ hp).mpr (by linarith only [hx])
    rw [max_eq_right hx, max_eq_right hh, mul_zero]

/-- The mixed edge is bounded by the diagonal row in positive-barrier coordinates. -/
theorem weighted_positiveLevel_row {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (t x y : ℝ) :
    x * max (y - t * q) 0 + y * max (x - t * p) 0 ≤
      x * max (x - t * p) 0 * (q / p) +
        y * max (y - t * q) 0 * (p / q) := by
  have hmono : 0 ≤ (x / p - y / q) * (truncPos t (x / p) - truncPos t (y / q)) :=
    (sq_nonneg _).trans (sub_mul_truncPos_sub_ge t (x / p) (y / q))
  have hpositive := mul_nonneg (mul_pos hp hq).le hmono
  rw [← barrier_mul_truncPos hp, ← barrier_mul_truncPos hq]
  have he :
      x * (p * truncPos t (x / p)) * (q / p) +
        y * (q * truncPos t (y / q)) * (p / q) -
        (x * (q * truncPos t (y / q)) + y * (p * truncPos t (x / p))) =
      (p * q) * ((x / p - y / q) * (truncPos t (x / p) - truncPos t (y / q))) := by
    field_simp [hp.ne', hq.ne']
    ring
  linarith only [he, hpositive]

/-- Exact separation of the relative jump from the barrier correction. -/
theorem weighted_positiveLevel_jump {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (t x y : ℝ) :
    (x - y) * (max (x - t * p) 0 - max (y - t * q) 0) =
      p * q * ((x / p - y / q) * (truncPos t (x / p) - truncPos t (y / q))) +
      (p - q) * (x * max (x - t * p) 0 / p - y * max (y - t * q) 0 / q) := by
  rw [← barrier_mul_truncPos hp, ← barrier_mul_truncPos hq]
  field_simp [hp.ne', hq.ne']
  ring

/-- The relative jump is nonnegative, so only the barrier correction can lower the mixed jump. -/
theorem weighted_positiveLevel_jump_lower {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (t x y : ℝ) :
    (p - q) * (x * max (x - t * p) 0 / p - y * max (y - t * q) 0 / q) ≤
      (x - y) * (max (x - t * p) 0 - max (y - t * q) 0) := by
  rw [weighted_positiveLevel_jump hp hq]
  have hmono : 0 ≤ (x / p - y / q) * (truncPos t (x / p) - truncPos t (y / q)) :=
    (sq_nonneg _).trans (sub_mul_truncPos_sub_ge t (x / p) (y / q))
  exact le_add_of_nonneg_left (mul_nonneg (mul_pos hp hq).le hmono)

#print axioms weighted_positiveLevel_row
#print axioms weighted_positiveLevel_jump_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
