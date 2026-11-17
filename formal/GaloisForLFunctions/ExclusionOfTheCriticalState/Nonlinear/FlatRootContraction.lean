import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexPotential

/-!
# The square-root flat potential is a contraction

The inequality `gradient² ≤ 2 potential` and the quadratic tangent bound
show that `sqrt (2 potential)` is globally 1-Lipschitz. This makes the
square-root control in §2.4 of arXiv:2611.08616 explicit and supplies another
nonlinear half-line energy test fixing zero.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- Normalization making the square-root potential a unit contraction. -/
def rootPotential (t : ℝ) : ℝ := Real.sqrt (2 * potential t)

theorem rootPotential_nonneg (t : ℝ) : 0 ≤ rootPotential t := Real.sqrt_nonneg _

theorem rootPotential_sq (t : ℝ) : rootPotential t ^ 2 = 2 * potential t :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (potential_bounds t).1)

@[simp] theorem rootPotential_zero : rootPotential 0 = 0 := by
  simp only [rootPotential, potential_zero, mul_zero, Real.sqrt_zero]

/-- The flat gradient is pointwise dominated by the square-root test. -/
theorem gradient_le_rootPotential (t : ℝ) : gradient t ≤ rootPotential t := by
  nlinarith only [gradient_square_le t, rootPotential_sq t,
    gradient_nonneg t, rootPotential_nonneg t]

private theorem rootPotential_upper (x y : ℝ) : rootPotential x ≤ rootPotential y + |x - y| := by
  have h₁ := mul_le_mul_of_nonneg_left (le_abs_self (x - y)) (gradient_nonneg y)
  have h₂ := mul_le_mul_of_nonneg_right (gradient_le_rootPotential y) (abs_nonneg (x - y))
  have hsq : rootPotential x ^ 2 ≤ (rootPotential y + |x - y|) ^ 2 := by
    nlinarith only [(tangent_error_bounds x y).2, h₁, h₂, rootPotential_sq x,
      rootPotential_sq y, sq_abs (x - y)]
  nlinarith only [hsq, rootPotential_nonneg x,
    add_nonneg (rootPotential_nonneg y) (abs_nonneg (x - y))]

/-- The square root retains a global unit Lipschitz bound across the flat junction. -/
theorem rootPotential_contraction : LipschitzWith 1 rootPotential := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  apply abs_le.mpr
  have hxy := rootPotential_upper x y
  have hyx := rootPotential_upper y x
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith only [hxy, hyx]

/-- Both nonlinear tests are controlled by the original amplitude. -/
theorem gradient_rootPotential_bounds (t : ℝ) :
    0 ≤ gradient t ∧ gradient t ≤ rootPotential t ∧ rootPotential t ≤ |t| := by
  refine ⟨gradient_nonneg t, gradient_le_rootPotential t, ?_⟩
  simpa only [rootPotential_zero, zero_add, sub_zero] using rootPotential_upper t 0

#print axioms rootPotential_sq
#print axioms gradient_le_rootPotential
#print axioms rootPotential_contraction
#print axioms gradient_rootPotential_bounds
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
