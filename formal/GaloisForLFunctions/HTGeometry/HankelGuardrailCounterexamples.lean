import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Finite Hankel positivity counterexamples

Two explicit counterexamples separate coordinate positivity and all-order log-convexity from
positive-semidefiniteness of the corresponding Hankel matrix.  They provide unconditional finite
obstructions to replacing the full moment square-test cone by either weaker condition.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

/-- A strictly entrywise-positive symmetric matrix with a negative determinant. -/
def axisPositiveHankelCounterexample : Matrix (Fin 2) (Fin 2) ℝ := !![1, 3; 3, 1]

/-- Every coordinate of the axis-positive counterexample is strictly positive. -/
theorem axisPositiveHankelCounterexample_entry_pos (i j : Fin 2) :
    0 < axisPositiveHankelCounterexample i j := by
  fin_cases i <;> fin_cases j <;> norm_num [axisPositiveHankelCounterexample]

/-- The axis-positive counterexample has determinant `-8`. -/
theorem axisPositiveHankelCounterexample_det :
    axisPositiveHankelCounterexample.det = -8 := by
  norm_num [axisPositiveHankelCounterexample, Matrix.det_fin_two]

/-- Coordinatewise positivity does not imply positive-semidefiniteness of a Hankel block. -/
theorem axisPositiveHankelCounterexample_not_posSemidef :
    ¬ axisPositiveHankelCounterexample.PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [axisPositiveHankelCounterexample_det] at hdet
  norm_num at hdet

/-- A positive sequence whose adjacent Hankel minors are nonnegative at every order. -/
def allOrderLogConvexCounterexample : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * (5 / 2 : ℝ) ^ n

/-- Every term of `allOrderLogConvexCounterexample` is strictly positive. -/
theorem allOrderLogConvexCounterexample_pos (n : ℕ) :
    0 < allOrderLogConvexCounterexample n := by
  rcases n with _ | n
  · norm_num [allOrderLogConvexCounterexample]
  rcases n with _ | n
  · norm_num [allOrderLogConvexCounterexample]
  simp [allOrderLogConvexCounterexample]

/-- The counterexample is log-convex at every index. -/
theorem allOrderLogConvexCounterexample_logConvex (n : ℕ) :
    allOrderLogConvexCounterexample (n + 1) ^ 2 ≤
      allOrderLogConvexCounterexample n * allOrderLogConvexCounterexample (n + 2) := by
  rcases n with _ | n
  · norm_num [allOrderLogConvexCounterexample]
  rcases n with _ | n
  · norm_num [allOrderLogConvexCounterexample]
  simp only [allOrderLogConvexCounterexample]
  rw [pow_succ, pow_succ]
  ring_nf
  exact le_rfl

/-- The leading three-by-three Hankel block of the all-order log-convex counterexample. -/
def allOrderLogConvexCounterexampleHankel : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => allOrderLogConvexCounterexample ((i : ℕ) + (j : ℕ))

/-- The leading three-by-three determinant is `-1/2`. -/
theorem allOrderLogConvexCounterexampleHankel_det :
    allOrderLogConvexCounterexampleHankel.det = -(1 / 2 : ℝ) := by
  norm_num [allOrderLogConvexCounterexampleHankel, allOrderLogConvexCounterexample,
    Matrix.det_fin_three]

/-- The leading three-by-three Hankel block is not positive semidefinite. -/
theorem allOrderLogConvexCounterexampleHankel_not_posSemidef :
    ¬ allOrderLogConvexCounterexampleHankel.PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [allOrderLogConvexCounterexampleHankel_det] at hdet
  norm_num at hdet

/-- There is a strictly positive, all-order log-convex sequence whose leading three-by-three
Hankel block is not positive semidefinite. -/
theorem exists_positive_logConvex_not_hankelPosSemidef :
    ∃ s : ℕ → ℝ,
      (∀ n, 0 < s n) ∧
      (∀ n, s (n + 1) ^ 2 ≤ s n * s (n + 2)) ∧
      ¬ (Matrix.of fun i j : Fin 3 => s ((i : ℕ) + (j : ℕ))).PosSemidef := by
  refine ⟨allOrderLogConvexCounterexample, allOrderLogConvexCounterexample_pos,
    allOrderLogConvexCounterexample_logConvex, ?_⟩
  simpa [allOrderLogConvexCounterexampleHankel] using
    allOrderLogConvexCounterexampleHankel_not_posSemidef

end

end HTGeometry
