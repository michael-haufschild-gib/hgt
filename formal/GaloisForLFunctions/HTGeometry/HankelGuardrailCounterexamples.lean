import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

/-- A strictly positive coefficient sequence with a convergent power series near the origin. -/
def positiveCoefficientCounterexample (n : ℕ) : ℝ := if n = 1 then 3 else 1

/-- Every coefficient of `positiveCoefficientCounterexample` is strictly positive. -/
theorem positiveCoefficientCounterexample_pos (n : ℕ) :
    0 < positiveCoefficientCounterexample n := by
  simp [positiveCoefficientCounterexample]
  split <;> norm_num

/-- The counterexample's power series converges at the positive point `1/2`. -/
theorem positiveCoefficientCounterexample_summable_half :
    Summable (fun n : ℕ => positiveCoefficientCounterexample n * (1 / 2 : ℝ) ^ n) := by
  have hgeom : Summable (fun n : ℕ => (3 : ℝ) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by norm_num)).mul_left 3
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
  · exact mul_nonneg (positiveCoefficientCounterexample_pos n).le (by positivity)
  · have ha : positiveCoefficientCounterexample n ≤ 3 := by
      simp [positiveCoefficientCounterexample]
      split <;> norm_num
    exact mul_le_mul_of_nonneg_right ha (by positivity)

/-- The first Hankel block of the positive-coefficient counterexample. -/
def positiveCoefficientCounterexampleHankel : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => positiveCoefficientCounterexample ((i : ℕ) + (j : ℕ))

/-- The first Hankel determinant is `-8`. -/
theorem positiveCoefficientCounterexampleHankel_det :
    positiveCoefficientCounterexampleHankel.det = -8 := by
  norm_num [positiveCoefficientCounterexampleHankel, positiveCoefficientCounterexample,
    Matrix.det_fin_two]

/-- The first Hankel block is not positive semidefinite. -/
theorem positiveCoefficientCounterexampleHankel_not_posSemidef :
    ¬ positiveCoefficientCounterexampleHankel.PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [positiveCoefficientCounterexampleHankel_det] at hdet
  norm_num at hdet

/-- The positive-coefficient sequence cannot be the moment sequence of any positive measure. -/
theorem positiveCoefficientCounterexample_not_momentSequence :
    ¬ ∃ μ : MeasureTheory.Measure ℝ,
      (∀ n, positiveCoefficientCounterexample n = ∫ x, x ^ n ∂μ) ∧
      (∀ n, MeasureTheory.Integrable (fun x : ℝ => x ^ n) μ) := by
  rintro ⟨μ, hs, hint⟩
  have hpsd := hankelMatrix_posSemidef positiveCoefficientCounterexample hs hint 2
  exact positiveCoefficientCounterexampleHankel_not_posSemidef (by
    simpa [positiveCoefficientCounterexampleHankel] using hpsd)

/-- Strict coefficient positivity, local power-series convergence, and failure of the moment
square-test cone occur simultaneously. -/
theorem exists_positiveCoefficient_summable_not_momentSequence :
    ∃ s : ℕ → ℝ,
      (∀ n, 0 < s n) ∧
      Summable (fun n : ℕ => s n * (1 / 2 : ℝ) ^ n) ∧
      ¬ ∃ μ : MeasureTheory.Measure ℝ,
        (∀ n, s n = ∫ x, x ^ n ∂μ) ∧
        (∀ n, MeasureTheory.Integrable (fun x : ℝ => x ^ n) μ) := by
  exact ⟨positiveCoefficientCounterexample, positiveCoefficientCounterexample_pos,
    positiveCoefficientCounterexample_summable_half,
    positiveCoefficientCounterexample_not_momentSequence⟩

/-- The unsigned Taylor moments furnished by `s ↦ exp (-s)`. -/
def reciprocalFactorialMoment (n : ℕ) : ℝ := 1 / (n.factorial : ℝ)

/-- Every reciprocal-factorial moment is strictly positive. -/
theorem reciprocalFactorialMoment_pos (n : ℕ) : 0 < reciprocalFactorialMoment n := by
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact one_div_pos.mpr hfact

/-- The first Hankel block of the reciprocal-factorial sequence. -/
def reciprocalFactorialHankel : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => reciprocalFactorialMoment ((i : ℕ) + (j : ℕ))

/-- The reciprocal-factorial Hankel determinant is `-1/2`. -/
theorem reciprocalFactorialHankel_det :
    reciprocalFactorialHankel.det = -(1 / 2 : ℝ) := by
  norm_num [reciprocalFactorialHankel, reciprocalFactorialMoment, Matrix.det_fin_two,
    Nat.factorial]

/-- The reciprocal-factorial Hankel block is not positive semidefinite. -/
theorem reciprocalFactorialHankel_not_posSemidef :
    ¬ reciprocalFactorialHankel.PosSemidef := by
  intro h
  have hdet := h.det_nonneg
  rw [reciprocalFactorialHankel_det] at hdet
  norm_num at hdet

/-- No positive measure has the reciprocal-factorial sequence as all of its moments. -/
theorem reciprocalFactorialMoment_not_momentSequence :
    ¬ ∃ μ : MeasureTheory.Measure ℝ,
      (∀ n, reciprocalFactorialMoment n = ∫ x, x ^ n ∂μ) ∧
      (∀ n, MeasureTheory.Integrable (fun x : ℝ => x ^ n) μ) := by
  rintro ⟨μ, hs, hint⟩
  have hpsd := hankelMatrix_posSemidef reciprocalFactorialMoment hs hint 2
  exact reciprocalFactorialHankel_not_posSemidef (by
    simpa [reciprocalFactorialHankel] using hpsd)

/-- Exact iterated derivatives of `s ↦ exp (-s)`. -/
theorem iteratedDeriv_exp_neg (n : ℕ) :
    iteratedDeriv n (fun s : ℝ => Real.exp (-s)) =
      fun s => (-1 : ℝ) ^ n * Real.exp (-s) := by
  simpa using iteratedDeriv_exp_const_mul n (-1)

/-- The negative exponential is strictly completely monotone. -/
theorem exp_neg_strictly_completelyMonotone (n : ℕ) (s : ℝ) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n (fun x : ℝ => Real.exp (-x)) s := by
  rw [congrFun (iteratedDeriv_exp_neg n) s]
  calc
    (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * Real.exp (-s)) =
        ((-1 : ℝ) ^ n) ^ 2 * Real.exp (-s) := by ring
    _ > 0 := mul_pos (sq_pos_of_ne_zero (pow_ne_zero n (by norm_num))) (Real.exp_pos _)

/-- The negative exponential is real analytic at every point. -/
theorem analyticAt_exp_neg (s : ℝ) : AnalyticAt ℝ (fun x : ℝ => Real.exp (-x)) s := by
  fun_prop

/-- Its Taylor coefficients are the alternating reciprocal-factorial sequence. -/
theorem exp_neg_taylorCoefficient (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (-x)) 0 / (n.factorial : ℝ) =
      (-1 : ℝ) ^ n * reciprocalFactorialMoment n := by
  rw [congrFun (iteratedDeriv_exp_neg n) 0]
  simp [reciprocalFactorialMoment, div_eq_mul_inv]

/-- A function may be analytic and strictly completely monotone while its unsigned Taylor
coefficients fail the moment square-test cone. -/
theorem exists_analytic_strictlyCompletelyMonotone_nonStieltjesTaylor :
    ∃ f : ℝ → ℝ,
      (∀ s, AnalyticAt ℝ f s) ∧
      (∀ n s, 0 < (-1 : ℝ) ^ n * iteratedDeriv n f s) ∧
      (∀ n, iteratedDeriv n f 0 / (n.factorial : ℝ) =
        (-1 : ℝ) ^ n * reciprocalFactorialMoment n) ∧
      ¬ ∃ μ : MeasureTheory.Measure ℝ,
        (∀ n, reciprocalFactorialMoment n = ∫ x, x ^ n ∂μ) ∧
        (∀ n, MeasureTheory.Integrable (fun x : ℝ => x ^ n) μ) := by
  exact ⟨fun s => Real.exp (-s), analyticAt_exp_neg, exp_neg_strictly_completelyMonotone,
    exp_neg_taylorCoefficient, reciprocalFactorialMoment_not_momentSequence⟩

end

end HTGeometry
