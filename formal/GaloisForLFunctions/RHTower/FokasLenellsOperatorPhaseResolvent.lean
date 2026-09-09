import GaloisForLFunctions.RHTower.FokasLenellsOperatorPhaseUnitary
import GaloisForLFunctions.RHTower.FokasLenellsTimeInverse

/-!
# Initial-data inverse budgets and residual estimates

The conserved exact initial jump norm gives a profile-dependent inverse
budget, uniform in time and position. It controls solutions, residual errors,
and inverse-operator differences between arbitrary actual input profiles.
-/

open MeasureTheory
namespace RHTower.FokasLenells
noncomputable section

/-- The Neumann inverse budget determined by the actual initial jump norm. -/
def directInitialResolventBudget (q : SchwartzMap ℝ ℂ) : ℝ :=
  (1 - ‖directJumpPerturbation q 0 0‖)⁻¹

private theorem initial_jump_norm_bound (q : SchwartzMap ℝ ℂ) :
    ‖directJumpPerturbation q 0 0‖ ≤ (4/9 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact directJumpPerturbation_bound q 0 0

private theorem initial_jump_denominator_pos (q : SchwartzMap ℝ ℂ) :
    0 < 1 - ‖directJumpPerturbation q 0 0‖ := by
  linarith [initial_jump_norm_bound q]

/-- The exact initial-data budget lies between one and the original universal bound. -/
theorem directInitialResolventBudget_bounds (q : SchwartzMap ℝ ℂ) :
    1 ≤ directInitialResolventBudget q ∧ directInitialResolventBudget q ≤ (9/5 : ℝ) := by
  unfold directInitialResolventBudget
  rw [← one_div]
  constructor
  · apply (le_div_iff₀ (initial_jump_denominator_pos q)).2
    linarith [norm_nonneg (directJumpPerturbation q 0 0)]
  · apply (div_le_iff₀ (initial_jump_denominator_pos q)).2
    linarith [initial_jump_norm_bound q]

private theorem initial_budget_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ directInitialResolventBudget q :=
  (by norm_num : (0 : ℝ) ≤ 1).trans (directInitialResolventBudget_bounds q).1

/-- Sharpened solution bound, uniform over the whole time-position plane. -/
theorem directSolution_bound_initial_budget (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ‖directSolution q t x d‖ ≤ directInitialResolventBudget q * ‖d‖ := by
  have he := (sub_eq_iff_eq_add).mp (directSolution_equation q t x d)
  have hn : ‖directSolution q t x d‖ ≤ ‖d‖ +
      ‖directCauchyOperator q t x (directSolution q t x d)‖ := by
    calc
      _ = ‖d + directCauchyOperator q t x (directSolution q t x d)‖ := congrArg norm he
      _ ≤ _ := norm_add_le _ _
  have hc := (directCauchyOperator q t x).le_opNorm (directSolution q t x d)
  rw [norm_directCauchyOperator_time_space_invariant] at hc
  have hd : ‖directSolution q t x d‖ ≤ ‖d‖ / (1 - ‖directJumpPerturbation q 0 0‖) := by
    apply (le_div_iff₀ (initial_jump_denominator_pos q)).2
    nlinarith
  simpa only [directInitialResolventBudget, div_eq_mul_inv, mul_comm] using hd

/-- The actual constructed inverse has the same initial-data operator-norm budget. -/
theorem norm_directResolventInverse_le_initial_budget (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val‖ ≤ directInitialResolventBudget q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (initial_budget_nonneg q)
  exact directSolution_bound_initial_budget q t x

/-- Forcing perturbations have the sharp initial-data Lipschitz budget uniformly in time and position. -/
theorem dist_directSolution_le_initial_budget (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d e : Boundary) :
    dist (directSolution q t x d) (directSolution q t x e) ≤
      directInitialResolventBudget q * dist d e := by
  have h := directSolution_bound_initial_budget q t x (d-e)
  change ‖((directResolventUnit q t x)⁻¹).val (d-e)‖ ≤ _ at h
  rw [map_sub] at h
  simpa only [dist_eq_norm, directSolution] using h

/-- The actual Cauchy residual gives a uniform rigorous error estimate for every candidate solution. -/
theorem directSolution_residual_bound_initial_budget (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (d u : Boundary) :
    ‖u - directSolution q t x d‖ ≤ directInitialResolventBudget q *
      ‖u - directCauchyOperator q t x u - d‖ := by
  have he : directSolution q t x (u - directCauchyOperator q t x u) = u :=
    (directSolution_existsUnique q t x _).unique (directSolution_equation q t x _) rfl
  have h := dist_directSolution_le_initial_budget q t x (u - directCauchyOperator q t x u) d
  rw [he] at h
  simpa only [dist_eq_norm] using h

/-- Exact resolvent difference identity also holds across different actual input potentials. -/
theorem directSolution_crossPotential_resolvent_difference
    (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) (d : Boundary) :
    directSolution q t x d - directSolution p s y d = directSolution q t x
      (directCauchyOperator q t x (directSolution p s y d) -
        directCauchyOperator p s y (directSolution p s y d)) := by
  apply (directSolution_existsUnique q t x _).unique ?_ (directSolution_equation q t x _)
  calc
    _ = (directSolution q t x d - directCauchyOperator q t x (directSolution q t x d)) -
        (directSolution p s y d - directCauchyOperator p s y (directSolution p s y d)) +
        (directCauchyOperator q t x (directSolution p s y d) -
          directCauchyOperator p s y (directSolution p s y d)) := by
      rw [map_sub]
      abel
    _ = _ := by rw [directSolution_equation, directSolution_equation]; abel

/-- Cross-potential inverse errors are controlled by the exact jump difference and the two initial budgets. -/
theorem norm_directResolvent_difference_le_initial_budgets
    (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val - ((directResolventUnit p s y)⁻¹).val‖ ≤
      (directInitialResolventBudget q * directInitialResolventBudget p) *
        ‖directJumpPerturbation q t x - directJumpPerturbation p s y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (initial_budget_nonneg q) (initial_budget_nonneg p)) (norm_nonneg _))
  intro d
  change ‖directSolution q t x d - directSolution p s y d‖ ≤ _
  rw [directSolution_crossPotential_resolvent_difference]
  have he : ‖directCauchyOperator q t x - directCauchyOperator p s y‖ =
      ‖directJumpPerturbation q t x - directJumpPerturbation p s y‖ := by
    simpa only [dist_eq_norm] using dist_directCauchyOperator_eq_jump q p t x s y
  have hop := (directCauchyOperator q t x - directCauchyOperator p s y).le_opNorm (directSolution p s y d)
  change ‖directCauchyOperator q t x (directSolution p s y d) -
    directCauchyOperator p s y (directSolution p s y d)‖ ≤ _ at hop
  calc
    _ ≤ directInitialResolventBudget q *
      ‖directCauchyOperator q t x (directSolution p s y d) -
        directCauchyOperator p s y (directSolution p s y d)‖ := directSolution_bound_initial_budget q t x _
    _ ≤ directInitialResolventBudget q *
      (‖directCauchyOperator q t x - directCauchyOperator p s y‖ * ‖directSolution p s y d‖) :=
        mul_le_mul_of_nonneg_left hop (initial_budget_nonneg q)
    _ ≤ directInitialResolventBudget q *
      (‖directCauchyOperator q t x - directCauchyOperator p s y‖ *
        (directInitialResolventBudget p * ‖d‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (directSolution_bound_initial_budget p s y d) (norm_nonneg _))
        (initial_budget_nonneg q)
    _ = _ := by rw [he]; ring

end
end RHTower.FokasLenells
