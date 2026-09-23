import GaloisForLFunctions.RHTower.FokasLenellsAnisotropicLipschitz
import GaloisForLFunctions.RHTower.FokasLenellsOperatorPhaseResolvent

/-!
# Profile-dependent stability for the actual Cauchy inverse

The conserved initial jump norm supplies the inverse budget. Combining it
with the optimal initial time and space generator weights gives uniform
stability of the inverse and its solutions under parameters and forcing.
-/

open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Joint inverse stability uses the actual initial generator norms and initial inverse budget. -/
theorem norm_directResolventInverse_joint_sub_le_initial_generators
    (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val - ((directResolventUnit q s y)⁻¹).val‖ ≤
      directInitialResolventBudget q ^ (2 : ℕ) *
        (‖directJumpTimeOperator q 0 0‖ * ‖t-s‖ +
          ‖directJumpSpaceOperator q 0 0‖ * ‖x-y‖) := by
  have h := norm_directResolvent_difference_le_initial_budgets q q t x s y
  rw [← pow_two] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (norm_directJumpPerturbation_joint_sub_le_initial_generators q t x s y) (sq_nonneg _))

/-- Sharper time stability for the actual inverse, uniform in the space parameter. -/
theorem norm_directResolventInverse_time_sub_le_initial_generator
    (q : SchwartzMap ℝ ℂ) (x t s : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val - ((directResolventUnit q s x)⁻¹).val‖ ≤
      (directInitialResolventBudget q ^ (2 : ℕ) * ‖directJumpTimeOperator q 0 0‖) * ‖t-s‖ := by
  simpa only [sub_self, norm_zero, mul_zero, add_zero, mul_assoc] using
    norm_directResolventInverse_joint_sub_le_initial_generators q t x s x

/-- Sharper space stability for the actual inverse, uniform in the time parameter. -/
theorem norm_directResolventInverse_space_sub_le_initial_generator
    (q : SchwartzMap ℝ ℂ) (t x y : ℝ) :
    ‖((directResolventUnit q t x)⁻¹).val - ((directResolventUnit q t y)⁻¹).val‖ ≤
      (directInitialResolventBudget q ^ (2 : ℕ) * ‖directJumpSpaceOperator q 0 0‖) * ‖x-y‖ := by
  simpa only [sub_self, norm_zero, mul_zero, zero_add, mul_assoc] using
    norm_directResolventInverse_joint_sub_le_initial_generators q t x t y

/-- The parameter estimate holds on every actual forcing vector. -/
theorem directSolution_joint_sub_le_initial_generators
    (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (d : Boundary) :
    ‖directSolution q t x d - directSolution q s y d‖ ≤
      (directInitialResolventBudget q ^ (2 : ℕ) *
        (‖directJumpTimeOperator q 0 0‖ * ‖t-s‖ +
          ‖directJumpSpaceOperator q 0 0‖ * ‖x-y‖)) * ‖d‖ := by
  have h := (((directResolventUnit q t x)⁻¹).val -
    ((directResolventUnit q s y)⁻¹).val).le_opNorm d
  exact h.trans (mul_le_mul_of_nonneg_right
    (norm_directResolventInverse_joint_sub_le_initial_generators q t x s y) (norm_nonneg _))

/-- Simultaneous forcing and parameter perturbations of the actual solution admit one uniform bound. -/
theorem directSolution_joint_forcing_sub_le_initial_generators
    (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (d e : Boundary) :
    ‖directSolution q t x d - directSolution q s y e‖ ≤
      directInitialResolventBudget q * ‖d-e‖ +
      (directInitialResolventBudget q ^ (2 : ℕ) *
        (‖directJumpTimeOperator q 0 0‖ * ‖t-s‖ +
          ‖directJumpSpaceOperator q 0 0‖ * ‖x-y‖)) * ‖e‖ := by
  have hf : ‖directSolution q t x d - directSolution q t x e‖ ≤
      directInitialResolventBudget q * ‖d-e‖ := by
    simpa only [dist_eq_norm] using dist_directSolution_le_initial_budget q t x d e
  exact (norm_sub_le_norm_sub_add_norm_sub
    (directSolution q t x d) (directSolution q t x e) (directSolution q s y e)).trans
    (add_le_add hf (directSolution_joint_sub_le_initial_generators q t x s y e))

/-- The actual initial inverse budget never exceeds the old universal squared factor. -/
theorem directInitialResolventBudget_sq_le (q : SchwartzMap ℝ ℂ) :
    directInitialResolventBudget q ^ (2 : ℕ) ≤ (81/25 : ℝ) := by
  have h := directInitialResolventBudget_bounds q
  nlinarith

/-- The new time constant is bounded above by the previous uniform time constant. -/
theorem directResolventInitialTimeBudget_le_uniform (q : SchwartzMap ℝ ℂ) :
    directInitialResolventBudget q ^ (2 : ℕ) * ‖directJumpTimeOperator q 0 0‖ ≤
      (81/50 : ℝ) * regularReflectionFrequencyBudget q := by
  have hj : ‖directJumpTimeOperator q 0 0‖ ≤ (1/2 : ℝ) * regularReflectionFrequencyBudget q := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
    exact directJumpTimeOperator_bound q 0 0
  calc
    _ ≤ (81/25 : ℝ) * ((1/2 : ℝ) * regularReflectionFrequencyBudget q) :=
      mul_le_mul (directInitialResolventBudget_sq_le q) hj (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The new space constant is bounded above by the previous uniform space constant. -/
theorem directResolventInitialSpaceBudget_le_uniform (q : SchwartzMap ℝ ℂ) :
    directInitialResolventBudget q ^ (2 : ℕ) * ‖directJumpSpaceOperator q 0 0‖ ≤
      (81/25 : ℝ) * directSpaceOperatorBudget q := by
  have hj : ‖directJumpSpaceOperator q 0 0‖ ≤ directSpaceOperatorBudget q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (directSpaceOperatorBudget_nonneg q)
    exact directJumpSpaceOperator_bound q 0 0
  exact mul_le_mul (directInitialResolventBudget_sq_le q) hj (norm_nonneg _) (by positivity)

end
end RHTower.FokasLenells
