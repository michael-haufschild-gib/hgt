import GaloisForLFunctions.RHTower.XiHeatThirdScaledPositivity

/-!
# Vanishing coefficient-uniform debt in the third Xi heat form

The reciprocal-square majorant is summable and each scaled Gaussian norm atom
tends to zero. Dominated convergence improves the uniform factorial ceiling to
a vanishing bound. One scalar error then controls the phase debt in every real
coefficient direction, without dropping any cross term of the original form.
-/

namespace RHTower
noncomputable section
open Filter Topology

/-- Every scaled norm moment is little-oh of its reciprocal-mass ceiling. -/
theorem xiHeatNormMoment_scaled_tendsto_zero (k : ℕ) :
    Tendsto (fun τ => (Real.exp τ) ^ (k + 1) * xiHeatNormMoment k τ)
      atBot (𝓝 0) := by
  let f : ℝ → XiZeroCopy → ℝ := fun τ q =>
    (Real.exp τ) ^ (k + 1) * (‖xiSpectralPoint q ^ 2‖ ^ k *
      Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re)))
  have hpoint : ∀ q, Tendsto (fun τ => f τ q) atBot (𝓝 0) := by
    intro q
    have hc : Continuous (fun t : ℝ => t ^ (k + 1) *
        (‖xiSpectralPoint q ^ 2‖ ^ k * Real.exp (-(t * (xiSpectralPoint q ^ 2).re)))) := by
      fun_prop
    simpa [f, Function.comp_def] using
      hc.continuousAt.tendsto.comp Real.tendsto_exp_atBot
  have hdom : ∀ᶠ τ in atBot, ∀ q,
      ‖f τ q‖ ≤ xiHeatMomentFactorialBound k * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    filter_upwards with τ q
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
    exact xiHeatNormMoment_scaled_atom_le k τ q
  have h := tendsto_tsum_of_dominated_convergence
    (xiSpectralPoint_inv_sq_summable.mul_left (xiHeatMomentFactorialBound k)) hpoint hdom
  simpa only [f, tsum_zero, tsum_mul_left, xiHeatNormMoment] using h

/-- A single scalar controls every coefficient direction of the scaled third form. -/
def xiHeatThirdUniformDebt (τ : ℝ) : ℝ :=
  11 * (Real.exp τ) ^ 2 * xiHeatNormMoment 1 τ +
    35 * (Real.exp τ) ^ 4 * xiHeatNormMoment 3 τ +
    3 * (Real.exp τ) ^ 6 * xiHeatNormMoment 5 τ

theorem xiHeatThirdUniformDebt_nonneg (τ : ℝ) :
    0 ≤ xiHeatThirdUniformDebt τ := by
  unfold xiHeatThirdUniformDebt
  have h1 := xiHeatNormMoment_nonneg 1 τ
  have h3 := xiHeatNormMoment_nonneg 3 τ
  have h5 := xiHeatNormMoment_nonneg 5 τ
  positivity

theorem xiHeatThirdUniformDebt_tendsto_zero :
    Tendsto xiHeatThirdUniformDebt atBot (𝓝 0) := by
  have h := (((xiHeatNormMoment_scaled_tendsto_zero 1).const_mul 11).add
    ((xiHeatNormMoment_scaled_tendsto_zero 3).const_mul 35)).add
      ((xiHeatNormMoment_scaled_tendsto_zero 5).const_mul 3)
  simp only [mul_zero, add_zero] at h
  convert h using 1
  ext τ
  unfold xiHeatThirdUniformDebt
  ring

/-- The complete phase debt has a coefficient-uniform vanishing majorant. -/
theorem xiHeatThirdPhaseDebt_le_uniform (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ ≤
      (a ^ 2 + b ^ 2 + c ^ 2) * xiHeatThirdUniformDebt τ := by
  have h1 := xiHeatNormMoment_nonneg 1 τ
  have h3 := xiHeatNormMoment_nonneg 3 τ
  have h5 := xiHeatNormMoment_nonneg 5 τ
  have hp1 : 0 ≤ (8 * a ^ 2 + 3 * b ^ 2 + 11 * c ^ 2) *
      (Real.exp τ) ^ 2 * xiHeatNormMoment 1 τ := by positivity
  have hp3 : 0 ≤ (35 * a ^ 2 + 32 * b ^ 2 + 3 * c ^ 2) *
      (Real.exp τ) ^ 4 * xiHeatNormMoment 3 τ := by positivity
  have hp5 : 0 ≤ (3 * a ^ 2 + 3 * b ^ 2) *
      (Real.exp τ) ^ 6 * xiHeatNormMoment 5 τ := by positivity
  refine (xiHeatThirdPhaseDebt_le_budget a (b * Real.exp τ)
    (c * (Real.exp τ) ^ 2) τ).trans ?_
  unfold xiHeatThirdDebtBudget xiHeatThirdUniformDebt
  nlinarith only [hp1, hp3, hp5]

/-- Uniform lower bound for the actual form, retaining the full norm energy. -/
theorem xiHeatThirdQuadratic_uniform_lower_bound (a b c τ : ℝ) :
    xiHeatThirdNormEnergy a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ -
        (a ^ 2 + b ^ 2 + c ^ 2) * xiHeatThirdUniformDebt τ ≤
      xiHeatThirdQuadratic a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) (Real.exp τ) := by
  rw [xiHeatThirdQuadratic_eq_energy_sub_debt]
  exact sub_le_sub_left (xiHeatThirdPhaseDebt_le_uniform a b c τ) _

end
end RHTower
