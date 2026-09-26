import GaloisForLFunctions.RHTower.XiHeatThirdPhaseDefectBound
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# Uniform control of the third Xi phase debt after heat scaling

The Gaussian factorial estimate bounds every positive norm moment by the
summable reciprocal-square mass of the actual Xi divisor.  For the polynomial
`a + b t z + c t² z²`, these estimates remove every heat-time factor from the
phase-debt budget.  The remaining mass has an unconditional rational ceiling.
-/

namespace RHTower
noncomputable section

def xiHeatInverseNormMass : ℝ :=
  ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

def xiHeatMomentFactorialBound (k : ℕ) : ℝ :=
  2 ^ (k + 1) * ((k + 1).factorial : ℝ)

theorem xiHeatMomentFactorialBound_nonneg (k : ℕ) :
    0 ≤ xiHeatMomentFactorialBound k := by
  unfold xiHeatMomentFactorialBound
  positivity

theorem xiHeatInverseNormMass_le : xiHeatInverseNormMass ≤ 198 / 3175 := by
  have h := tsum_norm_xiResolventPoint_le_budget (X := 0) (le_refl 0)
  simpa [xiHeatInverseNormMass, xiResolventPoint, norm_inv, norm_pow, one_div] using h

theorem xiHeatNormMoment_scaled_atom_le (k : ℕ) (τ : ℝ) (q : XiZeroCopy) :
    (Real.exp τ) ^ (k + 1) *
        (‖xiSpectralPoint q ^ 2‖ ^ k *
          Real.exp (-(Real.exp τ * (xiSpectralPoint q ^ 2).re))) ≤
      xiHeatMomentFactorialBound k * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let t := Real.exp τ
  let R := ‖xiSpectralPoint q ^ 2‖
  let u := (xiSpectralPoint q ^ 2).re
  have ht : 0 < t := Real.exp_pos τ
  have hR : 0 < R := norm_pos_iff.mpr (pow_ne_zero 2 (xiSpectralPoint_ne_zero q))
  have hsector : R < 2 * u := by
    simpa only [R, u, norm_pow, Complex.sq_norm] using
      xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hfac : 0 < ((k + 1).factorial : ℝ) := by positivity
  have hexp := Real.pow_div_factorial_le_exp (t * R / 2) (by positivity) (k + 1)
  have hpoly : (t * R / 2) ^ (k + 1) ≤
      Real.exp (t * R / 2) * ((k + 1).factorial : ℝ) :=
    (div_le_iff₀ hfac).mp hexp
  have hcancel : Real.exp (t * R / 2) * Real.exp (-(t * R / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hproduct : (t * R / 2) ^ (k + 1) * Real.exp (-(t * R / 2)) ≤
      ((k + 1).factorial : ℝ) := by
    calc
      _ ≤ (Real.exp (t * R / 2) * ((k + 1).factorial : ℝ)) *
          Real.exp (-(t * R / 2)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = ((k + 1).factorial : ℝ) *
          (Real.exp (t * R / 2) * Real.exp (-(t * R / 2))) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have hdecay : Real.exp (-(t * u)) ≤ Real.exp (-(t * R / 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hproduct' := (mul_le_mul_of_nonneg_left hdecay
    (pow_nonneg (by positivity : 0 ≤ t * R / 2) (k + 1))).trans hproduct
  have hscale := mul_le_mul_of_nonneg_left hproduct'
    (pow_nonneg (by positivity : (0 : ℝ) ≤ 2) (k + 1))
  have hid : (2 : ℝ) ^ (k + 1) * (t * R / 2) ^ (k + 1) =
      t ^ (k + 1) * R ^ (k + 1) := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  rw [← mul_assoc, hid] at hscale
  have hnorm : ‖xiSpectralPoint q‖ ^ 2 = R := (norm_pow _ _).symm
  rw [hnorm, one_div, ← div_eq_mul_inv]
  apply (le_div_iff₀ hR).2
  change (t ^ (k + 1) * (R ^ k * Real.exp (-(t * u)))) * R ≤ _
  calc
    _ = t ^ (k + 1) * R ^ (k + 1) * Real.exp (-(t * u)) := by
      rw [pow_succ]
      ring
    _ ≤ _ := hscale

/-- Gaussian norm moments have an explicit reciprocal-mass ceiling at every positive time. -/
theorem xiHeatNormMoment_scaled_le (k : ℕ) (τ : ℝ) :
    (Real.exp τ) ^ (k + 1) * xiHeatNormMoment k τ ≤
      xiHeatMomentFactorialBound k * xiHeatInverseNormMass := by
  have h := Summable.tsum_le_tsum (xiHeatNormMoment_scaled_atom_le k τ)
    ((summable_xiHeatNormMoment k τ).mul_left ((Real.exp τ) ^ (k + 1)))
    (xiSpectralPoint_inv_sq_summable.mul_left (xiHeatMomentFactorialBound k))
  simpa only [tsum_mul_left, xiHeatNormMoment, xiHeatInverseNormMass] using h

def xiHeatThirdScaledDebtConstant (a b c : ℝ) : ℝ :=
  (3 * a ^ 2 + 8 * b ^ 2) * xiHeatMomentFactorialBound 1 +
    (3 * b ^ 2 + 32 * c ^ 2) * xiHeatMomentFactorialBound 3 +
    3 * c ^ 2 * xiHeatMomentFactorialBound 5

theorem xiHeatThirdScaledDebtConstant_nonneg (a b c : ℝ) :
    0 ≤ xiHeatThirdScaledDebtConstant a b c := by
  unfold xiHeatThirdScaledDebtConstant
  exact add_nonneg (add_nonneg
    (mul_nonneg (by positivity) (xiHeatMomentFactorialBound_nonneg 1))
    (mul_nonneg (by positivity) (xiHeatMomentFactorialBound_nonneg 3)))
    (mul_nonneg (by positivity) (xiHeatMomentFactorialBound_nonneg 5))

/-- Scaling the linear and quadratic coefficients by heat time leaves a uniform debt bound. -/
theorem xiHeatThirdPhaseDebt_scaled_le_mass (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ ≤
      xiHeatThirdScaledDebtConstant a b c * xiHeatInverseNormMass := by
  have h1 := mul_le_mul_of_nonneg_left (xiHeatNormMoment_scaled_le 1 τ)
    (show 0 ≤ 3 * a ^ 2 + 8 * b ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left (xiHeatNormMoment_scaled_le 3 τ)
    (show 0 ≤ 3 * b ^ 2 + 32 * c ^ 2 by positivity)
  have h5 := mul_le_mul_of_nonneg_left (xiHeatNormMoment_scaled_le 5 τ)
    (show 0 ≤ 3 * c ^ 2 by positivity)
  refine (xiHeatThirdPhaseDebt_le_budget a (b * Real.exp τ)
    (c * (Real.exp τ) ^ 2) τ).trans ?_
  unfold xiHeatThirdDebtBudget xiHeatThirdScaledDebtConstant
  convert add_le_add (add_le_add h1 h3) h5 using 1 <;> ring

/-- The actual normalized negative remainder is bounded by an explicit rational-mass constant. -/
theorem xiHeatThirdPhaseDebt_scaled_le (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a (b * Real.exp τ) (c * (Real.exp τ) ^ 2) τ ≤
      xiHeatThirdScaledDebtConstant a b c * (198 / 3175) :=
  (xiHeatThirdPhaseDebt_scaled_le_mass a b c τ).trans
    (mul_le_mul_of_nonneg_left xiHeatInverseNormMass_le
      (xiHeatThirdScaledDebtConstant_nonneg a b c))


/-! ## Positivity along fixed normalized quadratic heat shapes -/

open Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

/-- Every fixed normalized quadratic heat shape has an unbounded positive norm energy. -/
theorem xiHeatThirdNormEnergy_scaled_tendsto (b c : ℝ) :
    Tendsto (fun τ => xiHeatThirdNormEnergy 1 (b * Real.exp τ)
      (c * (Real.exp τ) ^ 2) τ) atBot atTop := by
  classical
  apply tendsto_atTop.2
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  let e : ℕ ↪ XiZeroCopy := ⟨xiThermalEnumeration, xiThermalEnumeration_bijective.1⟩
  let s : Finset XiZeroCopy := (Finset.range N).map e
  let g : ℝ → XiZeroCopy → ℝ := fun t q =>
    ‖quadraticHeatValue 1 (b * t) (c * t ^ 2) (xiSpectralPoint q ^ 2)‖ ^ 2 *
      Real.exp (-(t * (xiSpectralPoint q ^ 2).re))
  have hcont : Continuous (fun t : ℝ => ∑ q ∈ s, g t q) := by
    dsimp [g, quadraticHeatValue]
    fun_prop
  have hlim : Tendsto (fun τ => ∑ q ∈ s, g (Real.exp τ) q) atBot (𝓝 (N : ℝ)) := by
    have h := hcont.continuousAt.tendsto.comp Real.tendsto_exp_atBot
    simpa [g, quadraticHeatValue, s, Function.comp_def] using h
  have hhead := hlim.eventually_const_lt hN
  filter_upwards [hhead] with τ hτ
  have hsum := (summable_xiHeatThirdAmplitude_norm_sq 1 (b * Real.exp τ)
    (c * (Real.exp τ) ^ 2) τ).sum_le_tsum s (fun _ _ => sq_nonneg _)
  have hfinite : (∑ q ∈ s, g (Real.exp τ) q) =
      ∑ q ∈ s, ‖xiHeatThirdAmplitude 1 (b * Real.exp τ)
        (c * (Real.exp τ) ^ 2) τ q‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro q _
    rw [xiHeatThirdAmplitude, heatPhaseAmplitude_norm_sq]
  rw [hfinite] at hτ
  exact hτ.le.trans hsum

/-- The bounded negative phase debt cannot prevent divergence to positive infinity. -/
theorem xiHeatThirdQuadratic_scaled_tendsto (b c : ℝ) :
    Tendsto (fun τ => xiHeatThirdQuadratic 1 (b * Real.exp τ)
      (c * (Real.exp τ) ^ 2) (Real.exp τ)) atBot atTop := by
  apply tendsto_atTop.2
  intro M
  have h := (tendsto_atTop.mp (xiHeatThirdNormEnergy_scaled_tendsto b c))
    (M + xiHeatThirdScaledDebtConstant 1 b c * (198 / 3175))
  filter_upwards [h] with τ hτ
  rw [xiHeatThirdQuadratic_eq_energy_sub_debt]
  have hd := xiHeatThirdPhaseDebt_scaled_le 1 b c τ
  linarith

/-- Every fixed normalized quadratic heat shape is positive at all sufficiently small times. -/
theorem xiHeatThirdQuadratic_scaled_eventually_pos (b c : ℝ) :
    ∀ᶠ τ in atBot, 0 < xiHeatThirdQuadratic 1 (b * Real.exp τ)
      (c * (Real.exp τ) ^ 2) (Real.exp τ) := by
  have h := (tendsto_atTop.mp (xiHeatThirdQuadratic_scaled_tendsto b c)) 1
  filter_upwards [h] with τ hτ
  linarith

end
end RHTower
