import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicRenewalMassHasItsExactNormalization
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCausalKernelHasItsFourierMultiplier

/-!
# Exact normalization of the coupled logarithmic renewal profiles

The cumulative mass of two causal increments is trapped between the square
of the half-scale renewal mass and the square of the full-scale mass.
Both have the same exact logarithmic normalization.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- Positivity makes the actual cumulative causal mass increasing. -/
theorem monotone_logarithmicRenewalMass : Monotone logarithmicRenewalMass := by
  intro x y hxy
  apply setIntegral_mono_set logarithmicCausalKernel_mass_one.1.integrableOn
  · exact Eventually.of_forall logarithmicCausalKernel_nonneg
  · exact Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hxy⟩

/-- The renewal readout of a reflected endpoint renewal profile. -/
def logarithmicRenewalCoupling (x : ℝ) : ℝ :=
  ∫ y in Ioc (0 : ℝ) x, logarithmicCausalKernel y * logarithmicRenewalMass (x - y)

theorem integrable_logarithmicRenewalCoupling (x : ℝ) :
    Integrable (fun y : ℝ => logarithmicCausalKernel y * logarithmicRenewalMass (x - y)) := by
  apply Integrable.mono' logarithmicCausalKernel_mass_one.1
    ((measurable_logarithmicCausalKernel.mul
      (monotone_logarithmicRenewalMass.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
  filter_upwards with y
  change ‖logarithmicCausalKernel y*logarithmicRenewalMass (x-y)‖ ≤ logarithmicCausalKernel y
  rw [Real.norm_of_nonneg (mul_nonneg (logarithmicCausalKernel_nonneg y)
    (logarithmicRenewalMass_nonneg _))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (logarithmicRenewalMass_le_one (x-y))
    (logarithmicCausalKernel_nonneg y)

/-- The coupled mass is no larger than the square of the full-scale mass. -/
theorem logarithmicRenewalCoupling_le_square (x : ℝ) :
    logarithmicRenewalCoupling x ≤ logarithmicRenewalMass x ^ 2 := by
  calc
    _ ≤ ∫ y in Ioc (0 : ℝ) x, logarithmicCausalKernel y * logarithmicRenewalMass x := by
      apply setIntegral_mono_on (integrable_logarithmicRenewalCoupling x).integrableOn
        (logarithmicCausalKernel_mass_one.1.integrableOn.mul_const _) measurableSet_Ioc
      intro y hy
      exact mul_le_mul_of_nonneg_left
        (monotone_logarithmicRenewalMass (by linarith only [hy.1]))
        (logarithmicCausalKernel_nonneg y)
    _ = _ := by rw [integral_mul_const]; change logarithmicRenewalMass x * logarithmicRenewalMass x = _; ring

/-- Restricting both increments to the half-scale gives a matching lower bound. -/
theorem square_half_le_logarithmicRenewalCoupling {x : ℝ} (hx : 0 ≤ x) :
    logarithmicRenewalMass (x / 2) ^ 2 ≤ logarithmicRenewalCoupling x := by
  calc
    _ = ∫ y in Ioc (0 : ℝ) (x / 2), logarithmicCausalKernel y * logarithmicRenewalMass (x / 2) := by
      rw [integral_mul_const]
      change _ = logarithmicRenewalMass (x / 2) * logarithmicRenewalMass (x / 2)
      ring
    _ ≤ ∫ y in Ioc (0 : ℝ) (x / 2), logarithmicCausalKernel y * logarithmicRenewalMass (x - y) := by
      apply setIntegral_mono_on (logarithmicCausalKernel_mass_one.1.integrableOn.mul_const _)
        (integrable_logarithmicRenewalCoupling x).integrableOn measurableSet_Ioc
      intro y hy
      exact mul_le_mul_of_nonneg_left
        (monotone_logarithmicRenewalMass (by linarith only [hy.2]))
        (logarithmicCausalKernel_nonneg y)
    _ ≤ _ := by
      apply setIntegral_mono_set (integrable_logarithmicRenewalCoupling x).integrableOn
      · exact Eventually.of_forall fun y => mul_nonneg (logarithmicCausalKernel_nonneg _)
          (logarithmicRenewalMass_nonneg _)
      · exact Eventually.of_forall fun y hy => ⟨hy.1, by linarith only [hy.2, hx]⟩

private theorem tendsto_renewal_exp_shift_normalized (d : ℝ) :
    Tendsto (fun u : ℝ => logarithmicRenewalMass (Real.exp (-(u+d))) * Real.sqrt u)
      atTop (nhds 1) := by
  have hd : Tendsto (fun u : ℝ => u+d) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop (B-d)] with u hu
    linarith only [hu]
  have hmain := tendsto_logarithmicRenewalMass_exp_normalized.comp hd
  have hratio : Tendsto (fun u : ℝ => Real.sqrt u / Real.sqrt (u+d)) atTop (nhds 1) := by
    have hr : Tendsto (fun u : ℝ => (u+d)/u) atTop (nhds 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero.const_mul d)
      simp only [mul_zero, add_zero] at h
      apply h.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      field_simp [hu.ne']
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hr.inv₀ (by norm_num))
    simp only [inv_one, Real.sqrt_one, inv_div] at hs
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact Real.sqrt_div hu.le (u+d)
  have hp := hmain.mul hratio
  simp only [mul_one] at hp
  apply hp.congr'
  filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℝ))] with u hu
  dsimp only [Function.comp_def]
  field_simp [(Real.sqrt_pos.mpr hu).ne']

private theorem tendsto_renewal_square_exp_shift (d : ℝ) :
    Tendsto (fun u : ℝ => logarithmicRenewalMass (Real.exp (-(u+d))) ^ 2 * u)
      atTop (nhds 1) := by
  have h := (tendsto_renewal_exp_shift_normalized d).pow 2
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [mul_pow, Real.sq_sqrt hu.le]

/-- The two-increment renewal mass has coefficient exactly one at logarithmic scale. -/
theorem tendsto_logarithmicRenewalCoupling_exp_normalized :
    Tendsto (fun u : ℝ => logarithmicRenewalCoupling (Real.exp (-u)) * u) atTop (nhds 1) := by
  have hup : Tendsto (fun u : ℝ => logarithmicRenewalMass (Real.exp (-u)) ^ 2 * u)
      atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_renewal_square_exp_shift 0
  have hlo : Tendsto (fun u : ℝ => logarithmicRenewalMass (Real.exp (-u) / 2) ^ 2 * u)
      atTop (nhds 1) := by
    have h := tendsto_renewal_square_exp_shift (Real.log 2)
    simpa only [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← div_eq_mul_inv] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_right (square_half_le_logarithmicRenewalCoupling (Real.exp_pos _).le) hu.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_right (logarithmicRenewalCoupling_le_square _) hu.le

/-- The actual endpoint renewal coupling has exact size `1 / log(1/x)` as the strip closes. -/
theorem tendsto_logarithmicRenewalCoupling_normalized :
    Tendsto (fun x : ℝ => logarithmicRenewalCoupling x * Real.log (1 / x))
      (𝓝[>] (0 : ℝ)) (nhds 1) := by
  have hu : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := tendsto_logarithmicRenewalCoupling_exp_normalized.comp hu
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (0 : ℝ) < x at hx
  simp only [Function.comp_def, neg_neg, Real.exp_log hx, one_div, Real.log_inv]

#print axioms tendsto_logarithmicRenewalCoupling_normalized
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
