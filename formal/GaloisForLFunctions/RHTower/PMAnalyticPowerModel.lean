import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Analytic power models for the PM input boundary

These comparison functions satisfy the analytic PNT inputs used by the weighted
PM endpoint. They carry no prime-support or divisor-convolution identity and
are not replacements for the actual Chebyshev function. Their exact optimally
centered variance is studied separately.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- An analytic comparison profile, with no claim to be a prime-counting function. -/
def pmPowerModel (σ x : ℝ) : ℝ := if x ≤ 1 then 0 else x + x ^ σ

/-- The normalized comparison profile. -/
def pmPowerProfile (σ x : ℝ) : ℝ := pmPowerModel σ x / x

theorem pmPowerModel_nonneg (σ x : ℝ) : 0 ≤ pmPowerModel σ x := by
  unfold pmPowerModel
  split_ifs with hx
  · exact le_rfl
  · have hx0 : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx)
    positivity

theorem pmPowerModel_monotone {σ : ℝ} (hσ : 0 ≤ σ) : Monotone (pmPowerModel σ) := by
  intro x y hxy
  by_cases hy : y ≤ 1
  · simp [pmPowerModel, hy, hxy.trans hy]
  by_cases hx : x ≤ 1
  · simpa [pmPowerModel, hx] using pmPowerModel_nonneg σ y
  rw [pmPowerModel, if_neg hx, pmPowerModel, if_neg hy]
  exact add_le_add hxy (Real.rpow_le_rpow (by linarith : 0 ≤ x) hxy hσ)

theorem measurable_pmPowerModel {σ : ℝ} (hσ : 0 ≤ σ) : Measurable (pmPowerModel σ) :=
  (pmPowerModel_monotone hσ).measurable

theorem pmPowerModel_le_two_mul {σ x : ℝ} (hσ : σ ≤ 1) (hx : 0 ≤ x) :
    pmPowerModel σ x ≤ 2 * x := by
  unfold pmPowerModel
  split_ifs with hx1
  · linarith
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hσ
    rw [Real.rpow_one] at h
    linarith

theorem pmPowerProfile_eq {σ x : ℝ} (hx : 1 < x) :
    pmPowerProfile σ x = 1 + x ^ (σ - 1) := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  rw [pmPowerProfile, pmPowerModel, if_neg (not_le.mpr hx), add_div, div_self hx0,
    ← Real.rpow_sub_one hx0]

theorem pmPowerProfile_bounds {σ : ℝ} (hσ : σ ≤ 1) (x : ℝ) :
    0 ≤ pmPowerProfile σ x ∧ pmPowerProfile σ x ≤ 2 := by
  by_cases hx : x ≤ 1
  · simp [pmPowerProfile, pmPowerModel, hx]
  have hx0 : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx)
  exact ⟨div_nonneg (pmPowerModel_nonneg σ x) hx0.le,
    (div_le_iff₀ hx0).mpr (pmPowerModel_le_two_mul hσ hx0.le)⟩

theorem measurable_pmPowerProfile {σ : ℝ} (hσ : 0 ≤ σ) : Measurable (pmPowerProfile σ) :=
  (measurable_pmPowerModel hσ).div measurable_id

theorem tendsto_pmPowerProfile_one {σ : ℝ} (hσ : σ < 1) :
    Tendsto (pmPowerProfile σ) atTop (𝓝 1) := by
  have hp : Tendsto (fun x : ℝ => x ^ (σ - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hσ)
  have hh : Tendsto (fun x : ℝ => 1 + x ^ (σ - 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hp
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (pmPowerProfile_eq hx).symm

theorem pmPowerModel_absError_div_sq {σ x : ℝ} (hx : 1 < x) :
    |pmPowerModel σ x - x| / x ^ 2 = x ^ (σ - 2) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [pmPowerModel, if_neg (not_le.mpr hx), add_sub_cancel_left,
    abs_of_nonneg (Real.rpow_nonneg hx0.le σ)]
  exact (Real.rpow_sub_natCast hx0.ne' σ 2).symm

theorem pmPowerModel_sqError_div_cube {σ x : ℝ} (hx : 1 < x) :
    (pmPowerModel σ x - x) ^ 2 / x ^ 3 = x ^ (2 * σ - 3) := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [pmPowerModel, if_neg (not_le.mpr hx), add_sub_cancel_left]
  calc
    _ = x ^ (2 * σ) / x ^ 3 := by
      congr 1
      rw [← Real.rpow_natCast (x ^ σ) 2, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    _ = _ := (Real.rpow_sub_natCast hx0.ne' (2 * σ) 3).symm

theorem integrableOn_pmPowerModel_absError_div_sq {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (fun x : ℝ => |pmPowerModel σ x - x| / x ^ 2) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith : σ - 2 < -1) zero_lt_one).congr_fun
    (fun x hx => (pmPowerModel_absError_div_sq hx).symm) measurableSet_Ioi

theorem integral_pmPowerModel_absError_div_sq {σ : ℝ} (hσ : σ < 1) :
    (∫ x in Ioi (1 : ℝ), |pmPowerModel σ x - x| / x ^ 2) = 1 / (1 - σ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pmPowerModel_absError_div_sq hx),
    integral_Ioi_rpow_of_lt (by linarith : σ - 2 < -1) zero_lt_one, Real.one_rpow]
  rw [show σ - 2 + 1 = -(1 - σ) by ring, neg_div_neg_eq]

theorem integrableOn_pmPowerModel_sqError_div_cube {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (fun x : ℝ => (pmPowerModel σ x - x) ^ 2 / x ^ 3) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by linarith : 2 * σ - 3 < -1) zero_lt_one).congr_fun
    (fun x hx => (pmPowerModel_sqError_div_cube hx).symm) measurableSet_Ioi

theorem integral_pmPowerModel_sqError_div_cube {σ : ℝ} (hσ : σ < 1) :
    (∫ x in Ioi (1 : ℝ), (pmPowerModel σ x - x) ^ 2 / x ^ 3) = 1 / (2 * (1 - σ)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pmPowerModel_sqError_div_cube hx),
    integral_Ioi_rpow_of_lt (by linarith : 2 * σ - 3 < -1) zero_lt_one, Real.one_rpow]
  rw [show 2 * σ - 3 + 1 = -(2 * (1 - σ)) by ring, neg_div_neg_eq]

theorem pmPowerModel_dyadic_difference (σ : ℝ) {x : ℝ} (hx : 2 < x) :
    pmPowerModel σ x - 2 * pmPowerModel σ (x / 2) = (1 - 2 ^ (1 - σ)) * x ^ σ := by
  rw [pmPowerModel, if_neg (by linarith : ¬x ≤ 1), pmPowerModel,
    if_neg (by linarith : ¬x / 2 ≤ 1), Real.div_rpow (by linarith : 0 ≤ x) (by norm_num),
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  ring

theorem pmPowerModel_stretchedLog_bound {σ α : ℝ} (hσ : σ < 1) (hα : α < 1) :
    ∀ᶠ x : ℝ in atTop, |pmPowerModel σ x - x| ≤ x * Real.exp (-(Real.log x) ^ α) := by
  have hp : Tendsto (fun x : ℝ => (Real.log x) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp Real.tendsto_log_atTop
  have hb : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (α - 1) < 1 - σ :=
    hp.eventually (gt_mem_nhds (sub_pos.mpr hσ))
  filter_upwards [hb, eventually_gt_atTop 1] with x hb hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hl : 0 < Real.log x := Real.log_pos hx
  rw [Real.rpow_sub_one hl.ne'] at hb
  have hmul := (div_lt_iff₀ hl).mp hb
  rw [pmPowerModel, if_neg (not_le.mpr hx), add_sub_cancel_left,
    abs_of_nonneg (Real.rpow_nonneg hx0.le σ)]
  calc
    _ = Real.exp (Real.log x * σ) := Real.rpow_def_of_pos hx0 σ
    _ ≤ Real.exp (Real.log x - (Real.log x) ^ α) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log hx0, Real.exp_neg, div_eq_mul_inv]

end RHTower
