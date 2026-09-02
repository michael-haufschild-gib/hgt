import GaloisForLFunctions.RHTower.Sieve.FibreMovingWindowNormalization
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerSubpowerSchedule

open Filter Topology

namespace RHTower.Sieve

noncomputable section

private theorem tendsto_id_div_log_atTop_for_growingRounding :
    Tendsto (fun z : ℝ => z / Real.log z) atTop atTop := by
  have h0 : Tendsto (fun z : ℝ => Real.log z / z) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa only [Real.rpow_one] using
        (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero) ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
    exact div_pos (Real.log_pos hz) (by linarith)
  have h1 := tendsto_inv_nhdsGT_zero.comp h0
  refine h1.congr fun z => ?_
  simp only [Function.comp_apply]
  rw [inv_div]

theorem tendsto_growingReciprocalMarkerH_atTop :
    Tendsto growingReciprocalMarkerH atTop atTop := by
  have hlog : Tendsto
      (fun x : ℝ => Real.log x / Real.log (Real.log x)) atTop atTop :=
    tendsto_id_div_log_atTop_for_growingRounding.comp Real.tendsto_log_atTop
  have hexp := Real.tendsto_exp_atTop.comp hlog
  change Tendsto (fun x : ℝ => Real.exp (Real.log x / Real.log (Real.log x))) atTop atTop
  simpa only [Function.comp_def] using hexp

theorem tendsto_growingReciprocalMarkerH_div_sqrt :
    Tendsto (fun x : ℝ => growingReciprocalMarkerH x / Real.sqrt x) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (growingReciprocalMarkerH_pos x).le (Real.sqrt_nonneg x)
  · filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 4))] with x hx
    have he4 : 1 < Real.exp 4 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 4)
    have hfourExp : (4 : ℝ) < Real.exp 4 := by
      linarith [Real.add_one_le_exp (4 : ℝ)]
    have hee0 : 0 < Real.exp (Real.exp 4) := Real.exp_pos _
    have hx0 : 0 < x := lt_of_lt_of_le hee0 hx
    have hx1 : 1 < x := lt_of_lt_of_le he4 (le_trans (by
      have : Real.exp 4 < Real.exp (Real.exp 4) := Real.exp_lt_exp.mpr hfourExp
      exact this.le) hx)
    have hlogLower : Real.exp 4 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      exact hx
    have hlog0 : 0 < Real.log x := Real.log_pos hx1
    have hll : 4 ≤ Real.log (Real.log x) := by
      rw [Real.le_log_iff_exp_le hlog0]
      exact hlogLower
    have hll0 : 0 < Real.log (Real.log x) := by linarith
    have hinv : 1 / Real.log (Real.log x) ≤ (1 : ℝ) / 4 := by
      exact one_div_le_one_div_of_le (by norm_num) hll
    have hdiv : Real.log x / Real.log (Real.log x) ≤ Real.log x / 4 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) hlog0.le
    rw [growingReciprocalMarkerH, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, ← Real.exp_sub]
    rw [Real.exp_le_exp]
    nlinarith [hdiv]

theorem tendsto_growingReciprocalMarkerRoundingError :
    Tendsto (fun x : ℝ =>
      (((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
          (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2) /
        (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hsqrtTop : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have hinvSqrt : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp hsqrtTop
  have hinvH : Tendsto (fun x : ℝ => 1 / growingReciprocalMarkerH x) atTop (𝓝 0) :=
    tendsto_one_div_atTop.comp tendsto_growingReciprocalMarkerH_atTop
  have hfactor : Tendsto (fun x : ℝ =>
      (Real.sqrt x + 1) / Real.sqrt x) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlim := hconst.add hinvSqrt
    simpa only [add_zero] using hlim.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
      field_simp)
  have hinner : Tendsto (fun x : ℝ =>
      (growingReciprocalMarkerH x / Real.sqrt x + 1) /
        growingReciprocalMarkerH x) atTop (𝓝 0) := by
    have hlim := hinvSqrt.add hinvH
    simpa only [zero_add] using hlim.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
      have hh0 : growingReciprocalMarkerH x ≠ 0 :=
        ne_of_gt (growingReciprocalMarkerH_pos x)
      field_simp)
  have hmajor : Tendsto (fun x : ℝ =>
      ((Real.sqrt x + 1) / Real.sqrt x) *
        ((growingReciprocalMarkerH x / Real.sqrt x + 1) /
          growingReciprocalMarkerH x) ^ 2) atTop (𝓝 0) := by
    simpa only [one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hfactor.mul (hinner.pow 2)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hh0 : 0 < growingReciprocalMarkerH x := growingReciprocalMarkerH_pos x
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hh0 : 0 < growingReciprocalMarkerH x := growingReciprocalMarkerH_pos x
    have hcard : (((outerBlock x (growingReciprocalMarkerH x)).card : ℕ) : ℝ)
        ≤ Real.sqrt x + 1 :=
      card_outerBlock_le hx (growingReciprocalMarkerH_pos x).le
    have hnum :
        (((outerBlock x (growingReciprocalMarkerH x)).card : ℕ) : ℝ) *
            (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2
          ≤ (Real.sqrt x + 1) *
            (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    have hden : 0 < growingReciprocalMarkerH x ^ 2 * Real.sqrt x := by positivity
    refine (div_le_div_of_nonneg_right hnum hden.le).trans_eq ?_
    field_simp

/-- The rounding term in the exact moving-length normalization also vanishes. -/
theorem tendsto_growingReciprocalMarkerMovingRoundingError :
    Tendsto (fun x : ℝ =>
      (((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
          (growingReciprocalMarkerH x / Real.sqrt x + 2) ^ 2) /
        (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)) atTop (𝓝 0) := by
  have hmajor := tendsto_growingReciprocalMarkerRoundingError.const_mul (4 : ℝ)
  simp only [mul_zero] at hmajor
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hh0 : 0 < growingReciprocalMarkerH x := growingReciprocalMarkerH_pos x
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hh0 : 0 < growingReciprocalMarkerH x := growingReciprocalMarkerH_pos x
    have hr0 : 0 ≤ growingReciprocalMarkerH x / Real.sqrt x := by positivity
    have hsq : (growingReciprocalMarkerH x / Real.sqrt x + 2) ^ 2
        ≤ 4 * (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2 := by
      nlinarith [sq_nonneg (growingReciprocalMarkerH x / Real.sqrt x)]
    have hcard0 : 0 ≤ (((outerBlock x (growingReciprocalMarkerH x)).card : ℕ) : ℝ) := by
      positivity
    have hnum := mul_le_mul_of_nonneg_left hsq hcard0
    have hden : 0 < growingReciprocalMarkerH x ^ 2 * Real.sqrt x := by positivity
    have hdiv := div_le_div_of_nonneg_right hnum hden.le
    calc
      (((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
          (growingReciprocalMarkerH x / Real.sqrt x + 2) ^ 2) /
          (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)
          ≤ ((((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
            (4 * (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2)) /
              (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)) := hdiv
      _ = 4 * ((((outerBlock x (growingReciprocalMarkerH x)).card : ℝ) *
          (growingReciprocalMarkerH x / Real.sqrt x + 1) ^ 2) /
            (growingReciprocalMarkerH x ^ 2 * Real.sqrt x)) := by ring

end

end RHTower.Sieve
