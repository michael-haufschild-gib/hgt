import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelDifferenceRenormalization
import GaloisForLFunctions.HTGeometry.LogExpTailIntegral

open Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section

theorem integrableOn_exp_neg_div_id_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi a) := by
  have hmajor := (integrableOn_exp_neg_Ioi a).const_mul a⁻¹
  refine hmajor.mono'
    ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := ha.trans hu
  have hinv : 1 / u ≤ 1 / a := one_div_le_one_div_of_le ha hu.le
  have hinv' : u⁻¹ ≤ a⁻¹ := by simpa only [one_div] using hinv
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hu0]
  rw [div_eq_mul_inv, show a⁻¹ * Real.exp (-u) = Real.exp (-u) * (1 / a) by ring]
  simpa only [one_div] using
    mul_le_mul_of_nonneg_left hinv' (Real.exp_pos _).le

theorem intervalIntegral_exp_neg_div_id_eq
    {a T : ℝ} (ha : 0 < a) (hT : a ≤ T) :
    (∫ u in a..T, Real.exp (-u) / u) =
      (∫ u in a..T, Real.log u * Real.exp (-u)) +
        Real.log T * Real.exp (-T) - Real.log a * Real.exp (-a) := by
  have hu : ∀ x ∈ uIcc a T, HasDerivAt Real.log x⁻¹ x := by
    intro x hx
    rw [uIcc_of_le hT] at hx
    exact Real.hasDerivAt_log (ne_of_gt (ha.trans_le hx.1))
  have hv : ∀ x ∈ uIcc a T,
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    intro x _
    have hcomp := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    change HasDerivAt (fun y : ℝ => Real.exp (-y)) _ x at hcomp
    simpa only [mul_neg, mul_one] using hcomp
  have hu' : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro x hx
    rw [mem_compl_iff, mem_singleton_iff]
    rw [uIcc_of_le hT] at hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hv' : IntervalIntegrable (fun x : ℝ => -Real.exp (-x)) volume a T := by
    have hcont := (Real.continuous_exp.comp continuous_neg).neg
    change Continuous (fun x : ℝ => -Real.exp (-x)) at hcont
    exact hcont.intervalIntegrable a T
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  rw [show (fun x : ℝ => Real.log x * -Real.exp (-x)) =
      fun x => -(Real.log x * Real.exp (-x)) by funext x; ring,
    intervalIntegral.integral_neg] at hip
  have hdiv : (fun x : ℝ => x⁻¹ * Real.exp (-x)) =
      fun x => Real.exp (-x) / x := by
    funext x
    rw [div_eq_mul_inv, mul_comm]
  rw [hdiv] at hip
  linarith

theorem tendsto_log_mul_exp_neg_atTop :
    Tendsto (fun T : ℝ => Real.log T * Real.exp (-T)) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlinexp := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hprod := hlogdiv.mul hlinexp
  have heq : (fun T : ℝ => Real.log T / T * (T ^ (1 : ℕ) * Real.exp (-T))) =ᶠ[atTop]
      fun T => Real.log T * Real.exp (-T) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    simp only [pow_one]
    field_simp
  simpa using hprod.congr' heq

theorem integral_exp_neg_div_id_Ioi_eq_log_tail
    {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi a, Real.exp (-u) / u) =
      (∫ u in Ioi a, Real.log u * Real.exp (-u)) -
        Real.log a * Real.exp (-a) := by
  have hE := intervalIntegral_tendsto_integral_Ioi a
    (integrableOn_exp_neg_div_id_Ioi ha) tendsto_id
  have hL := intervalIntegral_tendsto_integral_Ioi a
    (HTGeometry.integrableOn_log_mul_exp_neg_Ioi ha.le) tendsto_id
  have hR := (hL.add tendsto_log_mul_exp_neg_atTop).sub_const
    (Real.log a * Real.exp (-a))
  have heq : (fun T : ℝ => ∫ u in a..T, Real.exp (-u) / u) =ᶠ[atTop]
      fun T => (∫ u in a..T, Real.log u * Real.exp (-u)) +
        Real.log T * Real.exp (-T) - Real.log a * Real.exp (-a) := by
    filter_upwards [eventually_ge_atTop a] with T hT
    exact intervalIntegral_exp_neg_div_id_eq ha hT
  have hR' := hR.congr' heq.symm
  have huniq := tendsto_nhds_unique hE hR'
  simpa only [add_zero] using huniq

theorem tendsto_integral_exp_neg_div_id_add_log_nhdsGT_zero :
    Tendsto (fun a : ℝ => (∫ u in Ioi a, Real.exp (-u) / u) + Real.log a)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have htail := HTGeometry.tendsto_integral_Ioi_log_mul_exp_neg
  have hsmall : Tendsto (fun a : ℝ =>
      Real.log a * (1 - Real.exp (-a))) (𝓝[>] 0) (𝓝 0) := by
    have hb : ∀ᶠ a : ℝ in 𝓝[>] 0,
        ‖Real.log a * (1 - Real.exp (-a))‖ ≤ |a * Real.log a| := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha0 : 0 < a := ha
      have hexp : |1 - Real.exp (-a)| ≤ a := by
        have h1 : Real.exp (-a) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact neg_nonpos.mpr ha0.le
        have h2 : 1 - a ≤ Real.exp (-a) := by
          have := Real.add_one_le_exp (-a)
          linarith
        rw [abs_of_nonneg (sub_nonneg.mpr h1)]
        linarith
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |Real.log a| * |1 - Real.exp (-a)| ≤ |Real.log a| * a :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = |a * Real.log a| := by rw [abs_mul, abs_of_pos ha0]; ring
    refine squeeze_zero_norm' hb ?_
    have hmul : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
      have h := Real.continuous_mul_log.tendsto (0 : ℝ)
      simpa using h.mono_left nhdsWithin_le_nhds
    simpa using hmul.abs
  have hsum := htail.add hsmall
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [integral_exp_neg_div_id_Ioi_eq_log_tail ha]
  ring

theorem integral_exp_neg_scaled_div_id_Ioi_eq
    {delta R : ℝ} (hdelta : 0 < delta) (_hR : 0 < R) :
    (∫ h in Ioi R, Real.exp (-(delta * h)) / h) =
      ∫ u in Ioi (delta * R), Real.exp (-u) / u := by
  have hcv := integral_comp_mul_left_Ioi
    (fun u : ℝ => Real.exp (-u) / u) R hdelta
  have hpoint : (fun h : ℝ => Real.exp (-(delta * h)) / (delta * h)) =
      fun h => delta⁻¹ * (Real.exp (-(delta * h)) / h) := by
    funext h
    field_simp [hdelta.ne']
  rw [hpoint, integral_const_mul, smul_eq_mul] at hcv
  exact (mul_left_cancel₀ (inv_ne_zero hdelta.ne')) hcv

theorem tendsto_scaled_exp_tail_add_log_nhdsGT_zero
    (R : {R : ℝ // 0 < R}) :
    Tendsto (fun delta : ℝ =>
      (∫ h in Ioi R.1, Real.exp (-(delta * h)) / h) + Real.log delta)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant - Real.log R.1)) := by
  have hscale : Tendsto (fun delta : ℝ => delta * R.1) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun delta : ℝ => delta * R.1) (𝓝 0) (𝓝 (0 * R.1)) :=
        tendsto_id.mul_const R.1
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with delta hdelta
      exact mul_pos hdelta R.2
  have hbase := tendsto_integral_exp_neg_div_id_add_log_nhdsGT_zero.comp hscale
  have hshift := hbase.sub_const (Real.log R.1)
  apply hshift.congr'
  filter_upwards [self_mem_nhdsWithin] with delta hdelta
  simp only [Function.comp_apply]
  rw [integral_exp_neg_scaled_div_id_Ioi_eq hdelta R.2,
    Real.log_mul hdelta.ne' R.2.ne']
  ring

end
end RHTower
