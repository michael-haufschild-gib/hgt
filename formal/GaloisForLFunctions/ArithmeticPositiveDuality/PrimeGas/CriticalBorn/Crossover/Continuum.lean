import GaloisForLFunctions.RHTower.LogIntegralLaplaceComparison
import GaloisForLFunctions.PNTPlus.Consequences

/-! # Large positive and negative tilts of the continuum prime window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Real MeasureTheory
open _root_.RHTower
open scoped Topology Interval

private theorem li_scaled :
    Tendsto (fun x : ℝ => (∫ t in (2:ℝ)..x, 1/log t)*log x/x) atTop (𝓝 1) := by
  obtain ⟨c,hc,eq⟩ := _root_.integral_div_log_asymptotic
  have small : Tendsto c atTop (𝓝 0) := by
    simpa only [div_one] using hc.tendsto_div_nhds_zero
  have lim := small.const_add 1
  rw [add_zero] at lim
  apply lim.congr'
  filter_upwards [eq,eventually_ge_atTop (2:ℝ)] with x hx h2
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le h2] at hx
  rw [hx]
  have h1 : 1<x := by linarith only [h2]
  field_simp [(one_pos.trans h1).ne',(log_pos h1).ne']

private theorem scaled_log : Tendsto (fun w : ℝ => log w*w*exp (-w)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2)
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with w hw
    exact mul_nonneg (mul_nonneg (log_pos hw).le (one_pos.trans hw).le) (exp_pos _).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with w hw
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    rw [sq]
    exact mul_le_mul_of_nonneg_right ((log_le_sub_one_of_pos hw).trans (sub_le_self _ zero_le_one)) hw.le

/-- The positive continuum correction grows as exp(w)/w. -/
theorem continuum_edge : Tendsto (fun w : ℝ => logIntegralCompare w*w/exp w) atTop (𝓝 1) := by
  let K := logIntegralCompare (log 2)+log (log 2)
  have term := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul K
  have lim := (li_scaled.comp tendsto_exp_atTop).add (term.sub scaled_log)
  rw [mul_zero,sub_zero,add_zero] at lim
  apply lim.congr'
  filter_upwards [tendsto_exp_atTop.eventually_ge_atTop 2,eventually_gt_atTop (0:ℝ)] with w h2 hw
  have eq := integral_inv_log_eq_logIntegralCompare h2
  rw [log_exp,log_div hw.ne' (log_pos (by norm_num : (1:ℝ)<2)).ne'] at eq
  simp only [Function.comp_apply,log_exp,pow_one,eq,K,exp_neg]
  ring

/-- The opposite tilt has at most linear loss. -/
theorem negative_continuum_bound {q : ℝ} (hq : 0≤q) : |logIntegralCompare (-q)|≤q := by
  have hle : -q≤0 := neg_nonpos.mpr hq
  have hk (r : ℝ) (hr : r≤0) : logIntegralKernel r≤1 := by
    rcases hr.eq_or_lt with rfl | lt
    · rw [logIntegralKernel_zero]
    · rw [logIntegralKernel_of_ne lt.ne,div_le_iff_of_neg lt,one_mul]
      linarith only [add_one_le_exp r]
  have pos := intervalIntegral.integral_nonneg (μ := volume) hle (fun r _ => (logIntegralKernel_pos r).le)
  have upper := intervalIntegral.integral_mono_on (μ := volume) hle
    (continuous_logIntegralKernel.intervalIntegrable _ _) (intervalIntegrable_const (c:=(1:ℝ)))
    (fun r hr => hk r hr.2)
  rw [logIntegralCompare,intervalIntegral.integral_symm,abs_neg,abs_of_nonneg pos]
  simpa only [intervalIntegral.integral_const,zero_sub,neg_neg,smul_eq_mul,mul_one] using upper

#print axioms continuum_edge
#print axioms negative_continuum_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
