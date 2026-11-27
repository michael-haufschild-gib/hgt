import GaloisForLFunctions.RHTower.RouteEGibbsRapidity

/-! # Location of the elementary reflected-state transition window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Real
open scoped Topology

/-- Tilt in units of the largest elementary energy, with L the
logarithm of that energy. -/
def displacement (c L : ℝ) := log L + log (log L) + c

private theorem log_over_id : Tendsto (fun x : ℝ => log x/x) atTop (𝓝 0) := by
  simpa only [rpow_one] using _root_.RHTower.tendsto_logRpow_div_rpow (a := 1) zero_lt_one 1

theorem displacement_growth (c : ℝ) : Tendsto (displacement c) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_log_atTop
  filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (-c)] with L h
  change -c ≤ log (log L) at h
  unfold displacement
  linarith only [h]

theorem displacement_ratio (c : ℝ) :
    Tendsto (fun L => displacement c L / log L) atTop (𝓝 1) := by
  have h := ((log_over_id.comp tendsto_log_atTop).add (tendsto_log_atTop.const_div_atTop c)).const_add 1
  rw [add_zero,add_zero] at h
  apply h.congr'
  filter_upwards [tendsto_log_atTop.eventually_gt_atTop 0] with L hL
  simp only [displacement,Function.comp_apply]
  field_simp [hL.ne']
  ring

theorem displacement_small (c : ℝ) : Tendsto (fun L => displacement c L/L) atTop (𝓝 0) := by
  have h := (displacement_ratio c).mul log_over_id
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [tendsto_log_atTop.eventually_gt_atTop 0,eventually_gt_atTop (0:ℝ)] with L hL hL'
  field_simp [hL.ne',hL'.ne']

private theorem exp_displacement (c : ℝ) {L : ℝ} (hL : 1<L) :
    exp (displacement c L) = exp c * L * log L := by
  simp only [displacement,exp_add,exp_log (one_pos.trans hL),exp_log (log_pos hL)]
  ring

/-- The shifted tilt balances the exponential edge with the harmonic mass. -/
theorem edge_ratio (c : ℝ) : Tendsto (fun L => exp (displacement c L)/(displacement c L*L))
    atTop (𝓝 (exp c)) := by
  have h : Tendsto (fun _ : ℝ => exp c) atTop (𝓝 (exp c)) := tendsto_const_nhds
  have lim := h.div (displacement_ratio c) one_ne_zero
  rw [div_one] at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),(displacement_growth c).eventually_gt_atTop 0] with L hL hw
  change exp c / (displacement c L/log L) = _
  rw [exp_displacement c hL]
  field_simp [(one_pos.trans hL).ne',(log_pos hL).ne',hw.ne']

/-- The uniform prime quadrature error tends to zero across the entire
transition window, before dividing by the harmonic mass. -/
theorem quadrature_scale (c : ℝ) :
    Tendsto (fun L => |displacement c L| * (2+3*|displacement c L|)*exp (2*|displacement c L|)/exp L)
      atTop (𝓝 0) := by
  have poly := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6
  have top := poly.const_mul 16
  rw [mul_zero] at top
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds top
  · exact Eventually.of_forall fun L => div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
      (by positivity)) (exp_pos _).le) (exp_pos _).le
  · filter_upwards [(displacement_ratio c).eventually_lt_const (by norm_num : (1:ℝ)<2),
      (displacement_growth c).eventually_ge_atTop 0,eventually_gt_atTop (1:ℝ)] with L h hw hL
    rw [abs_of_nonneg hw]
    have Lp := one_pos.trans hL
    have wl := ((div_lt_iff₀ (log_pos hL)).mp h).le
    have wL : displacement c L ≤ 2*L := by linarith only [wl,log_le_sub_one_of_pos Lp]
    have mid : 2+3*displacement c L ≤ 8*L := by linarith only [wL,hL]
    have e : exp (2*displacement c L) ≤ L^4 := by
      calc
        _ ≤ exp (4*log L) := exp_le_exp.mpr (by linarith only [wl])
        _ = (exp (log L))^4 := Real.exp_nat_mul _ 4
        _ = L^4 := by rw [exp_log Lp]
    have prod := mul_le_mul (mul_le_mul wL mid (by positivity) (by positivity)) e
      (exp_pos _).le (by positivity)
    change _ ≤ 16*(L^6*exp (-L))
    rw [exp_neg,←div_eq_mul_inv]
    calc
      _ ≤ (2*L*(8*L)*L^4)/exp L := div_le_div_of_nonneg_right prod (exp_pos _).le
      _ = _ := by ring

#print axioms displacement_growth
#print axioms displacement_ratio
#print axioms displacement_small
#print axioms edge_ratio
#print axioms quadrature_scale

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
