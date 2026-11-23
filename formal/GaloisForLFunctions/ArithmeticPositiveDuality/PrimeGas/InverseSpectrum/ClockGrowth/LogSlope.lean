import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Logarithmic slope between two constant multiples of a real power -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private theorem log_power_multiple {C : ℝ} (hC : 0 < C) (p : ℝ) :
    Tendsto (fun t : ℝ => Real.log (C*t^p)/Real.log t) atTop (𝓝 p) := by
  have hz : Tendsto (fun t : ℝ => Real.log C/Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have he := hz.add_const p
  rw [zero_add] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have ht' := zero_lt_one.trans ht
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos ht' p).ne',Real.log_rpow ht',add_div,
    mul_div_cancel_right₀ _ (Real.log_pos ht).ne']

/-- Multiplicative constants disappear from the logarithmic slope of a two-sided power law. -/
theorem log_slope_of_power_bounds {f : ℝ → ℝ} {p a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ t ≥ 1, a*t^p ≤ f t ∧ f t ≤ b*t^p) :
    Tendsto (fun t : ℝ => Real.log (f t)/Real.log t) atTop (𝓝 p) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (log_power_multiple ha p) (log_power_multiple hb p)
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    exact div_le_div_of_nonneg_right (Real.log_le_log (mul_pos ha (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _)) (h t ht.le).1)
      (Real.log_pos ht).le
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
    have hpos := (mul_pos ha (Real.rpow_pos_of_pos (zero_lt_one.trans ht) p)).trans_le (h t ht.le).1
    exact div_le_div_of_nonneg_right (Real.log_le_log hpos (h t ht.le).2) (Real.log_pos ht).le

#print axioms log_slope_of_power_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
