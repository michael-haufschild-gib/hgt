import GaloisForLFunctions.RHTower.Sieve.BudgetSubstitution

/-!
# Polylogarithmic limits

The substitution produces two shapes: a power of the logarithm with a negative exponent, and a power
of the logarithm against a stretched exponential.  Both vanish.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A power of the logarithm against a stretched exponential of the logarithm. -/
theorem tendsto_rpow_log_mul_exp_neg {c a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c * Real.exp (-((Real.log x) ^ a))) atTop (𝓝 0) := by
  have hgrow := tendsto_exp_rpow_div_rpow (a := a) (k := (1 : ℝ)) (c := c) ha (by norm_num)
  have hcomp := hgrow.comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ =>
      1 / (Real.exp (1 * (Real.log x) ^ a) / (Real.log x) ^ c)) atTop (𝓝 0) := by
    have h := hcomp.inv_tendsto_atTop
    refine h.congr fun x => ?_
    simp only [Pi.inv_apply, Function.comp_apply, one_div]
  refine hinv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hpow : (0 : ℝ) < (Real.log x) ^ c := Real.rpow_pos_of_pos hlogx c
  rw [one_mul, one_div_div, Real.exp_neg]
  field_simp

/-- A negative power of the logarithm vanishes. -/
theorem tendsto_rpow_log_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c) atTop (𝓝 0) := by
  have := tendsto_log_rpow_neg (δ := -c) (by linarith)
  simpa using this

end

end RHTower.Sieve
