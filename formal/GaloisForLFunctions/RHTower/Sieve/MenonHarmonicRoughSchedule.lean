import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRoughMeanSquare

/-!
# Explicit schedule for Menon's harmonic rough remainder

The final-range harmonic rough energy is eventually bounded by the same negative eighth
logarithmic power used by the exact ladder-defect budget.  This is the explicit eventual form of
the existing unconditional little-oh theorem.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- Menon's actual final-range harmonic rough energy is eventually at most eight negative
logarithmic powers. -/
theorem eventually_menonFinalRangeHarmonicRoughEnergy_le_log_rpow_neg_eight :
    ∀ᶠ x : ℝ in atTop,
      menonFinalRangeHarmonicRoughEnergy x ≤ (Real.log x) ^ (-(8 : ℝ)) := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      menonFinalRangeHarmonicRoughEnergy x * (Real.log x) ^ 8 < 1 :=
    (tendsto_order.1 tendsto_menonFinalRangeHarmonicRoughEnergy_mul_logPow_zero).2
      1 zero_lt_one
  filter_upwards [hsmall, eventually_gt_atTop (Real.exp 1)] with x hx hxexp
  have hlog0 : 0 < Real.log x := Real.log_pos <| by
    have he1 : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    exact he1.trans hxexp
  have hpow0 : 0 < (Real.log x) ^ (8 : ℕ) := pow_pos hlog0 _
  have hrpow : (Real.log x) ^ (8 : ℝ) = (Real.log x) ^ (8 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [Real.rpow_neg hlog0.le, hrpow, inv_eq_one_div, le_div_iff₀ hpow0]
  exact hx.le

end

end RHTower.Sieve
