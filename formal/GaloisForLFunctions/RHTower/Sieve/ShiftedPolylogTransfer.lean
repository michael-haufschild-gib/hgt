import GaloisForLFunctions.RHTower.Sieve.PowerAbsorbsPolylog

/-!
# Transferring the polylogarithmic comparison to the half-integer cutoff

The Perron cutoff is `N + 1/2`, so every asymptotic statement proved on the reals has to be
composed with `N ↦ N + 1/2` and then compared with `N` itself; the shift costs only the constant
`2^b`.
-/

namespace RHTower.Sieve

open Filter Asymptotics

noncomputable section

theorem tendsto_shift_atTop :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
  Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- The shifted power is comparable to the power. -/
theorem shift_rpow_isBigO {b : ℝ} (hb : 0 ≤ b) :
    (fun N : ℕ => ((N : ℝ) + 1 / 2) ^ b) =O[atTop] fun N : ℕ => (N : ℝ) ^ b := by
  refine Asymptotics.IsBigO.of_bound (2 ^ b) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hle : ((N : ℝ) + 1 / 2) ≤ 2 * (N : ℝ) := by linarith
  have h1 : ((N : ℝ) + 1 / 2) ^ b ≤ (2 * (N : ℝ)) ^ b :=
    Real.rpow_le_rpow (by linarith) hle hb
  have h2 : (2 * (N : ℝ)) ^ b = 2 ^ b * (N : ℝ) ^ b :=
    Real.mul_rpow (by norm_num) hN0.le
  have h3 : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ b := Real.rpow_nonneg (by linarith) b
  have h4 : (0 : ℝ) ≤ (N : ℝ) ^ b := Real.rpow_nonneg hN0.le b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3, abs_of_nonneg h4]
  rw [h2] at h1
  exact h1

/-- **The transferred comparison.**  A shifted power times a polylogarithm is dominated by any
larger power of `N`. -/
theorem isBigO_shift_rpow_log {a b : ℝ} (hab : a < b) (hb : 0 ≤ b) (k : ℕ) :
    (fun N : ℕ => ((N : ℝ) + 1 / 2) ^ a * (Real.log ((N : ℝ) + 1 / 2)) ^ k)
      =O[atTop] fun N : ℕ => (N : ℝ) ^ b := by
  have hbase := (rpow_mul_log_pow_isBigO hab k).comp_tendsto tendsto_shift_atTop
  exact hbase.trans (shift_rpow_isBigO hb)

end

end RHTower.Sieve
