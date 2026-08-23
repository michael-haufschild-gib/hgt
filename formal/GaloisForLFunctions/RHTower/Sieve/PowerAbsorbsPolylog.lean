import GaloisForLFunctions.RHTower.Sieve.PerronIntegrandContinuity

/-!
# Powers absorb polylogarithms

`y^a·(log y)^k = O(y^b)` whenever `a < b`: choose `δ = (b−a)/(2k+2)`, use
`log = o(y^δ)` and `y^{a+kδ} = O(y^b)`.
-/

namespace RHTower.Sieve

open Filter Asymptotics

noncomputable section

/-- A power of the logarithm is dominated by every power. -/
theorem log_pow_isBigO_rpow {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    (fun y : ℝ => (Real.log y) ^ k) =O[atTop] fun y : ℝ => y ^ ((k : ℝ) * δ) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    refine Asymptotics.isBigO_of_le _ fun y => ?_
    simp
  | succ k ih =>
    have hlog : Real.log =O[atTop] fun y : ℝ => y ^ δ :=
      (isLittleO_log_rpow_atTop hδ).isBigO
    have hmul := ih.mul hlog
    refine hmul.congr' ?_ ?_
    · filter_upwards with y
      rw [pow_succ]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      rw [← Real.rpow_add hy]
      congr 1
      push_cast
      ring

/-- **Powers absorb polylogarithms.** -/
theorem rpow_mul_log_pow_isBigO {a b : ℝ} (hab : a < b) (k : ℕ) :
    (fun y : ℝ => y ^ a * (Real.log y) ^ k) =O[atTop] fun y : ℝ => y ^ b := by
  set δ : ℝ := (b - a) / (2 * ((k : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    have : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
    positivity
  have hkδ : (k : ℝ) * δ ≤ (b - a) / 2 := by
    rw [hδdef]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hd : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ hd (by norm_num : (0:ℝ) < 2)]
    nlinarith [hk, hab]
  have hbase : (fun y : ℝ => y ^ a * (Real.log y) ^ k)
      =O[atTop] fun y : ℝ => y ^ a * y ^ ((k : ℝ) * δ) :=
    (Asymptotics.isBigO_refl (fun y : ℝ => y ^ a) atTop).mul (log_pow_isBigO_rpow hδ k)
  refine hbase.trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  have hy0 : (0 : ℝ) < y := by linarith
  rw [← Real.rpow_add hy0]
  have hle : a + (k : ℝ) * δ ≤ b := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le hy hle
  have h0 : (0 : ℝ) ≤ y ^ (a + (k : ℝ) * δ) := Real.rpow_nonneg hy0.le _
  have h1 : (0 : ℝ) ≤ y ^ b := Real.rpow_nonneg hy0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1]
  linarith

end

end RHTower.Sieve
