import GaloisForLFunctions.HTGeometry.PowerLinearizationBound

/-!
# The repetition limit for scaled power increments

In every geometrically weighted ray norm, the `n`-fold scaled one-parameter
power increment converges to its tangent ray:

`Σ_m |n·((1+t/n)^m - 1) - t·m|·r^m  →  0`  as `n → ∞`,

for every ratio `0 < r < 1` and parameter `t`.  The quadratic linearization
bound gives the termwise estimate `(t²/n)·m²·(e^{|t|/n}r)^m`, and once
`e^{|t|/n} ≤ 1/√r` the series is dominated by `(t²/n)·Σ m²(√r)^m`.

Instantiated at `r = p^{-σ}`, this is the coefficient-side statement that
repeated one-prime Euler-unit increments converge to the coordinate tangent
in every level-`σ` ray topology.
-/

noncomputable section

namespace HTGeometry

open Filter

/-- **Repetition limit in a weighted ray norm**: the scaled power increment
converges to its tangent ray. -/
theorem tendsto_scaled_power_increment_ray
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    Tendsto (fun n : ℕ => ∑' m : ℕ,
      |(n : ℝ) * ((1 + t / n) ^ m - 1) - t * m| * r ^ m)
      atTop (nhds 0) := by
  set q : ℝ := Real.sqrt r with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hr0
  have hqq : q * q = r := Real.mul_self_sqrt hr0.le
  have hq1 : q < 1 := by nlinarith
  have hS : Summable fun m : ℕ => (m : ℝ) ^ 2 * q ^ m := by
    have hnorm : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hq0]
      exact hq1
    exact summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  set S : ℝ := ∑' m : ℕ, (m : ℝ) ^ 2 * q ^ m with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by positivity
  set lam : ℝ := Real.log (1 / q) with hlam
  have hlam0 : 0 < lam := by
    rw [hlam]
    apply Real.log_pos
    rw [lt_div_iff₀ hq0]
    linarith
  -- squeeze between 0 and (t²·S)/n
  apply squeeze_zero'
  · filter_upwards with n
    exact tsum_nonneg fun m => by positivity
  · filter_upwards [eventually_ge_atTop (max 1 ⌈|t| / lam⌉₊)] with n hn
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have htn : |t| / n ≤ lam := by
      have h1 : (⌈|t| / lam⌉₊ : ℝ) ≤ n := by
        exact_mod_cast le_trans (le_max_right _ _) hn
      have h2 : |t| / lam ≤ (n : ℝ) := le_trans (Nat.le_ceil _) h1
      rw [div_le_iff₀ hlam0] at h2
      rw [div_le_iff₀ hn0]
      linarith [h2]
    -- contraction of the perturbed ratio
    have hbase : Real.exp (|t| / n) * r ≤ q := by
      have h1 : Real.exp (|t| / n) ≤ Real.exp lam := Real.exp_le_exp.2 htn
      have h2 : Real.exp lam = 1 / q := by
        rw [hlam, Real.exp_log (by positivity)]
      calc Real.exp (|t| / n) * r ≤ (1 / q) * r := by
            rw [← h2]
            exact mul_le_mul_of_nonneg_right h1 hr0.le
        _ = q := by
            field_simp
            nlinarith [hqq]
    have hbase0 : 0 ≤ Real.exp (|t| / n) * r := by positivity
    -- termwise domination
    have hterm : ∀ m : ℕ,
        |(n : ℝ) * ((1 + t / n) ^ m - 1) - t * m| * r ^ m
          ≤ t ^ 2 / n * ((m : ℝ) ^ 2 * q ^ m) := by
      intro m
      have hfactor : (n : ℝ) * ((1 + t / n) ^ m - 1) - t * m
          = (n : ℝ) * ((1 + t / n) ^ m - 1 - m * (t / n)) := by
        field_simp
      rw [hfactor, abs_mul, abs_of_pos hn0]
      have hb := abs_pow_sub_one_sub_le (t / n) m
      have habs : |t / n| = |t| / n := by
        rw [abs_div, abs_of_pos hn0]
      rw [habs] at hb
      calc (n : ℝ) * |(1 + t / n) ^ m - 1 - m * (t / n)| * r ^ m
          ≤ (n : ℝ) * (((m : ℝ) * (|t| / n)) ^ 2
              * Real.exp ((m : ℝ) * (|t| / n))) * r ^ m := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hb hn0.le
        _ = t ^ 2 / n * ((m : ℝ) ^ 2
            * (Real.exp (|t| / n) * r) ^ m) := by
            rw [Real.exp_nat_mul, mul_pow (Real.exp (|t| / n)) r m,
              mul_pow (m : ℝ) (|t| / n) 2, div_pow, sq_abs]
            field_simp
        _ ≤ t ^ 2 / n * ((m : ℝ) ^ 2 * q ^ m) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_left₀ hbase0 hbase m
    -- sum the domination
    have hRS : Summable fun m : ℕ => t ^ 2 / n * ((m : ℝ) ^ 2 * q ^ m) :=
      hS.mul_left _
    have hLS : Summable fun m : ℕ =>
        |(n : ℝ) * ((1 + t / n) ^ m - 1) - t * m| * r ^ m :=
      Summable.of_nonneg_of_le (fun m => by positivity) hterm hRS
    calc (∑' m : ℕ, |(n : ℝ) * ((1 + t / n) ^ m - 1) - t * m| * r ^ m)
        ≤ ∑' m : ℕ, t ^ 2 / n * ((m : ℝ) ^ 2 * q ^ m) :=
          hLS.tsum_le_tsum hterm hRS
      _ = t ^ 2 * S / n := by
          rw [tsum_mul_left, ← hSdef]
          ring
  · exact tendsto_const_div_atTop_nhds_zero_nat (t ^ 2 * S)

end HTGeometry
