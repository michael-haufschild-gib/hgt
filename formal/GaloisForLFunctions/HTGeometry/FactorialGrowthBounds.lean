import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Elementary factorial growth bounds

Explicit exponential control of the separated-node interpolation constant:

* `(n/e)^n ≤ n!` from the exponential series;
* `((n+1)/n)^n ≤ e`;
* the packaged bound `(N+1)·2^N·(4(N+1))^N/N! ≤ e^{6(N+1)}`, which is the
  interpolation sup constant at node separation `η = 1/(4(N+1))`.

All bounds are crude but exponential with explicit constants, which is what
limsup-type sampling arguments require.
-/

noncomputable section

namespace HTGeometry

/-- The exponential-series factorial lower bound `n^n e^{-n} ≤ n!`. -/
theorem pow_mul_exp_neg_le_factorial (n : ℕ) :
    (n : ℝ) ^ n * Real.exp (-(n : ℝ)) ≤ (n.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hfac] at h
  have hexp : (0:ℝ) < Real.exp (-(n : ℝ)) := Real.exp_pos _
  calc (n : ℝ) ^ n * Real.exp (-(n : ℝ))
      ≤ (Real.exp (n : ℝ) * (n.factorial : ℝ)) * Real.exp (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right h hexp.le
    _ = (n.factorial : ℝ) * (Real.exp (n : ℝ) * Real.exp (-(n : ℝ))) := by
        ring
    _ = (n.factorial : ℝ) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- `((n+1)/n)^n ≤ e`. -/
theorem succ_div_pow_le_exp_one {n : ℕ} (hn : 1 ≤ n) :
    (((n : ℝ) + 1) / n) ^ n ≤ Real.exp 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : ((n : ℝ) + 1) / n = 1 + 1 / n := by
    field_simp
  have h2 : (1 : ℝ) + 1 / n ≤ Real.exp (1 / n) := by
    have := Real.add_one_le_exp (1 / (n : ℝ))
    linarith
  have h3 : ((1 : ℝ) + 1 / n) ^ n ≤ Real.exp (1 / n) ^ n :=
    pow_le_pow_left₀ (by positivity) h2 n
  rw [h1]
  calc ((1 : ℝ) + 1 / n) ^ n ≤ Real.exp (1 / n) ^ n := h3
    _ = Real.exp ((1 / n) * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ = Real.exp 1 := by
        congr 1
        field_simp

/-- Small exponential comparisons. -/
theorem two_le_exp_one : (2:ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1:ℝ)
  linarith

/-- **The interpolation constant is exponential**: at node separation
`η = 1/(4(N+1))`,
`(N+1) · 2^N / (η^N · N!) ≤ e^{6(N+1)}`. -/
theorem interpolation_constant_le (N : ℕ) :
    ((N : ℝ) + 1) * 2 ^ N
        / ((1 / (4 * ((N : ℝ) + 1))) ^ N * N.factorial)
      ≤ Real.exp (6 * ((N : ℝ) + 1)) := by
  have hN1 : (0:ℝ) < (N : ℝ) + 1 := by positivity
  have hfac : (0:ℝ) < (N.factorial : ℝ) := by positivity
  have hη : (0:ℝ) < (1 / (4 * ((N : ℝ) + 1))) ^ N := by positivity
  -- rewrite the reciprocal power
  have hflip : ((N : ℝ) + 1) * 2 ^ N
      / ((1 / (4 * ((N : ℝ) + 1))) ^ N * N.factorial)
      = ((N : ℝ) + 1) * 2 ^ N * (4 * ((N : ℝ) + 1)) ^ N
        / (N.factorial : ℝ) := by
    rw [div_pow, one_pow]
    field_simp
  rw [hflip]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · have hN0 : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    -- 1/N! ≤ e^N / N^N
    have hfacinv : (1:ℝ) / (N.factorial : ℝ)
        ≤ Real.exp (N : ℝ) / (N : ℝ) ^ N := by
      rw [div_le_div_iff₀ hfac (by positivity)]
      have h := pow_mul_exp_neg_le_factorial N
      calc (1:ℝ) * (N : ℝ) ^ N = (N : ℝ) ^ N := one_mul _
        _ = ((N : ℝ) ^ N * Real.exp (-(N : ℝ))) * Real.exp (N : ℝ) := by
            rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              mul_one]
        _ ≤ (N.factorial : ℝ) * Real.exp (N : ℝ) :=
            mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
        _ = Real.exp (N : ℝ) * (N.factorial : ℝ) := mul_comm _ _
    -- assemble
    have hmain : ((N : ℝ) + 1) * 2 ^ N * (4 * ((N : ℝ) + 1)) ^ N
        / (N.factorial : ℝ)
        ≤ ((N : ℝ) + 1) * 2 ^ N * (4 * ((N : ℝ) + 1)) ^ N
          * (Real.exp (N : ℝ) / (N : ℝ) ^ N) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hfacinv (by positivity)
    refine le_trans hmain ?_
    -- regroup: (N+1)·2^N·4^N·(N+1)^N·e^N/N^N
    have hregroup : ((N : ℝ) + 1) * 2 ^ N * (4 * ((N : ℝ) + 1)) ^ N
        * (Real.exp (N : ℝ) / (N : ℝ) ^ N)
        = ((N : ℝ) + 1) * 2 ^ N * 4 ^ N
          * ((((N : ℝ) + 1) / N) ^ N) * Real.exp (N : ℝ) := by
      rw [mul_pow, div_pow]
      field_simp
    rw [hregroup]
    -- individual exponential bounds
    have e1 : ((N : ℝ) + 1) ≤ Real.exp (N : ℝ) := by
      have := Real.add_one_le_exp ((N : ℝ))
      linarith
    have e2 : (2:ℝ) ^ N ≤ Real.exp (N : ℝ) := by
      calc (2:ℝ) ^ N ≤ (Real.exp 1) ^ N := pow_le_pow_left₀ (by norm_num)
            two_le_exp_one N
        _ = Real.exp (N : ℝ) := by
            rw [← Real.exp_nat_mul, mul_one]
    have e4 : (4:ℝ) ^ N ≤ Real.exp (2 * (N : ℝ)) := by
      have h4 : (4:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
        nlinarith [two_le_exp_one]
      calc (4:ℝ) ^ N ≤ (Real.exp 1 * Real.exp 1) ^ N :=
            pow_le_pow_left₀ (by norm_num) h4 N
        _ = Real.exp (2 * (N : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_nat_mul]
            congr 1
            ring
    have e5 := succ_div_pow_le_exp_one hN
    calc ((N : ℝ) + 1) * 2 ^ N * 4 ^ N * ((((N : ℝ) + 1) / N) ^ N)
          * Real.exp (N : ℝ)
        ≤ Real.exp (N : ℝ) * Real.exp (N : ℝ) * Real.exp (2 * (N : ℝ))
          * Real.exp 1 * Real.exp (N : ℝ) := by
          apply mul_le_mul _ le_rfl (Real.exp_nonneg _) (by positivity)
          apply mul_le_mul _ e5 (by positivity) (by positivity)
          apply mul_le_mul _ e4 (by positivity) (by positivity)
          exact mul_le_mul e1 e2 (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (5 * (N : ℝ) + 1) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (6 * ((N : ℝ) + 1)) := by
          apply Real.exp_le_exp.2
          linarith

end HTGeometry
