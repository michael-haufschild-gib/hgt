import GaloisForLFunctions.RHTower.Sieve.MoebiusWidthTwo

/-!
# Absorbing the price of the smoothing into the saving

At the balanced width the rate's coefficient is `(N/H + 2)² = exp(t/27)` up to a constant, while
the saving is `exp(-t/18)`.  Their product is `exp(-t/54)`, and the polynomial factor `t²` costs a
further halving of the exponent.  What is left is

```text
exp( -(log N)^{1/3} / 108 ).
```

The shift from `N` to `N + H + 1` costs nothing: the logarithm at most doubles, so `t ≤ s ≤ 2t`.
-/

namespace RHTower.Sieve

open Filter Topology

/-- The square of a shifted exponential. -/
theorem sq_ratio_le {N : ℝ} (hN : 1 ≤ Real.log N) :
    (smoothRatioTwo N + 2) ^ 2 ≤ 9 * Real.exp ((Real.log N) ^ ((1 : ℝ) / 3) / 27) := by
  have h1 : (1 : ℝ) ≤ smoothRatioTwo N := one_le_smoothRatioTwo hN
  have h0 : (0 : ℝ) < smoothRatioTwo N := smoothRatioTwo_pos N
  have hsq : smoothRatioTwo N ^ 2 = Real.exp ((Real.log N) ^ ((1 : ℝ) / 3) / 27) := by
    rw [smoothRatioTwo, sq, ← Real.exp_add]
    ring_nf
  have hle : smoothRatioTwo N + 2 ≤ 3 * smoothRatioTwo N := by linarith
  calc (smoothRatioTwo N + 2) ^ 2 ≤ (3 * smoothRatioTwo N) ^ 2 := by nlinarith
    _ = 9 * smoothRatioTwo N ^ 2 := by ring
    _ = 9 * Real.exp ((Real.log N) ^ ((1 : ℝ) / 3) / 27) := by rw [hsq]

/-- The shifted cutoff at most squares. -/
theorem log_shift_le {N : ℝ} (hN3 : 3 ≤ N) (hN : 1 ≤ Real.log N) :
    Real.log (N + smoothWidthTwo N + 1) ≤ 2 * Real.log N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hH := smoothWidthTwo_le hN0.le hN
  have hH0 : (0 : ℝ) ≤ smoothWidthTwo N := by
    rw [smoothWidthTwo]
    exact div_nonneg hN0.le (smoothRatioTwo_pos N).le
  have hsq : N + smoothWidthTwo N + 1 ≤ N ^ 2 := by nlinarith
  have h1 : Real.log (N + smoothWidthTwo N + 1) ≤ Real.log (N ^ 2) :=
    Real.log_le_log (by linarith) hsq
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

/-- The cube root of the shifted logarithm sits between `t` and `2t`. -/
theorem rpow_shift_le {N : ℝ} (hN3 : 3 ≤ N) (hN : 1 ≤ Real.log N) :
    (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3)
      ≤ 2 * (Real.log N) ^ ((1 : ℝ) / 3) := by
  have hlog := log_shift_le hN3 hN
  have hlog0 : (0 : ℝ) ≤ Real.log (N + smoothWidthTwo N + 1) := by
    have hH0 : (0 : ℝ) ≤ smoothWidthTwo N := by
      rw [smoothWidthTwo]
      exact div_nonneg (by linarith) (smoothRatioTwo_pos N).le
    exact Real.log_nonneg (by linarith)
  calc (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3)
      ≤ (2 * Real.log N) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hlog0 hlog (by norm_num)
    _ = (2 : ℝ) ^ ((1 : ℝ) / 3) * (Real.log N) ^ ((1 : ℝ) / 3) :=
        Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2 * (Real.log N) ^ ((1 : ℝ) / 3) := by
        have h2 : (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
          calc (2 : ℝ) ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one _
        have h3 : (0 : ℝ) ≤ (Real.log N) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
        nlinarith [h2, h3]

/-- The unshifted cube root is the smaller one. -/
theorem rpow_le_shift {N : ℝ} (hN0 : 0 < N) (hN : 1 ≤ Real.log N) :
    (Real.log N) ^ ((1 : ℝ) / 3)
      ≤ (Real.log (N + smoothWidthTwo N + 1)) ^ ((1 : ℝ) / 3) := by
  have hH0 : (0 : ℝ) ≤ smoothWidthTwo N := by
    rw [smoothWidthTwo]
    exact div_nonneg hN0.le (smoothRatioTwo_pos N).le
  exact Real.rpow_le_rpow (by linarith) (Real.log_le_log hN0 (by linarith)) (by norm_num)

/-- **A square is absorbed by an exponential.**  `t² ≤ 216² · exp(t/108)`. -/
theorem sq_le_exp_div {t : ℝ} (ht : 0 ≤ t) : t ^ 2 ≤ 46656 * Real.exp (t / 108) := by
  have h := Real.add_one_le_exp (t / 216)
  have hle : t ≤ 216 * Real.exp (t / 216) := by linarith [Real.exp_pos (t / 216)]
  have hexp : Real.exp (t / 216) ^ 2 = Real.exp (t / 108) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  nlinarith [hle, ht, Real.exp_pos (t / 216), hexp]

/-- Three factors at once. -/
theorem mul_three_le {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : a * b * c ≤ a' * b' * c' := by
  have hab : a * b ≤ a' * b' := mul_le_mul ha hb hb0 (le_trans ha0 ha)
  exact mul_le_mul hab hc hc0 (le_trans (mul_nonneg ha0 hb0) hab)

end RHTower.Sieve
