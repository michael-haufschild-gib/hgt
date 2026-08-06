import GaloisForLFunctions.RHTower.Sieve.ChebyshevRatePowersOne

/-!
# The smoothing width at the width-`1/log` rectangle

The contour bound costs `(N/H)²` and the left edge saves `exp(-√(log N)/80000)`, while replacing
the smoothed Chebyshev sum by the sharp one costs `(H+1)·log(N+H)`.  Writing

```text
chebRatioOne N = exp( √(log N) / 240000 ),      chebWidthOne N = N / chebRatioOne N
```

makes the price `exp(√(log N)/120000)`, leaving `exp(-√(log N)/240000)` on the contour side, and
the comparison costs `N·log N·exp(-√(log N)/240000)` — the same up to the logarithm.

The denominator has to exceed `2 · 80000`: any faster narrowing makes the squared price beat the
saving, and any slower one makes the comparison dominate.
-/

namespace RHTower.Sieve

/-- The smoothing ratio balanced against the width-`1/log` saving. -/
noncomputable def chebRatioOne (N : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log N) / 240000)

/-- The smoothing width. -/
noncomputable def chebWidthOne (N : ℝ) : ℝ := N / chebRatioOne N

theorem chebRatioOne_pos (N : ℝ) : 0 < chebRatioOne N := Real.exp_pos _

theorem one_le_chebRatioOne (N : ℝ) : 1 ≤ chebRatioOne N := by
  rw [chebRatioOne]
  exact Real.one_le_exp (by positivity)

theorem chebWidthOne_le {N : ℝ} (hN0 : 0 ≤ N) : chebWidthOne N ≤ N := by
  rw [chebWidthOne]
  exact div_le_self hN0 (one_le_chebRatioOne N)

theorem chebWidthOne_nonneg {N : ℝ} (hN0 : 0 ≤ N) : 0 ≤ chebWidthOne N := by
  rw [chebWidthOne]
  exact div_nonneg hN0 (chebRatioOne_pos N).le

theorem div_chebWidthOne {N : ℝ} (hN0 : 0 < N) : N / chebWidthOne N = chebRatioOne N := by
  rw [chebWidthOne]
  field_simp

/-- One is at most the square root of a logarithm past one. -/
theorem one_le_sqrt_log {N : ℝ} (hN : 1 ≤ Real.log N) : 1 ≤ Real.sqrt (Real.log N) := by
  have h := Real.sqrt_le_sqrt hN
  rwa [Real.sqrt_one] at h

/-- The square root of a logarithm past one is at most the logarithm. -/
theorem sqrt_log_le_log {N : ℝ} (hN : 1 ≤ Real.log N) :
    Real.sqrt (Real.log N) ≤ Real.log N := by
  have h1 := one_le_sqrt_log hN
  have hsq : Real.sqrt (Real.log N) * Real.sqrt (Real.log N) = Real.log N :=
    Real.mul_self_sqrt (by linarith)
  nlinarith [h1, hsq]

theorem one_le_chebWidthOne {N : ℝ} (hN0 : 0 < N) (hN : 1 ≤ Real.log N) :
    1 ≤ chebWidthOne N := by
  rw [chebWidthOne, le_div_iff₀ (chebRatioOne_pos N), one_mul, chebRatioOne]
  have hle := sqrt_log_le_log hN
  have h1 := one_le_sqrt_log hN
  calc Real.exp (Real.sqrt (Real.log N) / 240000) ≤ Real.exp (Real.log N) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = N := Real.exp_log hN0

/-- The smoothing width, written multiplicatively. -/
theorem chebWidthOne_eq (N : ℝ) :
    chebWidthOne N = N * Real.exp (-(Real.sqrt (Real.log N) / 240000)) := by
  rw [chebWidthOne, chebRatioOne, Real.exp_neg, div_eq_mul_inv]

/-- The square of the smoothing ratio, as an exponential. -/
theorem sq_chebRatioOne_le (N : ℝ) :
    (chebRatioOne N + 2) ^ 2 ≤ 9 * Real.exp (Real.sqrt (Real.log N) / 120000) := by
  have h1 : (1 : ℝ) ≤ chebRatioOne N := one_le_chebRatioOne N
  have hsq : chebRatioOne N ^ 2 = Real.exp (Real.sqrt (Real.log N) / 120000) := by
    rw [chebRatioOne, sq, ← Real.exp_add]
    ring_nf
  calc (chebRatioOne N + 2) ^ 2 ≤ (3 * chebRatioOne N) ^ 2 := by nlinarith
    _ = 9 * chebRatioOne N ^ 2 := by ring
    _ = 9 * Real.exp (Real.sqrt (Real.log N) / 120000) := by rw [hsq]

/-- **A square is absorbed by an exponential, at any rate.**  From `x + 1 ≤ exp x` squared.  The
Möbius chain's `sq_le_exp_div` is the case `k = 108`. -/
theorem sq_le_exp_div_gen {t k : ℝ} (ht : 0 ≤ t) (hk : 0 < k) :
    t ^ 2 ≤ 4 * k ^ 2 * Real.exp (t / k) := by
  have h := Real.add_one_le_exp (t / (2 * k))
  have hle : t ≤ 2 * k * Real.exp (t / (2 * k)) := by
    have hk2 : (0 : ℝ) < 2 * k := by linarith
    have hdiv : t / (2 * k) ≤ Real.exp (t / (2 * k)) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hdiv hk2.le
    have heq : 2 * k * (t / (2 * k)) = t := by field_simp
    linarith [hmul, heq]
  have hexp : Real.exp (t / (2 * k)) ^ 2 = Real.exp (t / k) := by
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  nlinarith [hle, ht, Real.exp_pos (t / (2 * k)), hexp, hk]

end RHTower.Sieve
