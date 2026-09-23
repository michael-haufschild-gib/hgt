import GaloisForLFunctions.RHTower.Sieve.ChebyshevPowersAtHeight
import GaloisForLFunctions.RHTower.Sieve.WidthFactor

/-!
# The balance: the smoothing's price against the left edge's saving

The contour's coefficient carries `(N/H + 2)²`, which at `chebRatioOne N = exp(√(log N)/240000)`
is at most `9 exp(√(log N)/120000)`.  The left edge saves `chebFactorOne Z = 3 exp(-√(log Z)/80000)`.
Since `N ≤ Z`, their product is

```text
27 · exp( -√(log Z) / 240000 ),
```

because `1/120000 - 1/80000 = -1/240000`.  This is the inequality the whole choice of parameters
exists to make true; the denominator `240000` of the smoothing ratio is exactly what forces it.

The truncation height is not a competitor: `1/T = exp(-2√(log Z))` is already below the saving.
-/

namespace RHTower.Sieve

/-- The truncation height's reciprocal is below the common factor. -/
theorem one_div_chebHeightOne_le_factor (Z : ℝ) :
    1 / chebHeightOne Z ≤ chebFactorOne Z := by
  rw [chebHeightOne, chebFactorOne, one_div, ← Real.exp_neg]
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Z) := Real.sqrt_nonneg _
  have h1 : Real.exp (-(2 * Real.sqrt (Real.log Z)))
      ≤ Real.exp (-(Real.sqrt (Real.log Z) / 80000)) := Real.exp_le_exp.mpr (by linarith)
  nlinarith [h1, Real.exp_pos (-(Real.sqrt (Real.log Z) / 80000))]

/-- The square root of the logarithm is monotone in the cutoff. -/
theorem sqrt_log_le_sqrt_log {N Z : ℝ} (hN0 : 0 < N) (hNZ : N ≤ Z) :
    Real.sqrt (Real.log N) ≤ Real.sqrt (Real.log Z) :=
  Real.sqrt_le_sqrt (Real.log_le_log hN0 hNZ)

/-- **The balance.**  The smoothing's squared price against the left edge's saving leaves
`exp(-√(log Z)/240000)`. -/
theorem price_mul_factor_le {N Z : ℝ} (hN0 : 0 < N) (hNZ : N ≤ Z) :
    9 * Real.exp (Real.sqrt (Real.log N) / 120000) * chebFactorOne Z
      ≤ 27 * Real.exp (-(Real.sqrt (Real.log Z) / 240000)) := by
  rw [chebFactorOne]
  have hmono := sqrt_log_le_sqrt_log hN0 hNZ
  have hsplit : 9 * Real.exp (Real.sqrt (Real.log N) / 120000)
        * (3 * Real.exp (-(Real.sqrt (Real.log Z) / 80000)))
      = 27 * Real.exp (Real.sqrt (Real.log N) / 120000
          + -(Real.sqrt (Real.log Z) / 80000)) := by
    rw [Real.exp_add]
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  linarith [hmono]

/-- **The whole coefficient of the left edge**, in the form the assembly consumes: the width
factor times the common exponential is a constant times `exp(-√(log Z)/240000)`. -/
theorem width_price_le {N H L Cm : ℝ} (hH1 : 1 ≤ H) (hN0 : 0 ≤ N) (hL : N / H ≤ L)
    (hCm : 0 ≤ Cm) (hLb : (L + 2) ^ (2 : ℕ) ≤ 9 * Real.exp (Real.sqrt (Real.log N) / 120000)) :
    Cm / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ)
      ≤ Cm * (9 * Real.exp (Real.sqrt (Real.log N) / 120000)) := by
  refine le_trans (sq_width_factor_le hH1 hN0 hL hCm) ?_
  exact mul_le_mul_of_nonneg_left hLb hCm

end RHTower.Sieve
