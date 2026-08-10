import GaloisForLFunctions.RHTower.Sieve.ConcaveSignSegment

/-!
# The smooth kernel's turning point

Instantiating the concavity lemma.  The smooth kernel's increment is a single quotient whose
denominator is positive, so its sign is the sign of

```text
kernelP x h k n = x(n+k)(n+1+k) − (x + h√x)·n(n+1)
                = −h√x·n² + (2kx − h√x)·n + xk(k+1) ,
```

whose second difference is the constant `−2h√x ≤ 0` and whose value at `0` is `xk(k+1) ≥ 0`.  By
`neg_of_concave_of_neg` the set where it is nonnegative is an initial segment, so the smooth kernel
increases and then decreases — the bimonotonicity that
`variation_le_two_range_of_bimonotone` needs, giving variation `O(h)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The sign-governing quadratic of the smooth kernel's increment. -/
def kernelP (x h : ℝ) (k n : ℕ) : ℝ :=
  x * ((n : ℝ) + k) * ((n : ℝ) + 1 + k) - (x + h * Real.sqrt x) * (n : ℝ) * ((n : ℝ) + 1)

/-- Its second difference is constant. -/
theorem kernelP_second_diff (x h : ℝ) (k n : ℕ) :
    kernelP x h k (n + 2) - 2 * kernelP x h k (n + 1) + kernelP x h k n
      = -2 * (h * Real.sqrt x) := by
  rw [kernelP, kernelP, kernelP]
  push_cast
  ring

/-- Hence it is concave. -/
theorem kernelP_concave {x h : ℝ} (_hx : 0 ≤ x) (hh : 0 ≤ h) (k n : ℕ) :
    kernelP x h k (n + 2) - kernelP x h k (n + 1)
      ≤ kernelP x h k (n + 1) - kernelP x h k n := by
  have hdiff := kernelP_second_diff x h k n
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith [hdiff, mul_nonneg hh hs]

/-- And nonnegative at zero. -/
theorem kernelP_zero_nonneg {x h : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ kernelP x h k 0 := by
  rw [kernelP]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hprod : (0 : ℝ) ≤ x * (k : ℝ) * (1 + k) := by positivity
  push_cast
  nlinarith [hprod]

/-- **The increment of the smooth kernel is `kernelP` over a positive denominator.** -/
theorem kernel_increment_eq {x h : ℝ} {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ((x + h * Real.sqrt x) / (((n : ℝ) + 1) + k) - x / ((n : ℝ) + 1))
        - ((x + h * Real.sqrt x) / ((n : ℝ) + k) - x / (n : ℝ))
      = kernelP x h k n
          / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + k) * ((n : ℝ) + 1 + k)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [kernelP]
  field_simp
  ring

end RHTower.Sieve

end
