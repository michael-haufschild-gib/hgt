import GaloisForLFunctions.RHTower.Sieve.KernelTurningPoint

/-!
# The smooth kernel rises then falls

The usable form.  With

```text
kernelDiff x h k n = (x + h√x)/(n+k) − x/n ,
```

the increment `kernelDiff(n+1) − kernelDiff(n)` equals `kernelP x h k n` over a positive
denominator, so the sign of the increment is the sign of `kernelP`.  Since `kernelP` is concave with
`kernelP(0) ≥ 0`, `neg_of_concave_of_neg` makes its nonnegativity set an initial segment, and
`kernelDiff` therefore rises and then falls.

That is precisely the hypothesis pair of `variation_le_two_range_of_bimonotone`, whose conclusion —
variation at most twice the range — gives the smooth kernel variation `O(h)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The smooth part of the kernel, before truncation. -/
def kernelDiff (x h : ℝ) (k n : ℕ) : ℝ :=
  (x + h * Real.sqrt x) / ((n : ℝ) + k) - x / (n : ℝ)

/-- Its increment is `kernelP` over a positive denominator. -/
theorem kernelDiff_increment_eq {x h : ℝ} {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    kernelDiff x h k (n + 1) - kernelDiff x h k n
      = kernelP x h k n
          / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + k) * ((n : ℝ) + 1 + k)) := by
  rw [kernelDiff, kernelDiff]
  push_cast
  exact kernel_increment_eq hn hk

/-- The denominator is positive. -/
theorem kernel_increment_den_pos {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + k) * ((n : ℝ) + 1 + k) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  positivity

/-- **Where `kernelP` is nonnegative, the smooth kernel rises.** -/
theorem kernelDiff_mono_of_nonneg {x h : ℝ} {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hP : 0 ≤ kernelP x h k n) :
    kernelDiff x h k n ≤ kernelDiff x h k (n + 1) := by
  have heq := kernelDiff_increment_eq (x := x) (h := h) hn hk
  have hden := kernel_increment_den_pos (k := k) (n := n) hn hk
  have : 0 ≤ kernelDiff x h k (n + 1) - kernelDiff x h k n := by
    rw [heq]
    positivity
  linarith

/-- **Where `kernelP` is nonpositive, the smooth kernel falls.** -/
theorem kernelDiff_anti_of_nonpos {x h : ℝ} {k n : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hP : kernelP x h k n ≤ 0) :
    kernelDiff x h k (n + 1) ≤ kernelDiff x h k n := by
  have heq := kernelDiff_increment_eq (x := x) (h := h) hn hk
  have hden := kernel_increment_den_pos (k := k) (n := n) hn hk
  have hle : kernelDiff x h k (n + 1) - kernelDiff x h k n ≤ 0 := by
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hP hden.le
  linarith

end RHTower.Sieve

end
