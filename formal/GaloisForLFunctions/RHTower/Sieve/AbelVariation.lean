import GaloisForLFunctions.RHTower.Sieve.LowerSumAsShifts

/-!
# Abel's inequality with bounded variation

The corpus's `abs_sum_mul_le_of_bounded_partial` needs the weight nonincreasing.  The kernel
`K(n+k, n)` is not: it is a *difference* of two decreasing functions,
`(x + h√x)/(n+k)` and `x/n`, so it has bounded variation but no monotonicity.

Summation by parts does not use monotonicity — it only uses the total variation:

```text
|∑_{i < n} w(i)·g(i)| ≤ B·( |w(n−1)| + ∑_{i < n−1} |w(i+1) − w(i)| ) ,
```

whenever every partial sum of `g` is at most `B`.  The monotone case is the special one where the
variation telescopes to `w(0) − w(n−1)`.

This is what lets the kernel be stripped from the correlation sums of `LowerSumAsShifts`, leaving
`∑_n μ(n)·μ(n+k)` to be quoted from the averaged Chowla theorem.
-/

namespace RHTower.Sieve

open Finset

/-- **Abel's inequality, bounded-variation form.** -/
theorem abs_sum_mul_le_of_bounded_partial_bv {g w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ k, |∑ j ∈ Finset.range k, g j| ≤ B) :
    |∑ i ∈ Finset.range n, w i * g i|
      ≤ B * (|w (n - 1)| + ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hparts := Finset.sum_range_by_parts w g n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  have hhead : |w (n - 1) * ∑ i ∈ Finset.range n, g i| ≤ |w (n - 1)| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg _)
  have htail : |∑ i ∈ Finset.range (n - 1),
      (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j|
      ≤ (∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) * B := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB (i + 1)) (abs_nonneg _)
  calc |w (n - 1) * ∑ i ∈ Finset.range n, g i
          - ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j|
      ≤ |w (n - 1) * ∑ i ∈ Finset.range n, g i|
        + |∑ i ∈ Finset.range (n - 1),
            (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), g j| := abs_sub _ _
    _ ≤ |w (n - 1)| * B + (∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) * B := by
        linarith [hhead, htail]
    _ = B * (|w (n - 1)| + ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) := by ring

end RHTower.Sieve
