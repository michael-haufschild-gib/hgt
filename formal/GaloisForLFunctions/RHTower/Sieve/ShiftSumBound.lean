import GaloisForLFunctions.RHTower.Sieve.WeightedCorrelation

/-!
# The sum over shifts

The interface the off-diagonal consumes, and the bound it gives.

`CorrelationPartialBound f K B` says that every *partial* correlation sum of `f` at every shift
`1 ≤ k ≤ K` is at most `B k`.  Given a weight whose last value plus total variation is at most `W`
at every shift, the whole shift sum obeys

```text
| ∑_{k=1}^{K} ∑_{i<n} w(k,i)·f(i)·f(i+k) | ≤ W·∑_{k=1}^{K} B k .
```

For the fibre kernel `W = O(h)`, so `OffDiagonalVanishes μ hh` reduces to
`∑_{k ≤ 2h} B k = o(h√x)` — the averaged Chowla theorem, in the maximal-partial-sum form that
partial summation requires.
-/

namespace RHTower.Sieve

open Finset

/-- Every partial correlation sum at shift `k ≤ K` is at most `B k`. -/
def CorrelationPartialBound (f : ℕ → ℝ) (K : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K → ∀ j, |∑ i ∈ Finset.range j, f i * f (i + k)| ≤ B k

/-- **The sum over shifts, with the weights stripped.** -/
theorem abs_shift_sum_le {f : ℕ → ℝ} {K n : ℕ} {B : ℕ → ℝ} {W : ℝ}
    (hB : CorrelationPartialBound f K B) (hB0 : ∀ k, 0 ≤ B k)
    {w : ℕ → ℕ → ℝ}
    (hw : ∀ k, 1 ≤ k → k ≤ K →
      |w k (n - 1)| + ∑ i ∈ Finset.range (n - 1), |w k (i + 1) - w k i| ≤ W) :
    |∑ k ∈ Finset.Icc 1 K, ∑ i ∈ Finset.range n, w k i * (f i * f (i + k))|
      ≤ W * ∑ k ∈ Finset.Icc 1 K, B k := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hbase := abs_weighted_correlation_le (g := fun i => f i * f (i + k)) (w := w k)
    (B := B k) (W := |w k (n - 1)|)
    (V := ∑ i ∈ Finset.range (n - 1), |w k (i + 1) - w k i|)
    n (hB0 k) (hB k hk.1 hk.2) le_rfl le_rfl
  refine le_trans hbase ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hw k hk.1 hk.2) (hB0 k)

end RHTower.Sieve
