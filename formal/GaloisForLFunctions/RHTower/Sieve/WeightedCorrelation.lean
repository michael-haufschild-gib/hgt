import GaloisForLFunctions.RHTower.Sieve.VariationOfDifference

/-!
# Stripping the kernel from a correlation

Assembling the bounded-variation Abel inequality with the telescoping variation of a difference of
monotone functions:

```text
| ∑_{i < n} (u(i) − v(i))·g(i) |
  ≤ B·( |u(n−1) − v(n−1)| + (u(0) − u(n−1)) + (v(0) − v(n−1)) ) ,
```

whenever every partial sum of `g` is at most `B` and `u`, `v` are nonincreasing.

With `g(i) = μ(i)·μ(i+k)` and `u − v` the kernel `K(i+k, i)`, the right-hand side is `B·O(h)`: the
weight's last value and its total swing are both `O(h)`.  So the weighted correlation is `O(h)` times
the largest partial correlation sum, and

```text
OffDiagonalVanishes μ hh  ⟸  ∑_{k ≤ 2h} max_j | ∑_{i < j} μ(i)·μ(i+k) | = o(h√x) ,
```

the averaged Chowla theorem in maximal-partial-sum form.
-/

namespace RHTower.Sieve

open Finset

/-- **A weighted correlation, with the weight stripped.** -/
theorem abs_weighted_correlation_le {g w : ℕ → ℝ} {B W V : ℝ} (n : ℕ) (hB0 : 0 ≤ B)
    (hB : ∀ j, |∑ i ∈ Finset.range j, g i| ≤ B)
    (hW : |w (n - 1)| ≤ W)
    (hV : ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| ≤ V) :
    |∑ i ∈ Finset.range n, w i * g i| ≤ B * (W + V) := by
  refine le_trans (abs_sum_mul_le_of_bounded_partial_bv n hB) ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hB0

/-- **The same, for a difference of nonincreasing weights.** -/
theorem abs_weighted_correlation_le_of_sub_antitone {g u v : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB0 : 0 ≤ B) (hB : ∀ j, |∑ i ∈ Finset.range j, g i| ≤ B)
    (hu : ∀ i, u (i + 1) ≤ u i) (hv : ∀ i, v (i + 1) ≤ v i) :
    |∑ i ∈ Finset.range n, (u i - v i) * g i|
      ≤ B * (|u (n - 1) - v (n - 1)|
          + ((u 0 - u (n - 1)) + (v 0 - v (n - 1)))) := by
  refine abs_weighted_correlation_le n hB0 hB le_rfl ?_
  exact variation_le_of_sub_antitone hu hv (n - 1)

end RHTower.Sieve
