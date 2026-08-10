import GaloisForLFunctions.RHTower.Sieve.DyadicMeanSquare

/-!
# The maximal window square, as a dyadic sum of squares

The two halves join.  A window of length at most `H` starting at `y` is a deviation of the partial
sums over at most `H + 1` steps from `y − 1`, so once `H + 1 ≤ 2^J`

```text
maxWindowSq f H y ≤ (maxDev P J (y−1))²
                  ≤ (J + 1)·( blockSq P J 0 (y−1) + ∑_{j < J} blockSq P J j (y−1) ) ,
```

with `P = partialSum f`.  Summing over the starting points turns `MaximalWindowMeanSquare` — the
Matomäki–Radziwiłł hypothesis the whole reduction bottoms out on — into a mean square of Möbius
sums over *dyadic* intervals, with no supremum and no varying window length.

That is the form Gallagher's lemma and the Halász machinery act on.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A window is a deviation of the partial sums. -/
theorem maxWindowSq_le_maxDev_sq (f : ℕ → ℝ) {H J y : ℕ} (hy : 1 ≤ y) (hJ : H + 1 ≤ 2 ^ J) :
    maxWindowSq f H y ≤ (maxDev (partialSum f) J (y - 1)) ^ 2 := by
  rw [maxWindowSq]
  refine Finset.sup'_le _ _ fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [window_eq_partialSum f hy]
  have hidx : y + m = (y - 1) + (m + 1) := by omega
  rw [hidx]
  have hk : m + 1 ≤ 2 ^ J := by omega
  have h1 : |partialSum f ((y - 1) + (m + 1)) - partialSum f (y - 1)|
      ≤ maxDev (partialSum f) J (y - 1) := le_maxDev _ hk
  calc (partialSum f ((y - 1) + (m + 1)) - partialSum f (y - 1)) ^ 2
      = |partialSum f ((y - 1) + (m + 1)) - partialSum f (y - 1)| ^ 2 := (sq_abs _).symm
    _ ≤ (maxDev (partialSum f) J (y - 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- **The maximal window square is a dyadic sum of squares.** -/
theorem maxWindowSq_le_blockSq (f : ℕ → ℝ) {H J y : ℕ} (hy : 1 ≤ y) (hJ : H + 1 ≤ 2 ^ J) :
    maxWindowSq f H y
      ≤ ((J : ℝ) + 1) * (blockSq (partialSum f) J 0 (y - 1)
          + ∑ j ∈ Finset.range J, blockSq (partialSum f) J j (y - 1)) :=
  le_trans (maxWindowSq_le_maxDev_sq f hy hJ) (maxDev_sq_le (partialSum f) J (y - 1))

/-- **The maximal-window mean square, reduced to a dyadic mean square.** -/
theorem sum_maxWindowSq_le (f : ℕ → ℝ) {H J A B : ℕ} (hA : 1 ≤ A) (hJ : H + 1 ≤ 2 ^ J) :
    ∑ y ∈ Finset.Icc A B, maxWindowSq f H y
      ≤ ((J : ℝ) + 1) * ∑ y ∈ Finset.Icc A B,
          (blockSq (partialSum f) J 0 (y - 1)
            + ∑ j ∈ Finset.range J, blockSq (partialSum f) J j (y - 1)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [Finset.mem_Icc] at hy
  exact maxWindowSq_le_blockSq f (le_trans hA hy.1) hJ

end RHTower.Sieve

end
