import GaloisForLFunctions.RHTower.Sieve.DyadicTranslates

/-!
# The reduction, in one statement

Everything from the maximal window down to fixed-length windows, composed:

```text
∑_{y ∈ [A+1, B+1]} maxWindowSq f H y
  ≤ (J + 1)·( ∑_{i < 2^J} dyadicMeanSquare f 1 (A+i) (B+i)
              + ∑_{j < J} ∑_{i < 2^{J−j}} dyadicMeanSquare f (2^j) (A + i·2^j) (B + i·2^j) )
```

whenever `H + 1 ≤ 2^J`.  The left-hand side is the quantity `MaximalWindowMeanSquare` averages; the
right-hand side involves only `dyadicMeanSquare` at the `J + 1` dyadic lengths `1, 2, …, 2^{J−1}`,
each over `O(2^J)` translates of one range of starting points.

No supremum, no varying length, no unaligned block.  The Matomäki–Radziwiłł input is now a single
estimate for `dyadicMeanSquare μ ℓ A B`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The maximal-window mean square, reduced to fixed-length dyadic mean squares.** -/
theorem sum_maxWindowSq_succ_le_dyadic (f : ℕ → ℝ) {H J A B : ℕ} (hJ : H + 1 ≤ 2 ^ J) :
    ∑ y ∈ Finset.Icc (A + 1) (B + 1), maxWindowSq f H y
      ≤ ((J : ℝ) + 1) *
          ((∑ i ∈ Finset.range (2 ^ J), dyadicMeanSquare f 1 (A + i) (B + i))
            + ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2 ^ (J - j)),
                dyadicMeanSquare f (2 ^ j) (A + i * 2 ^ j) (B + i * 2 ^ j)) := by
  classical
  -- move the range back by one
  have hshift : ∑ y ∈ Finset.Icc (A + 1) (B + 1), maxWindowSq f H y
      = ∑ z ∈ Finset.Icc A B, maxWindowSq f H (z + 1) :=
    (sum_Icc_shift (fun y => maxWindowSq f H y) A B 1).symm
  rw [hshift]
  -- termwise
  have hterm : ∀ z ∈ Finset.Icc A B, maxWindowSq f H (z + 1)
      ≤ ((J : ℝ) + 1) * (blockSq (partialSum f) J 0 z
          + ∑ j ∈ Finset.range J, blockSq (partialSum f) J j z) := by
    intro z _
    have h := maxWindowSq_le_blockSq f (H := H) (J := J) (y := z + 1) (by omega) hJ
    simpa using h
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  -- the two sums of block sums are the translated dyadic mean squares
  rw [Finset.sum_add_distrib]
  congr 1
  · have h0 := sum_blockSq_eq_translates f J 0 A B
    simpa using h0
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sum_blockSq_eq_translates f J j A B

end RHTower.Sieve

end
