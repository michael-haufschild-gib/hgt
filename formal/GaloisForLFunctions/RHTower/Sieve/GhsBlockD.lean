import GaloisForLFunctions.RHTower.Sieve.GhsPartialSumBlocks
import GaloisForLFunctions.RHTower.Sieve.HalaszGhsSharpCutoff

/-!
# The block's contribution `D`

The connector between the capstone and the Perron step.  The capstone asks for a bound on

```text
‖∑_{n ≤ N} (block k ⍟ (ghsInner f (N/a k) ⍟ f))(n)‖ ,
```

with the *untruncated* `f` as third factor, while the Perron step needs all three factors finitely
supported.  Truncating `f` at `N` costs nothing — every index a convolution touches at `n` divides
`n` — and the Perron step's cutoff `min (B'·(L·N)) N` is `N` as soon as `B'` and `L` are positive.

So the block's `D` is exactly `E + (1/2π)·V·(N+½)^σ·C`, with `E` the Perron truncation error and
the second term the cell-aggregate bound.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The block's contribution, with the third factor untruncated.** -/
theorem ghs_block_D_le
    {f : ℕ → ℂ} {A' B' L N n : ℕ} {σ E V C : ℝ}
    (hB' : 1 ≤ B') (hL : 1 ≤ L)
    (hAsupp : ∀ i : ℕ, ghsOuterBlock f N A' B' i ≠ 0 → i ∈ Finset.Icc 1 B')
    (hBsupp : ∀ i : ℕ, ghsInner f L i ≠ 0 → i ∈ Finset.Icc 1 L)
    (hE : ‖(∑ i ∈ Finset.Icc 1 (min (B' * (L * N)) N),
              (LSeries.convolution (ghsOuterBlock f N A' B')
                (LSeries.convolution (ghsInner f L) (truncSeq f N))) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1 (B' * (L * N)),
                      (LSeries.convolution (ghsOuterBlock f N A' B')
                        (LSeries.convolution (ghsInner f L) (truncSeq f N))) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E)
    (hP : (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N A' B') ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f L) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (truncSeq f N) ((σ : ℂ) + (y : ℝ) * I)
          * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I)
              / ((σ : ℂ) + (y : ℝ) * I))‖) ≤ V * ((N : ℝ) + 1 / 2) ^ σ * C) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N A' B')
          (LSeries.convolution (ghsInner f L) f)) i‖
      ≤ E + (1 / (2 * Real.pi)) * (V * ((N : ℝ) + 1 / 2) ^ σ * C) := by
  classical
  have hmin : min (B' * (L * N)) N = N := by
    refine min_eq_right ?_
    calc N = 1 * (1 * N) := by ring
      _ ≤ B' * (L * N) := Nat.mul_le_mul hB' (Nat.mul_le_mul hL le_rfl)
  have htrunc : ∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N A' B')
          (LSeries.convolution (ghsInner f L) f)) i
      = ∑ i ∈ Finset.Icc 1 (min (B' * (L * N)) N),
          (LSeries.convolution (ghsOuterBlock f N A' B')
            (LSeries.convolution (ghsInner f L) (truncSeq f N))) i := by
    rw [hmin]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact convolution_triple_truncSeq_eq_of_le (Finset.mem_Icc.1 hi).2
  rw [htrunc]
  exact ghs_block_sum_perron_le hAsupp hBsupp (fun i h => truncSeq_support h) hE hP

end RHTower.Sieve

end
