import GaloisForLFunctions.RHTower.Sieve.GhsBlockSumPerron

/-!
# The whole outer range against the blocks, with each block's own inner cutoff

The two arithmetic facts compose: the outer weight telescopes over the blocks, and inside block `k`
the inner weight may be cut at `N/a k` without changing anything.  Together,

```text
∑_{n ≤ M} (outer over (a 0, a K] ⍟ (ghsInner f N ⍟ F))(n)
  = ∑_{k < K} ∑_{n ≤ M} (block k ⍟ (ghsInner f (N/a k) ⍟ F))(n)      (M ≤ N) ,
```

an identity.  Bounding each summand and adding gives the total, `K` times the per-block bound —
and with the geometric scales `K ≍ log log N`.

This is the join between the arithmetic side (`GhsArithmeticBlocks`) and the analytic side
(`GhsBlockSumPerron`): the left-hand side is what the logarithmic recursion produces, the summands
on the right are what the Perron bound estimates.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The outer range telescopes, and each block gets its own inner cutoff.** -/
theorem sum_Icc_convolution_ghsOuterBlock_telescope_trunc (f F : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ}
    (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (K M : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Finset.Icc 1 M,
        (LSeries.convolution (ghsOuterBlock f N (a 0) (a K))
          (LSeries.convolution (ghsInner f N) F)) n
      = ∑ k ∈ Finset.range K,
          ∑ n ∈ Finset.Icc 1 M,
            (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
              (LSeries.convolution (ghsInner f (N / a k)) F)) n := by
  classical
  rw [sum_Icc_convolution_ghsOuterBlock_telescope f
    (LSeries.convolution (ghsInner f N) F) N ha K M]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact convolution_ghsInner_trunc_eq (haA k) (le_trans hn.2 hMN) (by omega) F

/-- **The total is the block count times the per-block bound.** -/
theorem norm_sum_Icc_ghsOuterBlock_blocks_le (f F : ℕ → ℂ) (N : ℕ) {a : ℕ → ℕ}
    (ha : Monotone a) (haA : ∀ k, 1 ≤ a k) (K M : ℕ) (hMN : M ≤ N) {D : ℝ}
    (hbd : ∀ k, k < K →
      ‖∑ n ∈ Finset.Icc 1 M,
        (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
          (LSeries.convolution (ghsInner f (N / a k)) F)) n‖ ≤ D) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (LSeries.convolution (ghsOuterBlock f N (a 0) (a K))
          (LSeries.convolution (ghsInner f N) F)) n‖
      ≤ (K : ℝ) * D := by
  classical
  rw [sum_Icc_convolution_ghsOuterBlock_telescope_trunc f F N ha haA K M hMN]
  calc ‖∑ k ∈ Finset.range K,
          ∑ n ∈ Finset.Icc 1 M,
            (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
              (LSeries.convolution (ghsInner f (N / a k)) F)) n‖
      ≤ ∑ k ∈ Finset.range K,
          ‖∑ n ∈ Finset.Icc 1 M,
            (LSeries.convolution (ghsOuterBlock f N (a k) (a (k + 1)))
              (LSeries.convolution (ghsInner f (N / a k)) F)) n‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, D :=
        Finset.sum_le_sum fun k hk => hbd k (Finset.mem_range.1 hk)
    _ = (K : ℝ) * D := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end RHTower.Sieve

end
