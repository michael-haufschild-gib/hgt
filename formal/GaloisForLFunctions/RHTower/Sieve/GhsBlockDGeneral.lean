import GaloisForLFunctions.RHTower.Sieve.GhsBlockGeneralBound

/-!
# The contribution of an arbitrary block

The block bound of `GhsBlockGeneralBound`, the Perron representation of `ghs_block_D_le` and the
damped size of the long factor compose into a single statement about an arbitrary block `(A, B]`
with an arbitrary inner cutoff `M`:

```text
‖∑_{i ≤ N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
  ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ Γ ,
```

subject to the block's primes exceeding the height, its shape factor being at most `Γ`, its plain
mass being dominated at the same scale, and `E` bounding the Perron truncation.  Nothing in it
refers to the geometric partition, so a partition may be chosen to fit the height: blocks above
`n²`, and the primes below `n²` handled by `norm_sum_Icc_ghs_small_block_le`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **An arbitrary block's contribution, with the long factor's size given by the distance.** -/
theorem ghs_block_D_le_general
    {f : ℕ → ℂ} {Ab Bb M N n z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hA : 1 ≤ Ab) (hAB : Ab ≤ Bb) (hBN : 2 ≤ N / Bb) (hM : 1 ≤ M)
    (hsq : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab, (n : ℝ) * (n : ℝ) ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
      4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))))
    {κplain Γ : ℝ} (hκ0 : 0 ≤ κplain)
    (hplain : ∑ q ∈ Nat.primesLE Bb \ Nat.primesLE Ab,
        ‖ghsOuterBlock f N Ab Bb q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain)
    (hshape : ((Real.log Bb - Real.log Ab + mertensBlockGapConst)
          / (Real.log ((N / Bb : ℕ) : ℝ)) ^ 2) * (Real.log M + Real.log 4) ≤ Γ)
    (hdom : (5 * (n : ℝ) / 4) * κplain * (Real.log M + Real.log 4) ≤ 1750 * Γ)
    {E : ℝ}
    (hE : ‖(∑ i ∈ Finset.Icc 1 (min (Bb * (M * N)) N),
              (LSeries.convolution (ghsOuterBlock f N Ab Bb)
                (LSeries.convolution (ghsInner f M) (truncSeq f N))) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1 (Bb * (M * N)),
                      (LSeries.convolution (ghsOuterBlock f N Ab Bb)
                        (LSeries.convolution (ghsInner f M) (truncSeq f N))) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N Ab Bb)
          (LSeries.convolution (ghsInner f M) f)) i‖
      ≤ E + (1 / (2 * Real.pi))
          * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConstOf σ Γ) := by
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hgc : Continuous fun t : ℝ =>
      LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support (by simp) (fun i h => truncSeq_support h) σ
  have hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      ‖LSeries (truncSeq f N) ((σ : ℂ) + (y : ℝ) * I)‖ ≤ dampedSize σ δ z N := by
    intro y hy
    exact norm_LSeries_truncSeq_line_le_damped hf1 hmul hf hσ hz hδ (T := (n : ℝ)) hunif hN hy
  have hP := ghs_block_bound_general (f := f) (g := truncSeq f N) (x := (N : ℝ) + 1 / 2)
    hf hσ.le hx (dampedSize_nonneg hσ z N) hgc hgb hn hA hAB hBN hM hsq hbig hκ0 hplain
    hshape hdom
  exact ghs_block_D_le (le_trans hA hAB) hM (fun i h => ghsOuterBlock_mem_Icc h)
    (fun i h => ghsInner_mem_Icc h) hE hP

end RHTower.Sieve

end
