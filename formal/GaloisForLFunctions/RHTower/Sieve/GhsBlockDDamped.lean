import GaloisForLFunctions.RHTower.Sieve.GhsBlockDUniform
import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped

/-!
# The block's `D` with the size supplied by the multiplicative distance

The vertical bound `V` on the long factor is not a free parameter: on the segment `|y| ≤ n` it is
the damped size, and the damping is the multiplicative distance from `f` to the characters
`n ↦ n^{iy}`.  Substituting `norm_LSeries_truncSeq_line_le_damped` for the hypothesis `hgb` of
`ghs_block_D_le_uniform` gives

```text
‖∑_{i ≤ N} (block k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
  ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConst σ ,
```

with `dampedSize σ δ z N ≍ (log z)·e^{−δ²}`.  The bound is uniform in the block index, so summing
over the `≍ log log N` blocks and dividing by `log N` is what `norm_sum_Icc_le_ghs` does.

The height enters only through the range on which the distance is measured: `δ` has to be a lower
bound for `𝔻(f, n^{iy})` on `|y| ≤ n`, and nothing is asked of `f` off that segment.  That is the
reason the uniform hypothesis was stated on a segment rather than on the whole line — no
`f`-independent `V` exists for all `y`, since the distance to a character necessarily degrades as
the character's height grows.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The block's `D`, with `V` the damped size.** -/
theorem ghs_block_D_le_damped
    {f : ℕ → ℂ} {N n k z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hDk : 2 * ghsScale N k ≤ N)
    (hBN : 2 ≤ N / ghsBlockRight N k)
    (hB1 : 1 ≤ ghsBlockRight N k)
    (hsq : ∀ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
      (n : ℝ) * (n : ℝ) ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
      4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))))
    {κplain : ℝ} (hκ0 : 0 ≤ κplain)
    (hplain : ∑ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
        ‖ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k) q
          * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain)
    (hdom : (5 * (n : ℝ) / 4) * κplain
        * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4)
      ≤ 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4)))
    {E : ℝ}
    (hE : ‖(∑ i ∈ Finset.Icc 1 (min (ghsBlockRight N k * ((N / ghsBlockLeft N k) * N)) N),
              (LSeries.convolution
                (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
                (LSeries.convolution (ghsInner f (N / ghsBlockLeft N k)) (truncSeq f N))) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1
                        (ghsBlockRight N k * ((N / ghsBlockLeft N k) * N)),
                      (LSeries.convolution
                        (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
                        (LSeries.convolution (ghsInner f (N / ghsBlockLeft N k))
                          (truncSeq f N))) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
          (LSeries.convolution (ghsInner f (N / ghsBlockLeft N k)) f)) i‖
      ≤ E + (1 / (2 * Real.pi))
          * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConst σ) := by
  refine ghs_block_D_le_uniform hf hσ.le (dampedSize_nonneg hσ z N) ?_ hn hN hk hDk hBN hB1
    hsq hbig hκ0 hplain hdom hE
  intro y hy
  exact norm_LSeries_truncSeq_line_le_damped hf1 hmul hf hσ hz hδ
    (T := (n : ℝ)) hunif hN hy

end RHTower.Sieve

end
