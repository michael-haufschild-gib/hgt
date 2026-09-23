import GaloisForLFunctions.RHTower.Sieve.GhsBlockPerronError

/-!
# Every block, with nothing left open

Composing the packaged block bounds with the Perron truncation error of `GhsBlockPerronError`
removes the last hypothesis that was not a condition on `N` and `n`:

```text
‖∑_{i ≤ N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
  ≤ ghsPerronError N B M n σ
      + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst .
```

Both the trimmed block `(n², ghsBlockRight N 0]` and the geometric blocks `(A_k, B_k]`, `k ≥ 1`,
satisfy it, with the same constant.  What is asked of `N` is a threshold, of the block a left
endpoint above `n²`, and of the height a single inequality.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The Perron truncation error of a block, in closed form. -/
def ghsPerronError (N B M n : ℕ) (σ : ℝ) : ℝ :=
  ((Real.log ((B * (M * N) : ℕ) : ℝ)) ^ (4 : ℕ) / (Real.log 2) ^ (3 : ℕ))
    * ((N : ℝ) + 1 / 2) ^ σ
    * (5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
    / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ)))

/-- **A geometric block, with the truncation error discharged.** -/
theorem ghs_block_D_geometric_explicit
    {f : ℕ → ℂ} {N n k z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 1 ≤ N)
    (hk1 : 1 ≤ k) (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hBN : 2 ≤ N / ghsBlockRight N k)
    (hA2 : n ^ (2 : ℕ) ≤ ghsBlockLeft N k)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * 4 ^ (k + 1) * (Real.log N + Real.log 4)) ≤ 1750 * ghsShapeConst) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
          (LSeries.convolution (ghsInner f (N / ghsBlockLeft N k)) f)) i‖
      ≤ ghsPerronError N (ghsBlockRight N k) (N / ghsBlockLeft N k) n σ
          + (1 / (2 * Real.pi))
            * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                * ghsBlockConstOf σ ghsShapeConst) :=
  ghs_block_D_le_geometric hf1 hmul hf hσ hz hδ hunif hn hne hN hk1 hk hBN hA2 hheight
    (ghs_block_perron_error_le hf hσ.le hn)

/-- **The trimmed block, with the truncation error discharged.** -/
theorem ghs_block_D_trimmed_explicit
    {f : ℕ → ℂ} {N n z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (0 + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hBN : 2 ≤ N / ghsBlockRight N 0)
    (hA2 : n ^ (2 : ℕ) ≤ ghsBlockRight N 0)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * 4 ^ (0 + 1) * (Real.log N + Real.log 4)) ≤ 1750 * ghsShapeConst) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N (n ^ (2 : ℕ)) (ghsBlockRight N 0))
          (LSeries.convolution (ghsInner f (N / n ^ (2 : ℕ))) f)) i‖
      ≤ ghsPerronError N (ghsBlockRight N 0) (N / n ^ (2 : ℕ)) n σ
          + (1 / (2 * Real.pi))
            * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                * ghsBlockConstOf σ ghsShapeConst) :=
  ghs_block_D_le_trimmed hf1 hmul hf hσ hz hδ hunif hn hne hN hk hBN hA2 hheight
    (ghs_block_perron_error_le hf hσ.le hn)

end RHTower.Sieve

end
