import GaloisForLFunctions.RHTower.Sieve.GhsBlockRatio

/-!
# One constant for every block

The geometric blocks have shape at most `(2 + C)(3 + log 4)` and the trimmed block at most
`(3 + C)(3 + log 4)`, so the larger of the two serves for all of them:

```text
ghsShapeConst := (3 + mertensBlockGapConst)·(3 + log 4) .
```

With that single `Γ` every block of `ghsPart` — the trimmed `(n², ghsBlockRight N 0]` and the
geometric `(A_k, B_k]` for `k ≥ 1` — satisfies the same bound

```text
‖∑_{i ≤ N} (blk ⍟ (ghsInner f M ⍟ f))(i)‖
  ≤ E + (1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst ,
```

and the only remaining input is the Perron truncation error `E` and the size of the height, through
the single inequality `(5/4n)·(16/9)·4^{k+1}·(log N + log 4) ≤ 1750·ghsShapeConst`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The shape constant that serves every block. -/
def ghsShapeConst : ℝ := (3 + mertensBlockGapConst) * (3 + Real.log 4)

theorem ghsShapeConst_nonneg : 0 ≤ ghsShapeConst := by
  rw [ghsShapeConst]
  have hC := mertensBlockGapConst_nonneg
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith

/-- The geometric shape bound, at the constant that also covers the trimmed block. -/
theorem ghs_geometric_shape_le {N k : ℕ} (hN : 1 ≤ N) (hk1 : 1 ≤ k)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N) :
    ((Real.log ((ghsBlockRight N k : ℕ) : ℝ) - Real.log ((ghsBlockLeft N k : ℕ) : ℝ)
          + mertensBlockGapConst)
        / (Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2)
      * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4)
      ≤ ghsShapeConst := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hpow2 : (2 : ℝ) ^ (2 : ℕ) ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hlogN : 2 * Real.log 2 ≤ Real.log N := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by norm_num at hpow2; linarith
    nlinarith [hk, hlog2, h4]
  have hbase := ghs_block_shape_le hN hk (two_mul_ghsScale_le hN hk1 hlogN)
  have hC := mertensBlockGapConst_nonneg
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hwiden : (2 + mertensBlockGapConst) * (3 + Real.log 4) ≤ ghsShapeConst := by
    rw [ghsShapeConst]
    nlinarith
  linarith [hbase, hwiden]

/-- **A geometric block of the partition, packaged.** -/
theorem ghs_block_D_le_geometric
    {f : ℕ → ℂ} {N n k z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 1 ≤ N)
    (hk1 : 1 ≤ k) (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hBN : 2 ≤ N / ghsBlockRight N k)
    (hA2 : n ^ 2 ≤ ghsBlockLeft N k)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * 4 ^ (k + 1) * (Real.log N + Real.log 4)) ≤ 1750 * ghsShapeConst)
    {E : ℝ}
    (hE : ‖(∑ i ∈ Finset.Icc 1
              (min (ghsBlockRight N k * ((N / ghsBlockLeft N k) * N)) N),
              (LSeries.convolution (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
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
          * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
              * ghsBlockConstOf σ ghsShapeConst) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hk1' : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  have hA : 1 ≤ ghsBlockLeft N k := le_trans (Nat.one_le_pow 2 n hn) hA2
  have hAB : ghsBlockLeft N k ≤ ghsBlockRight N k := ghsBlockLeft_le_right hN hk1'
  have hM : 1 ≤ N / ghsBlockLeft N k := Nat.div_pos ghsBlockLeft_le (by omega)
  exact ghs_block_D_le_sized hf1 hmul hf hσ hz hδ hunif hn hne hN hA hAB hBN hM hA2
    (ghs_geometric_shape_le hN hk1 hk)
    (ghs_block_dom_le hN hn hk (Nat.div_le_self N (ghsBlockLeft N k)) hheight) hE

/-- **The trimmed block of the partition, packaged.** -/
theorem ghs_block_D_le_trimmed
    {f : ℕ → ℂ} {N n z : ℕ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ δ : ℝ} (hσ : 1 < σ) (hz : 1 ≤ z) (hδ : 0 ≤ δ)
    (hunif : ∀ y : ℝ, |y| ≤ (n : ℝ) →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z)))
    (hn : 1 ≤ n) (hne : Real.exp 4 ≤ (n : ℝ)) (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (0 + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hBN : 2 ≤ N / ghsBlockRight N 0)
    (hA2 : n ^ 2 ≤ ghsBlockRight N 0)
    (hheight : (5 / (4 * (n : ℝ)))
        * ((16 / 9) * 4 ^ (0 + 1) * (Real.log N + Real.log 4)) ≤ 1750 * ghsShapeConst)
    {E : ℝ}
    (hE : ‖(∑ i ∈ Finset.Icc 1
              (min (ghsBlockRight N 0 * ((N / n ^ 2) * N)) N),
              (LSeries.convolution (ghsOuterBlock f N (n ^ 2) (ghsBlockRight N 0))
                (LSeries.convolution (ghsInner f (N / n ^ 2)) (truncSeq f N))) i)
            - ((1 / (2 * Real.pi) : ℝ) : ℂ)
              * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
                  (∑ i ∈ Finset.Icc 1 (ghsBlockRight N 0 * ((N / n ^ 2) * N)),
                      (LSeries.convolution (ghsOuterBlock f N (n ^ 2) (ghsBlockRight N 0))
                        (LSeries.convolution (ghsInner f (N / n ^ 2)) (truncSeq f N))) i
                        * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                    * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                        / ((σ : ℂ) + (t : ℝ) * I))‖ ≤ E) :
    ‖∑ i ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuterBlock f N (n ^ 2) (ghsBlockRight N 0))
          (LSeries.convolution (ghsInner f (N / n ^ 2)) f)) i‖
      ≤ E + (1 / (2 * Real.pi))
          * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
              * ghsBlockConstOf σ ghsShapeConst) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h8 : 8 * Real.log 2 ≤ Real.log N := by norm_num at hk; linarith
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hn
  have hM : 1 ≤ N / n ^ 2 := by
    refine Nat.div_pos ?_ (by omega)
    exact le_trans hA2 (Nat.div_le_self _ _)
  have hshape : ((Real.log ((ghsBlockRight N 0 : ℕ) : ℝ) - Real.log ((n ^ 2 : ℕ) : ℝ)
          + mertensBlockGapConst)
        / (Real.log ((N / ghsBlockRight N 0 : ℕ) : ℝ)) ^ 2)
      * (Real.log ((N / n ^ 2 : ℕ) : ℝ) + Real.log 4) ≤ ghsShapeConst :=
    ghs_trimmed_shape_le hN hn h8 hA2
  exact ghs_block_D_le_sized hf1 hmul hf hσ hz hδ hunif hn hne hN (by omega) hA2 hBN hM
    le_rfl hshape
    (ghs_block_dom_le hN hn hk (Nat.div_le_self N (n ^ 2)) hheight) hE

end RHTower.Sieve

end
