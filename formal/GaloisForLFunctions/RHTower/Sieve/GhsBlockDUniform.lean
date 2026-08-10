import GaloisForLFunctions.RHTower.Sieve.GhsMeanValue

/-!
# The block's `D`, with the vertical integral discharged

The last connector.  `ghs_block_D_le` takes the vertical integral as a hypothesis;
`ghs_block_bound_uniform` supplies it.  At the geometric endpoints `A_k = ghsBlockLeft N k`,
`B_k = ghsBlockRight N k`, the inner cutoff `N/A_k`, the third factor `truncSeq f N` and the Perron
cutoff `x = N + ½`, the two match exactly, so

```text
‖∑_{i ≤ N} (block k ⍟ (ghsInner f (N/A_k) ⍟ f))(i)‖
  ≤ E + (1/2π)·V·(N+½)^σ·ghsBlockConst σ ,
```

which is precisely the input `norm_sum_Icc_le_ghs` asks for.  Everything after this point is the
choice of `n` and `σ` and a bound for the Perron truncation error `E`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The block's `D`, with the vertical integral supplied.** -/
theorem ghs_block_D_le_uniform
    {f : ℕ → ℂ} {N n k : ℕ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ V : ℝ} (hσ : 1 ≤ σ) (hV : 0 ≤ V)
    (hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) → ‖LSeries (truncSeq f N) ((σ : ℂ) + (y : ℝ) * I)‖ ≤ V)
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
          * (V * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConst σ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  have hDk2 : 2 ≤ ghsScale N k := by
    refine ghsScale_pos hN ?_
    have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    nlinarith [hk1, hmono, hlog2]
  have hA1 : 1 ≤ ghsBlockLeft N k := Nat.div_pos (by omega) (by omega)
  have hL1 : 1 ≤ N / ghsBlockLeft N k := Nat.div_pos ghsBlockLeft_le (by omega)
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by positivity
  have hgc : Continuous fun t : ℝ =>
      LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support (by simp) (fun i h => truncSeq_support h) σ
  have hP := ghs_block_bound_uniform (f := f) (g := truncSeq f N) (x := (N : ℝ) + 1 / 2)
    hf hσ hx hV hgc hgb hn hN hk hDk hBN hsq hbig hκ0 hplain hdom
  exact ghs_block_D_le hB1 hL1 (fun i h => ghsOuterBlock_mem_Icc h)
    (fun i h => ghsInner_mem_Icc h) hE hP

end RHTower.Sieve

end
