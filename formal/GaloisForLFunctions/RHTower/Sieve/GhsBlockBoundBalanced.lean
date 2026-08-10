import GaloisForLFunctions.RHTower.Sieve.GhsBlockShape

/-!
# The per-block bound with the shape eliminated

`ghs_block_perron_bound` gives each block a product of two square roots, one carrying
`(log B − log A + C)/log²(N/B)` and the other `log(N/A) + log 4`.  `ghs_block_shape_le` says their
product is an absolute constant.  Multiplying the two roots into one and applying it leaves

```text
∫_{|y| ≤ n} ‖L(block k)·L(inner)·L(g)·x^s/s‖ dy
  ≤ √( (2π)²·V²x^{2σ}(7/σ²+1)·(5/4)·701
        · [ 1750·(2 + C)(3 + log 4) + (5n/4)·κ_plain·(log(N/A_k) + log 4) ] ) ,
```

in which **`k` appears only inside `κ_plain`'s coefficient** — and `κ_plain` is bounded by
`(log B/log(N/B))²/A`, smaller than any power of `log N` since `A` is a power of `N`.

So every block contributes the same `O(V·x^σ)`, and the sum over the `≍ log log N` blocks is
`O(V·x^σ·log log N)`.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- **The per-block bound, with the block's shape replaced by its absolute bound.** -/
theorem ghs_block_bound_balanced
    {f g : ℕ → ℂ} {n : ℕ} (hf : ∀ i : ℕ, ‖f i‖ ≤ 1)
    {σ x V : ℝ} (hσ : 1 ≤ σ) (hx : 0 < x) (hV : 0 ≤ V)
    (hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I))
    (hgb : ∀ y : ℝ, |y| ≤ (n : ℝ) → ‖LSeries g ((σ : ℂ) + (y : ℝ) * I)‖ ≤ V)
    {N k : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hDk : 2 * ghsScale N k ≤ N)
    (hBN : 2 ≤ N / ghsBlockRight N k)
    (hsq : ∀ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
      (n : ℝ) * (n : ℝ) ≤ (q : ℝ))
    (hbig : ∀ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
      4 ≤ Real.log ((q : ℝ) * (1 / (n : ℝ))))
    {κplain : ℝ} (hκ0 : 0 ≤ κplain)
    (hplain : ∑ q ∈ Nat.primesLE (ghsBlockRight N k) \ Nat.primesLE (ghsBlockLeft N k),
        ‖ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k) q
          * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain) :
    (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
            ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f (N / ghsBlockLeft N k)) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ Real.sqrt ((2 * Real.pi) ^ 2 * (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1)) * ((5 / 4) * 701)
          * (1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))
              + (5 * (n : ℝ) / 4) * κplain
                  * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4))) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  have hDk2 : 2 ≤ ghsScale N k := by
    refine ghsScale_pos hN ?_
    have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    nlinarith [hk1, hmono, hlog2]
  have hA1 : 1 ≤ ghsBlockLeft N k := Nat.div_pos (by omega) (by omega)
  have hAB : ghsBlockLeft N k ≤ ghsBlockRight N k := ghsBlockLeft_le_right hN hk1
  have hM1 : 1 ≤ N / ghsBlockLeft N k := Nat.div_pos ghsBlockLeft_le (by omega)
  have hbase := ghs_block_perron_bound (f := f) (g := g) hf hσ hx hV hgc hgb hn hA1 hAB hBN
    hsq hbig hM1 hplain
  refine le_trans hbase ?_
  -- notation
  set W : ℝ := Real.log (ghsBlockRight N k) - Real.log (ghsBlockLeft N k) with hWdef
  set S : ℝ := Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) with hSdef
  set U : ℝ := Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) with hUdef
  set γ : ℝ := V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1) with hγdef
  obtain ⟨hS1, hWle, hUle⟩ := ghs_block_balanced hN hk hDk
  have hA1R : (1 : ℝ) ≤ ((ghsBlockLeft N k : ℕ) : ℝ) := by exact_mod_cast hA1
  have hW0 : (0 : ℝ) ≤ W := by
    have hle : ((ghsBlockLeft N k : ℕ) : ℝ) ≤ ((ghsBlockRight N k : ℕ) : ℝ) := by
      exact_mod_cast hAB
    rw [hWdef]
    linarith [Real.log_le_log (by linarith) hle]
  have hU0 : (0 : ℝ) ≤ U := by
    rw [hUdef]
    refine Real.log_nonneg ?_
    exact_mod_cast hM1
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC0 := mertensBlockGapConst_nonneg
  have hS0 : (0 : ℝ) < S := by linarith
  have hshape := ghs_block_shape_le hN hk hDk
  -- the two factors, multiplied
  have hP0 : (0 : ℝ) ≤ 2 * Real.pi
      * ((5 * 700 / 4) * (2 * ((W + mertensBlockGapConst) / S ^ 2))
        + (5 * (n : ℝ) / 4) * κplain) := by
    have hq : (0 : ℝ) ≤ (W + mertensBlockGapConst) / S ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ (5 * (n : ℝ) / 4) * κplain := by positivity
    have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    nlinarith [hq, this, hπ]
  rw [← Real.sqrt_mul hP0]
  refine Real.sqrt_le_sqrt ?_
  -- the algebra
  have hA0 : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * γ * ((5 / 4) * 701) := by
    have hγ0 : (0 : ℝ) ≤ γ := by
      rw [hγdef]
      have h1 : (0 : ℝ) ≤ (x ^ σ) ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
      positivity
    positivity
  have hstep : 1750 * (((W + mertensBlockGapConst) / S ^ 2) * (U + Real.log 4))
        + (5 * (n : ℝ) / 4) * κplain * (U + Real.log 4)
      ≤ 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))
        + (5 * (n : ℝ) / 4) * κplain * (U + Real.log 4) := by
    linarith [mul_le_mul_of_nonneg_left hshape (by norm_num : (0 : ℝ) ≤ 1750)]
  have hmul := mul_le_mul_of_nonneg_left hstep hA0
  nlinarith [hmul]

end RHTower.Sieve

end
