import GaloisForLFunctions.RHTower.Sieve.GhsBlockBoundBalanced

/-!
# The sum over the blocks

Once the plain-mass term is dominated by the main one, the per-block bound is a single constant
times `V·x^σ`, with no dependence on the block index at all:

```text
∫_{|y| ≤ n} ‖L(block k)·L(ghsInner f (N/A_k))·L(g)·x^s/s‖ dy ≤ V·x^σ·ghsBlockConst σ ,
```

so the `K` blocks contribute `K·V·x^σ·ghsBlockConst σ`.  With the geometric scales of
`GhsScaleSequence`, `K ≍ log log N`.

**The inner cutoff is `N/A_k`, one per block.**  That is forced: the second Cauchy–Schwarz factor
contributes `log M + log 4`, and the balance needs it proportional to the block's scale
`log(N/B_k)`, which shrinks geometrically.  A cutoff held fixed at `N` would satisfy the balance
only for the first few blocks.  Consequently the reassembly of the blocks happens at the level of
the arithmetic sum — each block has its own Perron representation — and not by splitting one
integral with a fixed inner factor.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The absolute constant of a balanced block. -/
def ghsBlockConst (σ : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701)
    * (2 * 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))))

theorem ghsBlockConst_nonneg (σ : ℝ) : 0 ≤ ghsBlockConst σ := Real.sqrt_nonneg _

/-- **A balanced block whose plain mass is dominated contributes `V·x^σ` times a constant.** -/
theorem ghs_block_bound_uniform
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
          * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 ≤ κplain)
    (hdom : (5 * (n : ℝ) / 4) * κplain
        * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4)
      ≤ 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))) :
    (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
            ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f (N / ghsBlockLeft N k)) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ V * x ^ σ * ghsBlockConst σ := by
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  refine le_trans (ghs_block_bound_balanced hf hσ hx hV hgc hgb hn hN hk hDk hBN hsq hbig
    hκ0 hplain) ?_
  have hrest : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701)
      * (2 * 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))) := by
    have h7 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
    have hC := mertensBlockGapConst_nonneg
    have hl4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hprod : (0 : ℝ) ≤ (2 + mertensBlockGapConst) * (3 + Real.log 4) := by nlinarith
    positivity
  have hbound : (2 * Real.pi) ^ 2 * (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1)) * ((5 / 4) * 701)
        * (1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4))
            + (5 * (n : ℝ) / 4) * κplain
                * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4))
      ≤ (V * x ^ σ) ^ 2 * ((2 * Real.pi) ^ 2 * (7 / σ ^ 2 + 1) * ((5 / 4) * 701)
          * (2 * 1750 * ((2 + mertensBlockGapConst) * (3 + Real.log 4)))) := by
    have hA0 : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * (V ^ 2 * (x ^ σ) ^ 2 * (7 / σ ^ 2 + 1))
        * ((5 / 4) * 701) := by
      have h7 : (0 : ℝ) ≤ 7 / σ ^ 2 + 1 := by positivity
      positivity
    have hstep := mul_le_mul_of_nonneg_left hdom hA0
    nlinarith [hstep]
  refine le_trans (Real.sqrt_le_sqrt hbound) (le_of_eq ?_)
  rw [ghsBlockConst, Real.sqrt_mul (sq_nonneg (V * x ^ σ)), Real.sqrt_sq (by positivity)]

/-- **The sum over the blocks.** -/
theorem ghs_sum_blocks_bound_le
    {f g : ℕ → ℂ} {σ x V : ℝ} {N n : ℕ} (K : ℕ)
    (hbd : ∀ k, k < K →
      (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
            ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f (N / ghsBlockLeft N k)) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
        ≤ V * x ^ σ * ghsBlockConst σ) :
    ∑ k ∈ Finset.range K,
      (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
        ‖LSeries (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
            ((σ : ℂ) + (y : ℝ) * I)
          * LSeries (ghsInner f (N / ghsBlockLeft N k)) ((σ : ℂ) + (y : ℝ) * I)
          * LSeries g ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ (K : ℝ) * (V * x ^ σ * ghsBlockConst σ) := by
  calc ∑ k ∈ Finset.range K,
        (∫ y in Set.Icc (-(n : ℝ)) ((n : ℝ)),
          ‖LSeries (ghsOuterBlock f N (ghsBlockLeft N k) (ghsBlockRight N k))
              ((σ : ℂ) + (y : ℝ) * I)
            * LSeries (ghsInner f (N / ghsBlockLeft N k)) ((σ : ℂ) + (y : ℝ) * I)
            * LSeries g ((σ : ℂ) + (y : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ ∑ _k ∈ Finset.range K, (V * x ^ σ * ghsBlockConst σ) :=
        Finset.sum_le_sum fun k hk => hbd k (Finset.mem_range.1 hk)
    _ = (K : ℝ) * (V * x ^ σ * ghsBlockConst σ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end RHTower.Sieve

end
