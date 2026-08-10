import GaloisForLFunctions.RHTower.Sieve.GhsBlockSumBound

/-!
# Every block of the geometric partition contributes the same amount

The per-block Perron bound is a product of two square roots.  The block-dependent part of the first
is `(log B − log A + C)/log²(N/B)`; of the second, `log(N/A) + log 4`.  Their product is what the
`k`-sum multiplies, and the geometric partition was built so that it does not depend on `k`:

```text
((log B_k − log A_k + C)/log²(N/B_k))·(log(N/A_k) + log 4) ≤ (2 + C)(3 + log 4) ,
```

an absolute constant.  This is `block_balance_le` at the balance constants `κ = 2`, `κ' = 3` that
`ghs_block_balanced` supplies.  Everything else in the per-block bound — `V`, `x^σ`, `7/σ² + 1`,
the two `2π`'s, the numerical factors — is independent of `k` already.

Consequence: the sum over the `≍ log log N` blocks is `log log N` times a constant, which is the
shape the argument needs.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The left endpoint of a block is at most `N`. -/
theorem ghsBlockLeft_le {N k : ℕ} : ghsBlockLeft N k ≤ N := Nat.div_le_self N (ghsScale N k)

/-- **Every block has the same shape.** -/
theorem ghs_block_shape_le {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hDk : 2 * ghsScale N k ≤ N) :
    ((Real.log (ghsBlockRight N k) - Real.log (ghsBlockLeft N k) + mertensBlockGapConst)
        / (Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2)
      * (Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) + Real.log 4)
      ≤ (2 + mertensBlockGapConst) * (3 + Real.log 4) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  obtain ⟨hS1, hW, hU⟩ := ghs_block_balanced hN hk hDk
  -- the two nonnegativity side conditions
  have hDk2 : 2 ≤ ghsScale N k := by
    refine ghsScale_pos hN ?_
    have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [(by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    nlinarith [hk1, hmono, hlog2]
  have hA1 : 1 ≤ ghsBlockLeft N k := Nat.div_pos (by omega) (by omega)
  have hAB : ghsBlockLeft N k ≤ ghsBlockRight N k := ghsBlockLeft_le_right hN hk1
  have hA1R : (1 : ℝ) ≤ ((ghsBlockLeft N k : ℕ) : ℝ) := by exact_mod_cast hA1
  have hW0 : 0 ≤ Real.log (ghsBlockRight N k) - Real.log (ghsBlockLeft N k) := by
    have hle : ((ghsBlockLeft N k : ℕ) : ℝ) ≤ ((ghsBlockRight N k : ℕ) : ℝ) := by
      exact_mod_cast hAB
    linarith [Real.log_le_log (by linarith) hle]
  have hU1 : (1 : ℝ) ≤ ((N / ghsBlockLeft N k : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ N / ghsBlockLeft N k :=
      Nat.div_pos (ghsBlockLeft_le) (by omega)
    exact_mod_cast h
  have hU0 : 0 ≤ Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ) := Real.log_nonneg hU1
  exact block_balance_le hS1 mertensBlockGapConst_nonneg (by norm_num) (by norm_num)
    hW0 hU0 hW hU

end RHTower.Sieve

end
