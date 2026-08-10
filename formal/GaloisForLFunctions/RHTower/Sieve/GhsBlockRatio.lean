import GaloisForLFunctions.RHTower.Sieve.GhsTrimmedBlockShape

/-!
# How large the height has to be

The one hypothesis of `ghs_block_D_le_sized` still tied to the block is the domination

```text
(5/4n)·(log B/log⌊N/B⌋)²·(log M + log 4) ≤ 1750·Γ .
```

The ratio in it is bounded by the block's index alone.  The complementary scale of the `k`-th block
is at least `ghsScale N (k+1)`, whose logarithm is at least `(log N)/2^{k+1} − log 2`, and the
threshold `2^{k+1}·4·log 2 ≤ log N` makes the `log 2` at most a quarter of the first term:

```text
log⌊N/B_k⌋ ≥ (3/4)·(log N)/2^{k+1} ,   so   log B_k/log⌊N/B_k⌋ ≤ (4/3)·2^{k+1} .
```

The domination is therefore implied by `(5/4n)·(16/9)·4^{k+1}·(log N + log 4) ≤ 1750·Γ`, which at
`K ≍ log log N` blocks — where `4^{K+1} ≍ (log N)²` — asks only for a height `n ≫ (log N)³`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The block's ratio is bounded by its index.** -/
theorem ghs_block_ratio_le {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N) :
    Real.log ((ghsBlockRight N k : ℕ) : ℝ)
        / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)
      ≤ (4 / 3) * 2 ^ (k + 1) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hlogN : (0 : ℝ) < Real.log N := by nlinarith [hk, hlog2, hpow]
  have hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  -- the complementary scale dominates the next scale
  have hs1 : 2 ≤ ghsScale N (k + 1) := ghsScale_pos hN hk1
  have hsN : ghsScale N (k + 1) ≤ N := ghsScale_le hN
  have hcomp : ghsScale N (k + 1) ≤ N / ghsBlockRight N k := le_div_div (by omega) hsN
  have hcompR : ((ghsScale N (k + 1) : ℕ) : ℝ) ≤ ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    exact_mod_cast hcomp
  have hs1R : (2 : ℝ) ≤ ((ghsScale N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hs1
  have hSlow : Real.log ((ghsScale N (k + 1) : ℕ) : ℝ)
      ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hcompR
  have hscale := le_log_ghsScale hN hk1
  -- the threshold absorbs the floor's `log 2`
  have hlog2small : Real.log 2 ≤ Real.log N / (4 * 2 ^ (k + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hk]
  have hS34 : (3 / 4) * (Real.log N / 2 ^ (k + 1))
      ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    have hdiv : Real.log N / (4 * 2 ^ (k + 1)) = (1 / 4) * (Real.log N / 2 ^ (k + 1)) := by
      field_simp
    rw [hdiv] at hlog2small
    linarith [hSlow, hscale, hlog2small]
  have hS0 : (0 : ℝ) < Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    have : (0 : ℝ) < (3 / 4) * (Real.log N / 2 ^ (k + 1)) := by positivity
    linarith
  -- the numerator is at most `log N`
  have hBN : ghsBlockRight N k ≤ N := Nat.div_le_self _ _
  have hBNR : ((ghsBlockRight N k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hBN
  have hlogB : Real.log ((ghsBlockRight N k : ℕ) : ℝ) ≤ Real.log N := by
    rcases eq_or_lt_of_le (Nat.zero_le (ghsBlockRight N k)) with h | h
    · rw [← h]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · refine Real.log_le_log ?_ hBNR
      have : (1 : ℝ) ≤ ((ghsBlockRight N k : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  rw [div_le_iff₀ hS0]
  calc Real.log ((ghsBlockRight N k : ℕ) : ℝ) ≤ Real.log N := hlogB
    _ = (4 / 3) * 2 ^ (k + 1) * ((3 / 4) * (Real.log N / 2 ^ (k + 1))) := by
        field_simp
    _ ≤ (4 / 3) * 2 ^ (k + 1) * Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left hS34 ?_
        positivity

/-- **The domination hypothesis, reduced to a condition on the height.** -/
theorem ghs_block_dom_le {N n k M : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hM : M ≤ N) {Γ : ℝ}
    (hΓ : (5 / (4 * (n : ℝ))) * ((16 / 9) * 4 ^ (k + 1) * (Real.log N + Real.log 4))
      ≤ 1750 * Γ) :
    (5 / (4 * (n : ℝ)))
        * ((Real.log ((ghsBlockRight N k : ℕ) : ℝ)
              / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2
          * (Real.log M + Real.log 4))
      ≤ 1750 * Γ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hlogN : (0 : ℝ) < Real.log N := by nlinarith [hk, hlog2, hpow]
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hratio := ghs_block_ratio_le hN hk
  have hr0 : (0 : ℝ) ≤ Real.log ((ghsBlockRight N k : ℕ) : ℝ)
      / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    have hnum : (0 : ℝ) ≤ Real.log ((ghsBlockRight N k : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    have hden : (0 : ℝ) ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) :=
      Real.log_natCast_nonneg _
    positivity
  have hsq : (Real.log ((ghsBlockRight N k : ℕ) : ℝ)
        / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2
      ≤ (16 / 9) * 4 ^ (k + 1) := by
    have hstep : (Real.log ((ghsBlockRight N k : ℕ) : ℝ)
          / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2
        ≤ ((4 / 3) * 2 ^ (k + 1)) ^ 2 := by
      refine pow_le_pow_left₀ hr0 hratio 2
    have heq : ((4 / 3 : ℝ) * 2 ^ (k + 1)) ^ 2 = (16 / 9) * 4 ^ (k + 1) := by
      rw [mul_pow, ← pow_mul, mul_comm (k + 1) 2, pow_mul]
      norm_num
    linarith [hstep, heq.le, heq.ge]
  have hMlog : Real.log M + Real.log 4 ≤ Real.log N + Real.log 4 := by
    have hle : ((M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hM
    rcases eq_or_lt_of_le (Nat.zero_le M) with h | h
    · rw [← h]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · have : Real.log M ≤ Real.log N := by
        refine Real.log_le_log ?_ hle
        have : (1 : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      linarith
  have hM0 : (0 : ℝ) ≤ Real.log M + Real.log 4 := by
    have : (0 : ℝ) ≤ Real.log M := Real.log_natCast_nonneg _
    linarith
  have hprod : (Real.log ((ghsBlockRight N k : ℕ) : ℝ)
        / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2 * (Real.log M + Real.log 4)
      ≤ (16 / 9) * 4 ^ (k + 1) * (Real.log N + Real.log 4) := by
    have hpos : (0 : ℝ) ≤ (16 / 9 : ℝ) * 4 ^ (k + 1) := by positivity
    calc (Real.log ((ghsBlockRight N k : ℕ) : ℝ)
          / Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)) ^ 2 * (Real.log M + Real.log 4)
        ≤ ((16 / 9) * 4 ^ (k + 1)) * (Real.log M + Real.log 4) :=
          mul_le_mul_of_nonneg_right hsq hM0
      _ ≤ ((16 / 9) * 4 ^ (k + 1)) * (Real.log N + Real.log 4) :=
          mul_le_mul_of_nonneg_left hMlog hpos
  have hcoef : (0 : ℝ) ≤ 5 / (4 * (n : ℝ)) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hprod hcoef) hΓ

end RHTower.Sieve

end
