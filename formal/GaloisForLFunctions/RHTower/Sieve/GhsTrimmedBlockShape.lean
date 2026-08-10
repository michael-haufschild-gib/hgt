import GaloisForLFunctions.RHTower.Sieve.GhsBlockSized

/-!
# The shape of the trimmed block

`ghs_block_shape_le` is stated under `2·ghsScale N k ≤ N`, which at `k = 0` reads `2N ≤ N`: the
geometric shape bound says nothing about the first block.  That is not an oversight of the proof —
the first block of the geometric partition is `(1, N^{1/2}]`, and it is exactly the block that the
height forbids.  The block that replaces it, `(n², ghsBlockRight N 0]`, has to have its shape
proved directly.

Its complementary scale is `⌊N/⌊N/⌊N^{1/2}⌋⌋⌋ ≥ ⌊N^{1/2}⌋`, so

```text
S = log⌊N/B⌋ ≥ log⌊N^{1/2}⌋ ≥ (log N)/2 − log 2 ≥ (3/8)·log N
```

once `log N ≥ 8·log 2`, while both the block's width and the inner range are at most `log N ≤ 3S`.
`block_balance_le` at `κ = κ' = 3` then gives the shape bound `(3 + C)(3 + log 4)` — the same form
as the geometric blocks, with `2` widened to `3`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Every scale is at most `N`. -/
theorem ghsScale_le {N k : ℕ} (hN : 1 ≤ N) : ghsScale N k ≤ N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : (1 : ℝ) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hrpow : (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) ≤ (N : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  rw [Real.rpow_one] at hrpow
  rw [ghsScale]
  calc ⌊(N : ℝ) ^ ((1 : ℝ) / 2 ^ k)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_le_floor hrpow
    _ = N := Nat.floor_natCast N

/-- **The shape of the trimmed first block.** -/
theorem ghs_trimmed_shape_le {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n)
    (hk : 8 * Real.log 2 ≤ Real.log N)
    (hAB : n ^ 2 ≤ ghsBlockRight N 0) :
    ((Real.log ((ghsBlockRight N 0 : ℕ) : ℝ) - Real.log ((n ^ 2 : ℕ) : ℝ)
          + mertensBlockGapConst)
        / (Real.log ((N / ghsBlockRight N 0 : ℕ) : ℝ)) ^ 2)
      * (Real.log ((N / n ^ 2 : ℕ) : ℝ) + Real.log 4)
      ≤ (3 + mertensBlockGapConst) * (3 + Real.log 4) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2d : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogN : (0 : ℝ) < Real.log N := by linarith
  have hk1 : (2 : ℝ) ^ (1 : ℕ) * Real.log 2 ≤ Real.log N := by
    norm_num
    linarith
  -- the complementary scale of the block dominates the square root scale
  have hs1 : 2 ≤ ghsScale N 1 := ghsScale_pos hN hk1
  have hsN : ghsScale N 1 ≤ N := ghsScale_le hN
  have hcomp : ghsScale N 1 ≤ N / ghsBlockRight N 0 :=
    le_div_div (by omega) hsN
  have hcompR : ((ghsScale N 1 : ℕ) : ℝ) ≤ ((N / ghsBlockRight N 0 : ℕ) : ℝ) := by
    exact_mod_cast hcomp
  have hs1R : (2 : ℝ) ≤ ((ghsScale N 1 : ℕ) : ℝ) := by exact_mod_cast hs1
  have hSlow : Real.log ((ghsScale N 1 : ℕ) : ℝ)
      ≤ Real.log ((N / ghsBlockRight N 0 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hcompR
  have hscale := le_log_ghsScale hN hk1
  have hS38 : (3 / 8 : ℝ) * Real.log N ≤ Real.log ((N / ghsBlockRight N 0 : ℕ) : ℝ) := by
    have h1 : Real.log N / 2 ^ (1 : ℕ) - Real.log 2 ≤ Real.log ((ghsScale N 1 : ℕ) : ℝ) := hscale
    have h2 : Real.log 2 ≤ Real.log N / 8 := by linarith
    have h3 : Real.log N / 2 ^ (1 : ℕ) = Real.log N / 2 := by norm_num
    rw [h3] at h1
    linarith [hSlow, h1, h2]
  set S : ℝ := Real.log ((N / ghsBlockRight N 0 : ℕ) : ℝ) with hSdef
  have hS1 : (1 : ℝ) ≤ S := by
    have : (3 / 8 : ℝ) * Real.log N ≥ (3 / 8 : ℝ) * (8 * Real.log 2) := by linarith
    linarith [hS38, hlog2d]
  -- the width and the inner range
  have hBN : ghsBlockRight N 0 ≤ N := Nat.div_le_self _ _
  have hBNR : ((ghsBlockRight N 0 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hBN
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow 2 n hn
  have hn2R : (1 : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hn2
  have hABR : ((n ^ 2 : ℕ) : ℝ) ≤ ((ghsBlockRight N 0 : ℕ) : ℝ) := by exact_mod_cast hAB
  have hW0 : (0 : ℝ) ≤ Real.log ((ghsBlockRight N 0 : ℕ) : ℝ) - Real.log ((n ^ 2 : ℕ) : ℝ) := by
    linarith [Real.log_le_log (by linarith) hABR]
  have hlogB : Real.log ((ghsBlockRight N 0 : ℕ) : ℝ) ≤ Real.log N := by
    refine Real.log_le_log ?_ hBNR
    have : (1 : ℝ) ≤ ((ghsBlockRight N 0 : ℕ) : ℝ) := by linarith
    linarith
  have hlogn2 : (0 : ℝ) ≤ Real.log ((n ^ 2 : ℕ) : ℝ) := Real.log_nonneg hn2R
  have hW3 : Real.log ((ghsBlockRight N 0 : ℕ) : ℝ) - Real.log ((n ^ 2 : ℕ) : ℝ) ≤ 3 * S := by
    linarith [hS38, hlogB, hlogn2]
  have hU0 : (0 : ℝ) ≤ Real.log ((N / n ^ 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hUN : Real.log ((N / n ^ 2 : ℕ) : ℝ) ≤ Real.log N := by
    have hle : ((N / n ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.div_le_self N (n ^ 2)
    rcases eq_or_lt_of_le (Nat.zero_le (N / n ^ 2)) with h | h
    · rw [← h]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · refine Real.log_le_log ?_ hle
      have : (1 : ℝ) ≤ ((N / n ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  have hU3 : Real.log ((N / n ^ 2 : ℕ) : ℝ) ≤ 3 * S := by linarith [hS38, hUN]
  exact block_balance_le hS1 mertensBlockGapConst_nonneg (by norm_num) (by norm_num)
    hW0 hU0 hW3 hU3

/-- **Past the second scale the geometric hypothesis `2·ghsScale N k ≤ N` is automatic.**  It fails
only at `k = 0`, where it reads `2N ≤ N`. -/
theorem two_mul_ghsScale_le {N k : ℕ} (hN : 1 ≤ N) (hk1 : 1 ≤ k)
    (hlog : 2 * Real.log 2 ≤ Real.log N) : 2 * ghsScale N k ≤ N := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : (0 : ℝ) < Real.log N := by linarith
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  have hfrac : (1 : ℝ) / 2 ^ k ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hexp : Real.log 2 + (1 / 2 ^ k) * Real.log N ≤ Real.log N := by
    nlinarith [hfrac, hlogN, hlog]
  have hrw : (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) = Real.exp ((1 / 2 ^ k) * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0]
    ring_nf
  have hmul : 2 * (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) ≤ (N : ℝ) := by
    rw [hrw]
    have hstep : Real.exp (Real.log 2) * Real.exp ((1 / 2 ^ k) * Real.log N)
        ≤ Real.exp (Real.log N) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 hexp
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hN0] at hstep
  have hfl : ((ghsScale N k : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := by
    rw [ghsScale]
    exact Nat.floor_le (Real.rpow_nonneg hN0.le _)
  have : ((2 * ghsScale N k : ℕ) : ℝ) ≤ (N : ℝ) := by
    push_cast
    linarith [hfl, hmul]
  exact_mod_cast this

end RHTower.Sieve

end
