import GaloisForLFunctions.RHTower.Sieve.GhsTopScale

/-!
# The top block costs `O(N)`

The last endpoint of the partition satisfies `⌊N/2048⌋ ≤ ghsPart N n (K+1) ≤ N`, so both quantities
the top block's trivial bound depends on are bounded by absolute constants:

```text
log N − log(ghsPart N n (K+1)) ≤ log 4096 ,     ⌊N/ghsPart N n (K+1)⌋ ≤ 4096 .
```

Hence the top block is at most `N·ghsTopConst`, and `K` of them divided by `N·log N` is
`≍ (log log N)/log N → 0`.  This is the last row of the size table: the interval the geometric
partition cannot reach is short in the multiplicative sense, and short intervals are exactly what
the trivial bound handles well.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- The constant of the top block. -/
def ghsTopConst : ℝ :=
  ((Real.log 4096 + mertensBlockGapConst) / Real.log 2) * (Real.log 4096 + Real.log 4)

/-- **The top block is `O(N)`.** -/
theorem ghs_top_block_le {N n : ℕ} (hN : 65536 ≤ N) (hn2 : n ^ (2 : ℕ) ≤ N) :
    (N : ℝ) * (((1 / Real.log 2)
            * (Real.log (N : ℝ)
                - Real.log ((ghsPart N n (ghsScaleCount N + 1) : ℕ) : ℝ)
                + mertensBlockGapConst))
          * (Real.log ((N / ghsPart N n (ghsScaleCount N + 1) : ℕ) : ℝ) + Real.log 4))
      ≤ (N : ℝ) * ghsTopConst := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hC := mertensBlockGapConst_nonneg
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4096 : (0 : ℝ) ≤ Real.log 4096 := Real.log_nonneg (by norm_num)
  set A : ℕ := ghsPart N n (ghsScaleCount N + 1) with hAdef
  -- the endpoint sits between `⌊N/2048⌋` and `N`
  have hlow : N / 2048 ≤ A := by
    rw [hAdef, ghsPart_succ]
    exact le_trans (ghsBlockLeft_scaleCount_ge hN) (le_max_right _ _)
  have hlow0 : 0 < N / 2048 := by omega
  have hA1 : 1 ≤ A := by omega
  have hAN : A ≤ N := ghsPart_le (by omega) hn2
  have hAR1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
  have hANR : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
  -- the real lower bound
  have hfl : (N : ℝ) / 2048 - 1 < ((N / 2048 : ℕ) : ℝ) := by
    have hlt : N < (N / 2048 + 1) * 2048 := lt_div_add_one_mul (by omega)
    have hltR : (N : ℝ) < (((N / 2048 : ℕ) : ℝ) + 1) * 2048 := by exact_mod_cast hlt
    linarith
  have hbig : (N : ℝ) / 4096 ≤ (A : ℝ) := by
    have hlowR : ((N / 2048 : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hlow
    have h4096 : (1 : ℝ) ≤ (N : ℝ) / 4096 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith [hfl, hlowR, h4096]
  -- the width
  have hwidth : Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) ≤ Real.log 4096 := by
    have hstep : Real.log ((N : ℝ) / 4096) ≤ Real.log ((A : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hbig
    rw [Real.log_div (ne_of_gt hN0) (by norm_num)] at hstep
    linarith
  have hwidth0 : (0 : ℝ) ≤ Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) := by
    have := Real.log_le_log (by linarith : (0:ℝ) < (A:ℝ)) hANR
    linarith [this]
  -- the inner range
  have hdivle : N / A ≤ N / (N / 2048) := Nat.div_le_div_left hlow hlow0
  have hlt2 : N / (N / 2048) < 2 * 2048 := div_div_lt_two_mul (by omega) (by omega)
  have hquot : ((N / A : ℕ) : ℝ) ≤ 4096 := by
    have : N / A ≤ 4096 := by omega
    exact_mod_cast this
  have hlogQ : Real.log ((N / A : ℕ) : ℝ) ≤ Real.log 4096 := by
    rcases eq_or_lt_of_le (Nat.zero_le (N / A)) with h | h
    · rw [← h]
      simp only [Nat.cast_zero, Real.log_zero]
      linarith
    · refine Real.log_le_log ?_ hquot
      have : (1 : ℝ) ≤ ((N / A : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  have hlogQ0 : (0 : ℝ) ≤ Real.log ((N / A : ℕ) : ℝ) := Real.log_natCast_nonneg _
  -- assemble
  refine mul_le_mul_of_nonneg_left ?_ hN0.le
  rw [ghsTopConst]
  have hfirst : (1 / Real.log 2)
        * (Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) + mertensBlockGapConst)
      ≤ (Real.log 4096 + mertensBlockGapConst) / Real.log 2 := by
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ hlog2 hlog2]
    nlinarith [hwidth, hlog2]
  have hfirst0 : (0 : ℝ) ≤ (1 / Real.log 2)
      * (Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) + mertensBlockGapConst) := by
    have : (0 : ℝ) ≤ Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) + mertensBlockGapConst := by
      linarith
    positivity
  have hsecond0 : (0 : ℝ) ≤ Real.log ((N / A : ℕ) : ℝ) + Real.log 4 := by linarith
  have hconst0 : (0 : ℝ) ≤ (Real.log 4096 + mertensBlockGapConst) / Real.log 2 := by
    have : (0 : ℝ) ≤ Real.log 4096 + mertensBlockGapConst := by linarith
    positivity
  calc (1 / Real.log 2)
        * (Real.log (N : ℝ) - Real.log ((A : ℕ) : ℝ) + mertensBlockGapConst)
        * (Real.log ((N / A : ℕ) : ℝ) + Real.log 4)
      ≤ ((Real.log 4096 + mertensBlockGapConst) / Real.log 2)
          * (Real.log ((N / A : ℕ) : ℝ) + Real.log 4) :=
        mul_le_mul_of_nonneg_right hfirst hsecond0
    _ ≤ ((Real.log 4096 + mertensBlockGapConst) / Real.log 2)
          * (Real.log 4096 + Real.log 4) :=
        mul_le_mul_of_nonneg_left (by linarith) hconst0

end RHTower.Sieve

end
