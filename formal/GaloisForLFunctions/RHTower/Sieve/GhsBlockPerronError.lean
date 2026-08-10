import GaloisForLFunctions.RHTower.Sieve.GhsBlockPackage
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal

/-!
# The block's Perron truncation error

The last input of `ghs_block_D_le_sized` that is not a condition on `N` and `n`.  The block's triple
convolution is prime-supported in its first two factors, so its coefficients are polylogarithmic,
and it is supported in `[1, B·(M·N)]`; the near-diagonal truncated Perron formula then bounds the
discrepancy between the partial sum and the truncated vertical integral:

```text
E = ((log(B·M·N))⁴/(log 2)³)·(N+½)^σ·(5(1 + log(B·M·N)) + 4(1 + log N))/(π·n) .
```

With `B, M ≤ N` the numerator is `≍ N·(log N)⁵`, so the `K ≍ log log N` blocks contribute
`N(log N)⁵·log log N/n` to the capstone, and after division by `log N` this is `o(N)` as soon as
`n ≫ (log N)⁴·log log N`.  Together with the domination's `n ≫ (log N)³`, the height is pinned to a
fixed power of `log N` — and `n ≤ N^{1/4}` from `n² ≤ ghsBlockLeft N 1`, so the two are compatible.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset

/-- The block's outer coefficient obeys the same logarithmic bound as the outer coefficient. -/
theorem norm_ghsOuterBlock_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N A B p : ℕ) :
    ‖ghsOuterBlock f N A B p‖ ≤ (1 / Real.log 2) * Real.log p := by
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [ghsOuterBlock]
  split_ifs with h
  · exact norm_ghsOuter_le hf N p
  · rw [norm_zero]
    positivity

/-- **The block's triple convolution has polylogarithmic coefficients, uniformly.** -/
theorem norm_ghsBlockTriple_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N A B M : ℕ} (i : ℕ) :
    ‖(LSeries.convolution (ghsOuterBlock f N A B)
        (LSeries.convolution (ghsInner f M) (truncSeq f N))) i‖
      ≤ (Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsupp : ∀ k : ℕ, (LSeries.convolution (ghsOuterBlock f N A B)
      (LSeries.convolution (ghsInner f M) (truncSeq f N))) k ≠ 0 →
      k ∈ Finset.Icc 1 (B * (M * N)) := by
    intro k hk
    refine convolution_mem_Icc_of_support_mul (fun j hj => ghsOuterBlock_mem_Icc hj) ?_ hk
    intro j hj
    exact convolution_mem_Icc_of_support_mul (fun i hi => ghsInner_mem_Icc hi)
      (fun i hi => truncSeq_support hi) hj
  by_cases hzero : (LSeries.convolution (ghsOuterBlock f N A B)
      (LSeries.convolution (ghsInner f M) (truncSeq f N))) i = 0
  · rw [hzero, norm_zero]
    have : (0 : ℝ) ≤ Real.log ((B * (M * N) : ℕ) : ℝ) := Real.log_natCast_nonneg _
    positivity
  · have hmem := Finset.mem_Icc.1 (hsupp i hzero)
    have hi1 : 1 ≤ i := hmem.1
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hlogi : (0 : ℝ) ≤ Real.log i := Real.log_nonneg hiR
    have hmono : Real.log i ≤ Real.log ((B * (M * N) : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hmem.2
    have hbase := norm_convolution_triple_le_log_pow_const
      (A := 1 / Real.log 2) (B := 1) (by positivity) zero_le_one
      (fun p hp => prime_of_mem_block (ghsOuterBlock_supp hp)) (norm_ghsOuterBlock_le hf N A B)
      (fun q hq => ghsInner_support hq) (by simpa using norm_ghsInner_le hf M)
      (norm_truncSeq_le hf N) hi1
    refine le_trans hbase ?_
    have hpow : (Real.log i) ^ 4 ≤ (Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hlogi hmono 4
    rw [show (1 / Real.log 2) * 1 * ((Real.log i) ^ 4 / (Real.log 2) ^ 2)
        = (Real.log i) ^ 4 / (Real.log 2) ^ 3 by field_simp]
    exact div_le_div_of_nonneg_right hpow (by positivity)

/-- **The block's Perron truncation error.** -/
theorem ghs_block_perron_error_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N A B M n : ℕ}
    {σ : ℝ} (hσ : 1 ≤ σ) (hn : 1 ≤ n) :
    ‖(∑ i ∈ Finset.Icc 1 (min (B * (M * N)) N),
          (LSeries.convolution (ghsOuterBlock f N A B)
            (LSeries.convolution (ghsInner f M) (truncSeq f N))) i)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ)
          * ∫ t in (-((n : ℝ) * 2 ^ (0 : ℕ)))..((n : ℝ) * 2 ^ (0 : ℕ)),
              (∑ i ∈ Finset.Icc 1 (B * (M * N)),
                  (LSeries.convolution (ghsOuterBlock f N A B)
                    (LSeries.convolution (ghsInner f M) (truncSeq f N))) i
                    * ((i : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
                * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                    / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ((Real.log ((B * (M * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          * ((N : ℝ) + 1 / 2) ^ σ
          * (5 * (1 + Real.log ((B * (M * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
          / (Real.pi * ((n : ℝ) * 2 ^ (0 : ℕ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hT : (0 : ℝ) < (n : ℝ) * 2 ^ (0 : ℕ) := by positivity
  exact norm_sum_Icc_sub_perron_integral_near_le (norm_ghsBlockTriple_le hf) hσ hT

end RHTower.Sieve

end
