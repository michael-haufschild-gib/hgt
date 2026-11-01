import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsWeylBlock

/-! # Power comparisons for the `5/6` subconvexity line

The fifth-derivative secondary term meets the fourth-derivative main term
at `N=t^(15/53)`, with common exponent `2/53` after the `N^(-5/6)` weight.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The generic fifth-derivative test gives exponent `2/53` on its short-block interval. -/
theorem fiveSixths_fifth_numeric {t n : ℝ} (ht : 1 ≤ t) (hn : 0 < n)
    (hlo : 12 * Real.log t ≤ 53 * Real.log n)
    (hhi : 53 * Real.log n ≤ 15 * Real.log t) :
    3 * t / (8 * Real.pi * n ^ 5) ≤ 1 ∧
      256 * (n * (1024 * (3 * t / (8 * Real.pi * n ^ 5))) ^ (1 / 30 : ℝ) +
        n ^ (7 / 8 : ℝ) * (3 * t / (8 * Real.pi * n ^ 5)) ^ (-(1 / 16 : ℝ))) ≤
        10 ^ 6 * n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨lam, hlam⟩ : ∃ l, l = 3 * t / (8 * Real.pi * n ^ 5) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hupper : lam ≤ t / n ^ 5 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : (3 : ℝ) ≤ 8 * Real.pi := by linarith only [hpi]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 5))]
  have hlower : t / (32 * n ^ 5) ≤ lam := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : 8 * Real.pi ≤ (96 : ℝ) := by linarith only [hpi4]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 5))]
  have hlogUpper : Real.log lam ≤ Real.log t - 5 * Real.log n := by
    have h := Real.log_le_log hlam0 hupper
    rw [Real.log_div ht0.ne' (by positivity), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogLower : Real.log t - Real.log 32 - 5 * Real.log n ≤ Real.log lam := by
    have h := Real.log_le_log (by positivity : 0 < t / (32 * n ^ 5)) hlower
    rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog1024 : 0 ≤ Real.log (1024 : ℝ) := Real.log_nonneg (by norm_num)
  have hlam1 : lam ≤ 1 := by
    refine le_of_log_le_log hlam0 zero_lt_one ?_
    rw [Real.log_one]
    linarith only [hlogUpper, hlo, hlt]
  obtain ⟨Q, hQ⟩ : ∃ q, q = n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hlogQ : Real.log Q = 5 / 6 * Real.log n + 2 / 53 * Real.log t := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow ht0]
  have hA : n * (1024 * lam) ^ (1 / 30 : ℝ) ≤ 1024 * Q := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul hn.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_mul (by norm_num) hlam0.ne', Real.log_mul (by norm_num) hQ0.ne', hlogQ]
    linarith only [hlogUpper, hlt, hlog1024]
  have hB : n ^ (7 / 8 : ℝ) * lam ^ (-(1 / 16 : ℝ)) ≤ 32 * Q := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow hlam0,
      Real.log_mul (by norm_num) hQ0.ne', hlogQ]
    linarith only [hlogLower, hhi, hlog32]
  refine ⟨hlam1, ?_⟩
  rw [show 10 ^ 6 * n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) = 10 ^ 6 * Q by rw [hQ]; ring]
  linarith only [hA, hB, hQ0]

/-- The sharp fourth-derivative bound continues the `2/53` exponent up to square-root length. -/
theorem fiveSixths_fourth_numeric {t n : ℝ} (ht : 1 ≤ t) (hn : 0 < n)
    (hlo : 15 * Real.log t ≤ 53 * Real.log n)
    (hhi : 2 * Real.log n ≤ Real.log t) :
    3 * t / (16 * Real.pi * n ^ 4) ≤ 1 ∧
      224 * (n * (3 * t / (16 * Real.pi * n ^ 4)) ^ (1 / 14 : ℝ) +
        n ^ (3 / 4 : ℝ) * (3 * t / (16 * Real.pi * n ^ 4)) ^ (-(1 / 14 : ℝ))) ≤
        10 ^ 6 * n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  obtain ⟨lam, hlam⟩ : ∃ l, l = 3 * t / (16 * Real.pi * n ^ 4) := ⟨_, rfl⟩
  rw [← hlam]
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hupper : lam ≤ t / n ^ 4 := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : (3 : ℝ) ≤ 16 * Real.pi := by linarith only [hpi]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 4))]
  have hlower : t / (32 * n ^ 4) ≤ lam := by
    rw [hlam, div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : 16 * Real.pi ≤ (96 : ℝ) := by linarith only [hpi4]
    nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg ht0.le (pow_nonneg hn.le 4))]
  have hlogUpper : Real.log lam ≤ Real.log t - 4 * Real.log n := by
    have h := Real.log_le_log hlam0 hupper
    rw [Real.log_div ht0.ne' (by positivity), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogLower : Real.log t - Real.log 32 - 4 * Real.log n ≤ Real.log lam := by
    have h := Real.log_le_log (by positivity : 0 < t / (32 * n ^ 4)) hlower
    rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hlam1 : lam ≤ 1 := by
    refine le_of_log_le_log hlam0 zero_lt_one ?_
    rw [Real.log_one]
    linarith only [hlogUpper, hlo, hlt]
  obtain ⟨Q, hQ⟩ : ∃ q, q = n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hlogQ : Real.log Q = 5 / 6 * Real.log n + 2 / 53 * Real.log t := by
    rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow ht0]
  have hA : n * lam ^ (1 / 14 : ℝ) ≤ Q := by
    refine le_of_log_le_log (by positivity) hQ0 ?_
    rw [Real.log_mul hn.ne' (by positivity), Real.log_rpow hlam0, hlogQ]
    linarith only [hlogUpper, hlo]
  have hB : n ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ)) ≤ 32 * Q := by
    refine le_of_log_le_log (by positivity) (by positivity) ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hn, Real.log_rpow hlam0,
      Real.log_mul (by norm_num) hQ0.ne', hlogQ]
    linarith only [hlogLower, hhi, hlt, hlog32]
  refine ⟨hlam1, ?_⟩
  rw [show 10 ^ 6 * n ^ (5 / 6 : ℝ) * t ^ (2 / 53 : ℝ) = 10 ^ 6 * Q by rw [hQ]; ring]
  linarith only [hA, hB, hQ0]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fiveSixths_fifth_numeric
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.fiveSixths_fourth_numeric
