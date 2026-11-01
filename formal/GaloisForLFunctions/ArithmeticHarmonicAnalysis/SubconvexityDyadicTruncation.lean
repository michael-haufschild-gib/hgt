import GaloisForLFunctions.RHTower.ZetaCriticalLineWeylBound

/-! # A common finite dyadic truncation for subconvexity bounds

The exponent immediately above `ceil(t²)` gives a polynomial-length
truncation with at most `4 log t` dyadic blocks.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- First dyadic exponent above the square-height cutoff. -/
def zetaDyadicTruncationExponent (t : ℝ) : ℕ := Nat.log 2 ⌈t ^ 2⌉₊ + 1

/-- The square-height cutoff has logarithmically many blocks and lies below `4t²`. -/
theorem zetaDyadicTruncation_bounds {t : ℝ} (ht : 8 ≤ t) :
    t ^ 2 < (2 : ℝ) ^ zetaDyadicTruncationExponent t ∧
      (2 : ℝ) ^ zetaDyadicTruncationExponent t ≤ 4 * t ^ 2 ∧
      (zetaDyadicTruncationExponent t : ℝ) ≤ 4 * Real.log t := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith only [h]
  have hl20 : 0 < Real.log 2 := by linarith only [hl2]
  have hlogt : 2 ≤ Real.log t := by
    have h8 := Real.log_le_log (by norm_num : (0 : ℝ) < 8) ht
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at h8
    norm_num only [Nat.cast_ofNat] at h8
    linarith only [hl2, h8]
  have hq1 : 1 ≤ ⌈t ^ 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]
    positivity)
  have hq2 : (⌈t ^ 2⌉₊ : ℝ) ≤ 2 * t ^ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ t ^ 2 by positivity)
    have hs : (1 : ℝ) ≤ t ^ 2 := by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ht1 2
    linarith only [h, hs]
  have hlower : t ^ 2 < (2 : ℝ) ^ zetaDyadicTruncationExponent t := by
    have hnat : ⌈t ^ 2⌉₊ < 2 ^ zetaDyadicTruncationExponent t := by
      unfold zetaDyadicTruncationExponent
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hc : (⌈t ^ 2⌉₊ : ℝ) < (2 : ℝ) ^ zetaDyadicTruncationExponent t := by exact_mod_cast hnat
    exact (Nat.le_ceil _).trans_lt hc
  have hupper : (2 : ℝ) ^ zetaDyadicTruncationExponent t ≤ 4 * t ^ 2 := by
    unfold zetaDyadicTruncationExponent
    rw [pow_succ]
    have hnat := Nat.pow_log_le_self 2 (show ⌈t ^ 2⌉₊ ≠ 0 by omega)
    have hc : (2 : ℝ) ^ Nat.log 2 ⌈t ^ 2⌉₊ ≤ (⌈t ^ 2⌉₊ : ℝ) := by exact_mod_cast hnat
    linarith only [hc, hq2]
  have hlogNat : (Nat.log 2 ⌈t ^ 2⌉₊ : ℝ) ≤ Real.log (⌈t ^ 2⌉₊ : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hl20, ← Real.log_rpow (by norm_num)]
    refine Real.log_le_log (by positivity) ?_
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 (show ⌈t ^ 2⌉₊ ≠ 0 by omega)
  have hlogq : Real.log (⌈t ^ 2⌉₊ : ℝ) ≤ Real.log 2 + 2 * Real.log t := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < ⌈t ^ 2⌉₊ by omega) : (0 : ℝ) < ⌈t ^ 2⌉₊) hq2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlogq' : Real.log (⌈t ^ 2⌉₊ : ℝ) / Real.log 2 ≤ 1 + 3 * Real.log t := by
    rw [div_le_iff₀ hl20]
    have hc : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith only [hl2]
    have hm := mul_le_mul_of_nonneg_right hc (by linarith only [hlogt] : 0 ≤ Real.log t)
    nlinarith only [hlogq, hm]
  refine ⟨hlower, hupper, ?_⟩
  unfold zetaDyadicTruncationExponent
  push_cast
  linarith only [hlogNat, hlogq', hlogt]

/-- The preceding integer cutoff still lies above `t²`. -/
theorem square_le_zetaDyadicTruncation_pred (t : ℝ) :
    t ^ 2 ≤ ((2 ^ zetaDyadicTruncationExponent t - 1 : ℕ) : ℝ) := by
  have hnat : ⌈t ^ 2⌉₊ < 2 ^ zetaDyadicTruncationExponent t := by
    unfold zetaDyadicTruncationExponent
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : ⌈t ^ 2⌉₊ ≤ 2 ^ zetaDyadicTruncationExponent t - 1 := by omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast hle)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.zetaDyadicTruncation_bounds
