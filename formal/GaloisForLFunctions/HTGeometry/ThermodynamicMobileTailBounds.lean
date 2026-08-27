import GaloisForLFunctions.HTGeometry.StaticLocalNestedThermodynamicRampReturnLaw

/-!
# Uniform mobile-tail bounds

At laboratory shell index `K`, cut the compatible nested chain after pair `2K`.  The deleted
inverse-fourth boundary bond and a perturbation tail bounded by twelve copies of a
`10⁻⁶ n⁻²` sequence each contribute less than half the target error throughout the complete
shell.  These are the quantitative estimates needed to retain the inverse-square phase block on
pairs `4K+1,...,8K` while allowing an arbitrary noncommuting prefix.
-/

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- The inverse-fourth base bond crossing the cut after pair `2K` costs less than half the error. -/
theorem mobileCut_baseDuhamel_lt_half {K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε)
    (ht : t < 256 * Real.pi * ε * (K + 1)) :
    t * (1 / (((2 * K + 1 : ℕ) : ℝ) ^ 4)) < ε / 2 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have hk3 : (8 : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 := by gcongr
  have hk4 : 512 * (K : ℝ) ≤ (K : ℝ) ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left hk3 (le_of_lt hk0)
    norm_num [pow_succ] at hm ⊢
    nlinarith
  have hpoly : 2048 * ((K : ℝ) + 1) < (2 * (K : ℝ) + 1) ^ 4 := by
    have hrough : 2048 * ((K : ℝ) + 1) < 16 * (K : ℝ) ^ 4 := by
      nlinarith
    have hsquare : (2 * (K : ℝ)) ^ 4 < (2 * (K : ℝ) + 1) ^ 4 := by
      gcongr
      norm_num
    norm_num [mul_pow] at hsquare
    nlinarith
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hden : (0 : ℝ) < (2 * (K : ℝ) + 1) ^ 4 := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul]
  rw [← div_eq_mul_inv, div_lt_iff₀ hden]
  nlinarith

/-- A twelve-coordinate inverse-square perturbation tail costs less than half the error. -/
theorem mobileCut_perturbDuhamel_lt_half {K : ℕ} {t ε R : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε) (ht0 : 0 ≤ t)
    (ht : t < 256 * Real.pi * ε * (K + 1))
    (hR : R ≤ 12 / (1000000 * (K : ℝ))) :
    t * R < ε / 2 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hR ht0
  have hrough : t * (12 / (1000000 * (K : ℝ))) < ε / 2 := by
    have hden : (0 : ℝ) < 1000000 * (K : ℝ) := by positivity
    rw [show t * (12 / (1000000 * (K : ℝ))) =
      (12 * t) / (1000000 * (K : ℝ)) by ring]
    rw [div_lt_iff₀ hden]
    have hk1 : (K : ℝ) + 1 ≤ 2 * K := by nlinarith
    have htScale' : 12 * t < 12 * (1024 * ε * ((K : ℝ) + 1)) := by nlinarith
    nlinarith
  exact lt_of_le_of_lt hmul hrough

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
