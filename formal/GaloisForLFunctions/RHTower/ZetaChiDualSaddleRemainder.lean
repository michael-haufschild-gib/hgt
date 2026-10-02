import GaloisForLFunctions.RHTower.ZetaChiDualCoefficientBound

open Complex
noncomputable section
namespace RHTower

/-- An explicit polynomial choice of height and margin makes the complete
normalized stationary remainder small. No exterior interval is discarded. -/
theorem zetaChi_dual_stationary_remainder_le {m a C : ℝ}
    (hm : 1 ≤ m) (hl : m ^ 10 ≤ a) (hu : a ≤ 2 * m ^ 10) (hC : 0 ≤ C) :
    ((2 * Real.pi) / Real.sqrt (m ^ 10)) *
      (C * (78 + 2 * (m ^ 6) ^ 2 / m ^ 10 +
        40 * a ^ 2 / (m ^ 10 * m ^ 6) + 4 * (m ^ 6) ^ 4 / a ^ 2 +
          40 * a / m ^ 6)) ≤ 648 * Real.pi * C / m := by
  have hm0 : 0 < m := by linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hl
  have hpow2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
  have hpow4 : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have h24 : m ^ 2 ≤ m ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpow2) (sq_nonneg m)]
  have hlo : m ^ 20 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ a + m ^ 10 by positivity)]
  have hup : a ^ 2 ≤ 4 * m ^ 20 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ 2 * m ^ 10 + a by positivity)]
  have h2 : 2 * (m ^ 6) ^ 2 / m ^ 10 ≤ 2 * m ^ 4 := by
    calc
      _ = 2 * m ^ 2 := by field_simp
      _ ≤ _ := by linarith
  have h3 : 40 * a ^ 2 / (m ^ 10 * m ^ 6) ≤ 160 * m ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < m ^ 10 * m ^ 6)).mpr
    nlinarith
  have h4 : 4 * (m ^ 6) ^ 4 / a ^ 2 ≤ 4 * m ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < a ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 4 * m ^ 4)]
  have h5 : 40 * a / m ^ 6 ≤ 80 * m ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < m ^ 6)).mpr
    nlinarith
  have hsum : 78 + 2 * (m ^ 6) ^ 2 / m ^ 10 +
      40 * a ^ 2 / (m ^ 10 * m ^ 6) + 4 * (m ^ 6) ^ 4 / a ^ 2 +
        40 * a / m ^ 6 ≤ 324 * m ^ 4 := by linarith
  have hsqrt : Real.sqrt (m ^ 10) = m ^ 5 := by
    rw [show m ^ 10 = (m ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  calc
    _ ≤ ((2 * Real.pi) / Real.sqrt (m ^ 10)) * (C * (324 * m ^ 4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hC) (by positivity)
    _ = _ := by rw [hsqrt]; field_simp; ring

end RHTower
