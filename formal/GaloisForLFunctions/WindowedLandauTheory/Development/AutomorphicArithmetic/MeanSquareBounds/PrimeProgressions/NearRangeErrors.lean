import Mathlib

/-! The differenced ramp error at height `U⁸` and difference fraction `U⁻⁴`. -/

noncomputable section

namespace QH.PrimeProgressions

theorem near_range_ramp_error {M y U C D E t L : ℝ}
    (hM : 0 ≤ M) (hMU : M ≤ U) (hU : 1 ≤ U) (hy : U ^ 4 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : E ≤ C * (1 + D) * (U ^ 7)⁻¹) (hL : L ≤ D * U) (ht : t ≤ (U ^ 8)⁻¹) :
    M * (4 * y * E / (U ^ 4)⁻¹ + 4 * ((U ^ 4)⁻¹ * y + 1) * L) +
      (20 * (U ^ 4)⁻¹ * y + 2 * y * t) ≤
        (4 * C * (1 + D) + 8 * D + 22) * y * (U ^ 2)⁻¹ := by
  have hU₀ : 0 < U := zero_lt_one.trans_le hU
  have hy₀ : 0 ≤ y := (by positivity : 0 ≤ U ^ 4).trans hy
  have hδ : 0 < (U ^ 4)⁻¹ := by positivity
  have h1 : M * (4 * y * E / (U ^ 4)⁻¹) ≤ 4 * C * (1 + D) * y * (U ^ 2)⁻¹ := by
    calc M * (4 * y * E / (U ^ 4)⁻¹)
        ≤ U * (4 * y * (C * (1 + D) * (U ^ 7)⁻¹) / (U ^ 4)⁻¹) := by
          have hscale := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hE (show 0 ≤ 4 * y by positivity)) hδ.le
          exact (mul_le_mul_of_nonneg_left hscale hM).trans
            (mul_le_mul_of_nonneg_right hMU (by positivity))
      _ = _ := by field_simp [hU₀.ne'] <;> ring
  have hδy : 1 ≤ (U ^ 4)⁻¹ * y := by
    rw [inv_mul_eq_div, one_le_div (by positivity)]
    exact hy
  have h2 : M * (4 * ((U ^ 4)⁻¹ * y + 1) * L) ≤ 8 * D * y * (U ^ 2)⁻¹ := by
    calc M * (4 * ((U ^ 4)⁻¹ * y + 1) * L) ≤ U * (4 * (2 * ((U ^ 4)⁻¹ * y)) * (D * U)) := by
          have hcoeff : 4 * ((U ^ 4)⁻¹ * y + 1) ≤ 4 * (2 * ((U ^ 4)⁻¹ * y)) := by
            linarith only [hδy]
          have hscale := (mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * ((U ^ 4)⁻¹ * y + 1) by positivity)).trans
            (mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ D * U))
          exact (mul_le_mul_of_nonneg_left hscale hM).trans
            (mul_le_mul_of_nonneg_right hMU (by positivity))
      _ = _ := by field_simp [hU₀.ne'] <;> ring
  have ha : (U ^ 4)⁻¹ ≤ (U ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hU (by norm_num))
  have hb : (U ^ 8)⁻¹ ≤ (U ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hU (by norm_num))
  have h3 : 20 * (U ^ 4)⁻¹ * y + 2 * y * t ≤ 22 * y * (U ^ 2)⁻¹ := by
    nlinarith only [mul_le_mul_of_nonneg_right ha hy₀, mul_le_mul_of_nonneg_left (ht.trans hb) hy₀]
  rw [mul_add]
  linarith only [h1, h2, h3]

theorem near_range_zero_error {M U C D L X W : ℝ}
    (hM : 0 ≤ M) (hMU : M ≤ U) (hU : 1 ≤ U) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : L ≤ D * U) (hX : X ≤ (U ^ 16)⁻¹) (hX₀ : 0 ≤ X)
    (hW : W ≤ M * (2 * C * (U ^ 8 + 2) * L) * X) : W ≤ 6 * C * D * (U ^ 2)⁻¹ := by
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hpow : 1 ≤ U ^ (8 : ℕ) := one_le_pow₀ hU
  have hT : U ^ 8 + 2 ≤ 3 * U ^ (8 : ℕ) := by linarith only [hpow]
  calc W ≤ U * (2 * C * (3 * U ^ 8) * (D * U)) * (U ^ 16)⁻¹ := by
        refine hW.trans (mul_le_mul ?_ hX hX₀ (by positivity))
        have hcoeff := mul_le_mul_of_nonneg_left hT (show 0 ≤ 2 * C by positivity)
        have hscale := (mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * C * (U ^ 8 + 2) by positivity)).trans
          (mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ D * U))
        exact (mul_le_mul_of_nonneg_left hscale hM).trans
          (mul_le_mul_of_nonneg_right hMU (by positivity))
    _ = 6 * C * D * (U ^ 6)⁻¹ := by field_simp [hUp.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ hU (by norm_num)))
      (by positivity)

end QH.PrimeProgressions
