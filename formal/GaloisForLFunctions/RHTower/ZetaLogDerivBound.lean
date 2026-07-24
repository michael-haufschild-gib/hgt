import GaloisForLFunctions.RHTower.ZetaStripLowerBound

/-!
# The logarithmic derivative of ζ on the zero-free strip

`‖1/ζ(σ+it)‖ ≤ (20/A)·log⁷|t|` and hence
`‖ζ′/ζ(σ+it)‖ ≤ (2240/A)·log⁹|t|` on the strip `|σ−1| ≤ A/log⁹|t|`,
`|t| ≥ 9` — with the rational witness `20/A` whose fourth power clears
the quartic strip bound (`160000/(12096·A) ≥ 1`), so no roots appear.
This is the integrand estimate for the Perron contour of `−ζ′/ζ`.
-/

noncomputable section

namespace RHTower

open Set

/-- **Inverse bound on the strip**:
`‖1/ζ(σ+it)‖ ≤ (20/A)·log⁷|t|`. -/
theorem norm_inv_riemannZeta_le {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ 9 ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ 9) :
    ‖(riemannZeta (↑σ + ↑t * Complex.I))⁻¹‖
      ≤ 20 / zetaLowerA * Real.log |t| ^ 7 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hexp2 : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
      nlinarith [Real.exp_pos 1]
    rw [h2]
    nlinarith [h3]
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hq := pow_four_norm_riemannZeta_ge_strip ht hσl hσu
  have hq0 : (0 : ℝ) < zetaLowerA ^ 3 / (12096 * Real.log |t| ^ 28) := by
    positivity
  -- ζ does not vanish on the strip
  have hζ0 : (0 : ℝ) < ‖riemannZeta (↑σ + ↑t * Complex.I)‖ := by
    rcases eq_or_lt_of_le (norm_nonneg
      (riemannZeta (↑σ + ↑t * Complex.I))) with h | h
    · exfalso
      rw [← h] at hq
      rw [show ((0 : ℝ)) ^ 4 = 0 by norm_num] at hq
      linarith
    · exact h
  -- the rational witness beats the quartic bound
  have hkey : 1 ≤ (20 / zetaLowerA * Real.log |t| ^ 7)
      * ‖riemannZeta (↑σ + ↑t * Complex.I)‖ := by
    apply le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity)
    have hexp4 : ((20 / zetaLowerA * Real.log |t| ^ 7)
        * ‖riemannZeta (↑σ + ↑t * Complex.I)‖) ^ 4
        = (20 / zetaLowerA) ^ 4 * Real.log |t| ^ 28
          * ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 4 := by
      ring
    rw [hexp4, one_pow]
    have h1 : (20 / zetaLowerA) ^ 4 * Real.log |t| ^ 28
        * (zetaLowerA ^ 3 / (12096 * Real.log |t| ^ 28))
        ≤ (20 / zetaLowerA) ^ 4 * Real.log |t| ^ 28
          * ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 4 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    refine le_trans ?_ h1
    have h2 : (20 / zetaLowerA) ^ 4 * Real.log |t| ^ 28
        * (zetaLowerA ^ 3 / (12096 * Real.log |t| ^ 28))
        = 160000 / (12096 * zetaLowerA) := by
      field_simp
      ring
    rw [h2]
    rw [le_div_iff₀ (by positivity)]
    have h3 : 12096 * zetaLowerA ≤ 12096 := by
      nlinarith [zetaLowerA_le_one, hA0]
    linarith
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hζ0]
  nlinarith [hkey]

/-- **Logarithmic derivative bound on the strip**:
`‖ζ′/ζ(σ+it)‖ ≤ (2240/A)·log⁹|t|`. -/
theorem norm_deriv_div_riemannZeta_le {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ 9 ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ 9) :
    ‖deriv riemannZeta (↑σ + ↑t * Complex.I)
        / riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ 2240 / zetaLowerA * Real.log |t| ^ 9 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hexp2 : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
      nlinarith [Real.exp_pos 1]
    rw [h2]
    nlinarith [h3]
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hAhalf : zetaLowerA ≤ 1 / 2 := by rw [zetaLowerA]; norm_num
  have hL90 : (0 : ℝ) < Real.log |t| ^ 9 := by positivity
  -- the strip sits inside the derivative-growth region
  have hη14 : zetaLowerA / Real.log |t| ^ 9 ≤ 1 / (4 * Real.log |t|) := by
    rw [div_le_div_iff₀ hL90 (by positivity)]
    have h2 : (2 : ℝ) ^ 8 ≤ Real.log |t| ^ 8 :=
      pow_le_pow_left₀ (by norm_num) hlogt2.le 8
    have h4 : zetaLowerA * (4 * Real.log |t|) ≤ 4 * Real.log |t| := by
      nlinarith [zetaLowerA_le_one, hA0, hL0]
    have h5 : (4 : ℝ) ≤ Real.log |t| ^ 8 := by nlinarith
    have h7 : 4 * Real.log |t| ≤ Real.log |t| ^ 8 * Real.log |t| :=
      mul_le_mul_of_nonneg_right h5 hL0.le
    nlinarith [hL0]
  have hηhalf : zetaLowerA / Real.log |t| ^ 9 ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.log |t| ^ 9 := by
      have h2 : (1 : ℝ) ≤ Real.log |t| := by linarith
      calc (1 : ℝ) = 1 ^ 9 := by norm_num
        _ ≤ Real.log |t| ^ 9 := pow_le_pow_left₀ (by norm_num) h2 9
    calc zetaLowerA / Real.log |t| ^ 9 ≤ zetaLowerA / 1 := by
          apply div_le_div_of_nonneg_left hA0.le (by norm_num) h1
      _ ≤ 1 / 2 := by rw [div_one]; exact hAhalf
  rw [div_eq_mul_inv, norm_mul]
  have hd := abs_deriv_riemannZeta_le_sq_log ht
    (by linarith : 1 - 1 / (4 * Real.log |t|) ≤ σ)
    (by linarith : σ ≤ 3 / 2)
  have hi := norm_inv_riemannZeta_le ht hσl hσu
  calc ‖deriv riemannZeta (↑σ + ↑t * Complex.I)‖
        * ‖(riemannZeta (↑σ + ↑t * Complex.I))⁻¹‖
      ≤ (112 * Real.log |t| ^ 2)
        * (20 / zetaLowerA * Real.log |t| ^ 7) := by
        apply mul_le_mul hd hi (norm_nonneg _) (by positivity)
    _ = 2240 / zetaLowerA * Real.log |t| ^ 9 := by
        ring

end RHTower
