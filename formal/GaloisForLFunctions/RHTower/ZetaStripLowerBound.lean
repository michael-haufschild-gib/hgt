import GaloisForLFunctions.RHTower.ZetaLowerBound

/-!
# The ζ lower bound on the zero-free strip

`A³/(12096·log²⁸|t|) ≤ ‖ζ(σ+it)‖⁴` on the strip
`|σ − 1| ≤ A/log⁹|t|`, `A = 1/(2·448⁴·756)`: the quartic lower bound at
`1 + A/log⁹|t|` survives the leftward segment drift because the drift's
fourth power `(448·η·log²)⁴` sits below the quartic bound `η³/(756·log)`
by the choice of `A` — entirely root-free through
`le_of_pow_le_pow_left`.  This is the `1/ζ` input of the `ζ′/ζ` bounds
on the Perron contour.
-/

noncomputable section

namespace RHTower

open Set

/-- The strip half-width constant `1/(2·448⁴·756)`. -/
def zetaLowerA : ℝ := 1 / (2 * 448 ^ 4 * 756)

theorem zetaLowerA_pos : 0 < zetaLowerA := by
  rw [zetaLowerA]
  norm_num

theorem zetaLowerA_le_one : zetaLowerA ≤ 1 := by
  rw [zetaLowerA]
  norm_num

set_option maxHeartbeats 3200000 in
/-- **Strip lower bound**: `A³/(12096·log²⁸|t|) ≤ ‖ζ(σ+it)‖⁴` for
`|σ − 1| ≤ A/log⁹|t|`, `|t| ≥ 9`. -/
theorem pow_four_norm_riemannZeta_ge_strip {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ 9 ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ 9) :
    zetaLowerA ^ 3 / (12096 * Real.log |t| ^ 28)
      ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 4 := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  -- `log|t| > 2`
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
  have hL90 : (0 : ℝ) < Real.log |t| ^ 9 := by positivity
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hAhalf : zetaLowerA ≤ 1 / 2 := by rw [zetaLowerA]; norm_num
  have hηhalf : zetaLowerA / Real.log |t| ^ 9 ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.log |t| ^ 9 := by
      have h2 : (1 : ℝ) ≤ Real.log |t| := by linarith
      calc (1 : ℝ) = 1 ^ 9 := by norm_num
        _ ≤ Real.log |t| ^ 9 := pow_le_pow_left₀ (by norm_num) h2 9
    calc zetaLowerA / Real.log |t| ^ 9 ≤ zetaLowerA / 1 := by
          apply div_le_div_of_nonneg_left zetaLowerA_pos.le
            (by norm_num) h1
      _ ≤ 1 / 2 := by rw [div_one]; exact hAhalf
  have hη0 : (0 : ℝ) < zetaLowerA / Real.log |t| ^ 9 :=
    div_pos zetaLowerA_pos hL90
  have hη1 : zetaLowerA / Real.log |t| ^ 9 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ Real.log |t| ^ 9 := by
      have h2 : (1 : ℝ) ≤ Real.log |t| := by linarith
      calc (1 : ℝ) = 1 ^ 9 := by norm_num
        _ ≤ Real.log |t| ^ 9 := pow_le_pow_left₀ (by norm_num) h2 9
    calc zetaLowerA / Real.log |t| ^ 9 ≤ zetaLowerA / 1 := by
          apply div_le_div_of_nonneg_left zetaLowerA_pos.le
            (by norm_num) h1
      _ ≤ 1 := by rw [div_one]; exact zetaLowerA_le_one
  -- the quartic bound at the right edge `σ₁ = 1 + η`
  have hZ := pow_four_norm_riemannZeta_ge ht hη0 hη1
  -- the key drift comparison `(2D)⁴ ≤ Z` where `D` bounds the segment
  have hkey : (2 * (112 * Real.log |t| ^ 2
      * (2 * (zetaLowerA / Real.log |t| ^ 9)))) ^ 4
      ≤ (zetaLowerA / Real.log |t| ^ 9) ^ 3
        / (756 * Real.log |t|) := by
    have hA448 : 448 ^ 4 * 756 * zetaLowerA = 1 / 2 := by
      rw [zetaLowerA]
      norm_num
    have hexp : (2 * (112 * Real.log |t| ^ 2
        * (2 * (zetaLowerA / Real.log |t| ^ 9)))) ^ 4
        = 448 ^ 4 * zetaLowerA ^ 4 * Real.log |t| ^ 8
          / Real.log |t| ^ 36 := by
      field_simp
      ring
    have hexp2' : (zetaLowerA / Real.log |t| ^ 9) ^ 3
        / (756 * Real.log |t|)
        = zetaLowerA ^ 3 / (756 * Real.log |t| ^ 28) := by
      field_simp
    rw [hexp, hexp2']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hL8 : Real.log |t| ^ 36 = Real.log |t| ^ 8 * Real.log |t| ^ 28 := by
      ring
    -- reduces to `448⁴·756·A ≤ 1` against matching log powers
    have hred : 448 ^ 4 * zetaLowerA ^ 4 * 756 ≤ zetaLowerA ^ 3 := by
      have h1 : zetaLowerA ^ 4 = zetaLowerA ^ 3 * zetaLowerA := by ring
      rw [h1]
      have h2 : 448 ^ 4 * (zetaLowerA ^ 3 * zetaLowerA) * 756
          = (448 ^ 4 * 756 * zetaLowerA) * zetaLowerA ^ 3 := by ring
      rw [h2, hA448]
      have h3 : (0 : ℝ) ≤ zetaLowerA ^ 3 := by positivity
      linarith
    calc 448 ^ 4 * zetaLowerA ^ 4 * Real.log |t| ^ 8
          * (756 * Real.log |t| ^ 28)
        = (448 ^ 4 * zetaLowerA ^ 4 * 756)
          * (Real.log |t| ^ 8 * Real.log |t| ^ 28) := by ring
      _ ≤ zetaLowerA ^ 3 * (Real.log |t| ^ 8 * Real.log |t| ^ 28) := by
          apply mul_le_mul_of_nonneg_right hred (by positivity)
      _ = zetaLowerA ^ 3 * Real.log |t| ^ 36 := by ring
  -- rewrite the target through `Z/16`
  have hZ16 : (zetaLowerA / Real.log |t| ^ 9) ^ 3
      / (756 * Real.log |t|) / 16
      = zetaLowerA ^ 3 / (12096 * Real.log |t| ^ 28) := by
    field_simp
    ring
  rcases eq_or_lt_of_le hσu with heq | hlt
  · -- at the right edge the quartic bound applies directly
    rw [heq]
    refine le_trans ?_ hZ
    rw [← hZ16]
    have hZ0 : (0 : ℝ) ≤ (zetaLowerA / Real.log |t| ^ 9) ^ 3
        / (756 * Real.log |t|) := by positivity
    linarith
  · -- interior: drift from the right edge
    have hseg := norm_riemannZeta_sub_le_segment ht
      (show 1 - 1 / (4 * Real.log |t|) ≤ σ by
        have h1 : zetaLowerA / Real.log |t| ^ 9
            ≤ 1 / (4 * Real.log |t|) := by
          rw [div_le_div_iff₀ hL90 (by positivity)]
          have h2 : (1 : ℝ) ≤ Real.log |t| ^ 8 := by
            have h3 : (1 : ℝ) ≤ Real.log |t| := by linarith
            calc (1 : ℝ) = 1 ^ 8 := by norm_num
              _ ≤ Real.log |t| ^ 8 := pow_le_pow_left₀ (by norm_num) h3 8
          have h4 : zetaLowerA * (4 * Real.log |t|) ≤ 4 * Real.log |t| := by
            nlinarith [zetaLowerA_le_one, zetaLowerA_pos, hL0]
          have h5 : (4 : ℝ) ≤ Real.log |t| ^ 8 := by
            have h6 : (2 : ℝ) ^ 8 ≤ Real.log |t| ^ 8 :=
              pow_le_pow_left₀ (by norm_num) hlogt2.le 8
            nlinarith
          have h7 : 4 * Real.log |t| ≤ Real.log |t| ^ 8 * Real.log |t| :=
            mul_le_mul_of_nonneg_right h5 hL0.le
          nlinarith [hL0]
        linarith)
      hlt
      (show 1 + zetaLowerA / Real.log |t| ^ 9 ≤ 3 / 2 by linarith)
    -- triangle: the value at `σ` keeps half the edge value
    set W : ℝ := ‖riemannZeta
      (((1 + zetaLowerA / Real.log |t| ^ 9 : ℝ) : ℂ)
        + (t : ℂ) * Complex.I)‖ with hW
    have hWZ : (zetaLowerA / Real.log |t| ^ 9) ^ 3
        / (756 * Real.log |t|) ≤ W ^ 4 := hZ
    have hD : ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ 9 : ℝ) : ℂ)
        + (t : ℂ) * Complex.I) - riemannZeta (↑σ + ↑t * Complex.I)‖
        ≤ 112 * Real.log |t| ^ 2
          * (2 * (zetaLowerA / Real.log |t| ^ 9)) := by
      refine le_trans hseg ?_
      have h1 : 1 + zetaLowerA / Real.log |t| ^ 9 - σ
          ≤ 2 * (zetaLowerA / Real.log |t| ^ 9) := by linarith
      nlinarith [sq_nonneg (Real.log |t|), hη0]
    -- `2D ≤ W` from `(2D)⁴ ≤ Z ≤ W⁴`
    have h2D : 2 * (112 * Real.log |t| ^ 2
        * (2 * (zetaLowerA / Real.log |t| ^ 9))) ≤ W := by
      apply le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0)
        (by rw [hW]; exact norm_nonneg _)
      exact le_trans hkey hWZ
    have hhalf : W / 2 ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ := by
      have h1 : W ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖
          + ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ 9 : ℝ) : ℂ)
              + (t : ℂ) * Complex.I)
            - riemannZeta (↑σ + ↑t * Complex.I)‖ := by
        rw [hW]
        calc ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ 9 : ℝ) : ℂ)
              + (t : ℂ) * Complex.I)‖
            = ‖riemannZeta (↑σ + ↑t * Complex.I)
              + (riemannZeta (((1 + zetaLowerA / Real.log |t| ^ 9 : ℝ) : ℂ)
                  + (t : ℂ) * Complex.I)
                - riemannZeta (↑σ + ↑t * Complex.I))‖ := by
              congr 1
              ring
          _ ≤ _ := norm_add_le _ _
      linarith [hD, h2D]
    have hfinal : (W / 2) ^ 4
        ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ 4 :=
      pow_le_pow_left₀ (by positivity) hhalf 4
    have hW4 : (W / 2) ^ 4 = W ^ 4 / 16 := by ring
    rw [hW4] at hfinal
    rw [← hZ16]
    have h16 : (zetaLowerA / Real.log |t| ^ 9) ^ 3
        / (756 * Real.log |t|) / 16 ≤ W ^ 4 / 16 := by
      linarith [hWZ]
    linarith

end RHTower
