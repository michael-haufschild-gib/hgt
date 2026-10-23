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
def zetaLowerA : ℝ := 1 / (2 * 448 ^ (4 : ℕ) * 756)

theorem zetaLowerA_pos : 0 < zetaLowerA := by
  rw [zetaLowerA]
  norm_num

theorem zetaLowerA_le_one : zetaLowerA ≤ 1 := by
  rw [zetaLowerA]
  norm_num

/-- **Strip lower bound**: `A³/(12096·log²⁸|t|) ≤ ‖ζ(σ+it)‖⁴` for
`|σ − 1| ≤ A/log⁹|t|`, `|t| ≥ 9`. -/
theorem pow_four_norm_riemannZeta_ge_strip {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ)) :
    zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |t| ^ (28 : ℕ))
      ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ (4 : ℕ) := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  -- `log|t| > 2`
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hL90 : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hAhalf : zetaLowerA ≤ 1 / 2 := by rw [zetaLowerA]; norm_num
  have hηhalf : zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 1 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.log |t| ^ (9 : ℕ) := by
      have h2 : (1 : ℝ) ≤ Real.log |t| := by linarith
      calc (1 : ℝ) = 1 ^ (9 : ℕ) := by norm_num
        _ ≤ Real.log |t| ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 9
    calc zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ zetaLowerA / 1 := by
          apply div_le_div_of_nonneg_left zetaLowerA_pos.le
            (by norm_num) h1
      _ ≤ 1 / 2 := by rw [div_one]; exact hAhalf
  have hη0 : (0 : ℝ) < zetaLowerA / Real.log |t| ^ (9 : ℕ) :=
    div_pos zetaLowerA_pos hL90
  have hη1 : zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ Real.log |t| ^ (9 : ℕ) := by
      have h2 : (1 : ℝ) ≤ Real.log |t| := by linarith
      calc (1 : ℝ) = 1 ^ (9 : ℕ) := by norm_num
        _ ≤ Real.log |t| ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) h2 9
    calc zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ zetaLowerA / 1 := by
          apply div_le_div_of_nonneg_left zetaLowerA_pos.le
            (by norm_num) h1
      _ ≤ 1 := by rw [div_one]; exact zetaLowerA_le_one
  -- the quartic bound at the right edge `σ₁ = 1 + η`
  have hZ := pow_four_norm_riemannZeta_ge ht hη0 hη1
  -- the key drift comparison `(2D)⁴ ≤ Z` where `D` bounds the segment
  have hkey : (2 * (112 * Real.log |t| ^ (2 : ℕ)
      * (2 * (zetaLowerA / Real.log |t| ^ (9 : ℕ))))) ^ (4 : ℕ)
      ≤ (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
        / (756 * Real.log |t|) := by
    have hA448 : 448 ^ (4 : ℕ) * 756 * zetaLowerA = 1 / 2 := by
      rw [zetaLowerA]
      norm_num
    have hexp : (2 * (112 * Real.log |t| ^ (2 : ℕ)
        * (2 * (zetaLowerA / Real.log |t| ^ (9 : ℕ))))) ^ (4 : ℕ)
        = 448 ^ (4 : ℕ) * zetaLowerA ^ (4 : ℕ) * Real.log |t| ^ (8 : ℕ)
          / Real.log |t| ^ (36 : ℕ) := by
      field_simp
      ring
    have hexp2' : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
        / (756 * Real.log |t|)
        = zetaLowerA ^ (3 : ℕ) / (756 * Real.log |t| ^ (28 : ℕ)) := by
      field_simp
    rw [hexp, hexp2']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hL8 : Real.log |t| ^ (36 : ℕ) = Real.log |t| ^ (8 : ℕ) * Real.log |t| ^ (28 : ℕ) := by
      ring
    -- reduces to `448⁴·756·A ≤ 1` against matching log powers
    have hred : 448 ^ (4 : ℕ) * zetaLowerA ^ (4 : ℕ) * 756 ≤ zetaLowerA ^ (3 : ℕ) := by
      have h1 : zetaLowerA ^ (4 : ℕ) = zetaLowerA ^ (3 : ℕ) * zetaLowerA := by ring
      rw [h1]
      have h2 : 448 ^ (4 : ℕ) * (zetaLowerA ^ (3 : ℕ) * zetaLowerA) * 756
          = (448 ^ (4 : ℕ) * 756 * zetaLowerA) * zetaLowerA ^ (3 : ℕ) := by ring
      rw [h2, hA448]
      have h3 : (0 : ℝ) ≤ zetaLowerA ^ (3 : ℕ) := by positivity
      linarith
    calc 448 ^ (4 : ℕ) * zetaLowerA ^ (4 : ℕ) * Real.log |t| ^ (8 : ℕ)
          * (756 * Real.log |t| ^ (28 : ℕ))
        = (448 ^ (4 : ℕ) * zetaLowerA ^ (4 : ℕ) * 756)
          * (Real.log |t| ^ (8 : ℕ) * Real.log |t| ^ (28 : ℕ)) := by ring
      _ ≤ zetaLowerA ^ (3 : ℕ) * (Real.log |t| ^ (8 : ℕ) * Real.log |t| ^ (28 : ℕ)) := by
          apply mul_le_mul_of_nonneg_right hred (by positivity)
      _ = zetaLowerA ^ (3 : ℕ) * Real.log |t| ^ (36 : ℕ) := by ring
  -- rewrite the target through `Z/16`
  have hZ16 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
      / (756 * Real.log |t|) / 16
      = zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |t| ^ (28 : ℕ)) := by
    field_simp
    ring
  rcases eq_or_lt_of_le hσu with heq | hlt
  · -- at the right edge the quartic bound applies directly
    rw [heq]
    refine le_trans ?_ hZ
    rw [← hZ16]
    have hZ0 : (0 : ℝ) ≤ (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
        / (756 * Real.log |t|) := by positivity
    linarith
  · -- interior: drift from the right edge
    have hseg := norm_riemannZeta_sub_le_segment ht
      (show 1 - 1 / (4 * Real.log |t|) ≤ σ by
        have h1 : zetaLowerA / Real.log |t| ^ (9 : ℕ)
            ≤ 1 / (4 * Real.log |t|) := by
          rw [div_le_div_iff₀ hL90 (by positivity)]
          have h2 : (1 : ℝ) ≤ Real.log |t| ^ (8 : ℕ) := by
            have h3 : (1 : ℝ) ≤ Real.log |t| := by linarith
            calc (1 : ℝ) = 1 ^ (8 : ℕ) := by norm_num
              _ ≤ Real.log |t| ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) h3 8
          have h4 : zetaLowerA * (4 * Real.log |t|) ≤ 4 * Real.log |t| := by
            exact mul_le_of_le_one_left (by linarith) zetaLowerA_le_one
          have h5 : (4 : ℝ) ≤ Real.log |t| ^ (8 : ℕ) := by
            have h6 : (2 : ℝ) ^ (8 : ℕ) ≤ Real.log |t| ^ (8 : ℕ) :=
              pow_le_pow_left₀ (by norm_num) hlogt2.le 8
            linarith
          have h7 : 4 * Real.log |t| ≤ Real.log |t| ^ (8 : ℕ) * Real.log |t| :=
            mul_le_mul_of_nonneg_right h5 hL0.le
          linarith
        linarith)
      hlt
      (show 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 3 / 2 by linarith)
    -- triangle: the value at `σ` keeps half the edge value
    set W : ℝ := ‖riemannZeta
      (((1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) : ℝ) : ℂ)
        + (t : ℂ) * Complex.I)‖ with hW
    have hWZ : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
        / (756 * Real.log |t|) ≤ W ^ (4 : ℕ) := hZ
    have hD : ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) : ℝ) : ℂ)
        + (t : ℂ) * Complex.I) - riemannZeta (↑σ + ↑t * Complex.I)‖
        ≤ 112 * Real.log |t| ^ (2 : ℕ)
          * (2 * (zetaLowerA / Real.log |t| ^ (9 : ℕ))) := by
      refine le_trans hseg ?_
      have h1 : 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) - σ
          ≤ 2 * (zetaLowerA / Real.log |t| ^ (9 : ℕ)) := by linarith
      linarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (Real.log |t|))]
    -- `2D ≤ W` from `(2D)⁴ ≤ Z ≤ W⁴`
    have h2D : 2 * (112 * Real.log |t| ^ (2 : ℕ)
        * (2 * (zetaLowerA / Real.log |t| ^ (9 : ℕ)))) ≤ W := by
      apply le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0)
        (by rw [hW]; exact norm_nonneg _)
      exact le_trans hkey hWZ
    have hhalf : W / 2 ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ := by
      have h1 : W ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖
          + ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) : ℝ) : ℂ)
              + (t : ℂ) * Complex.I)
            - riemannZeta (↑σ + ↑t * Complex.I)‖ := by
        rw [hW]
        calc ‖riemannZeta (((1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) : ℝ) : ℂ)
              + (t : ℂ) * Complex.I)‖
            = ‖riemannZeta (↑σ + ↑t * Complex.I)
              + (riemannZeta (((1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) : ℝ) : ℂ)
                  + (t : ℂ) * Complex.I)
                - riemannZeta (↑σ + ↑t * Complex.I))‖ := by
              congr 1
              ring
          _ ≤ _ := norm_add_le _ _
      linarith [hD, h2D]
    have hfinal : (W / 2) ^ (4 : ℕ)
        ≤ ‖riemannZeta (↑σ + ↑t * Complex.I)‖ ^ (4 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hhalf 4
    have hW4 : (W / 2) ^ (4 : ℕ) = W ^ (4 : ℕ) / 16 := by ring
    rw [hW4] at hfinal
    rw [← hZ16]
    have h16 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
        / (756 * Real.log |t|) / 16 ≤ W ^ (4 : ℕ) / 16 := by
      linarith [hWZ]
    linarith

end RHTower
