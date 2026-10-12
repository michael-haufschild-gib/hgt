import GaloisForLFunctions.RHTower.XiLineNearOneWindow
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.ZetaChiLeftHalfPlaneGrowth

/-!
# The strip comparison for `ξ` along a horizontal line, by convexity

Put `F(w) = ξ(½ + w + iX)` (`xiLine X w`). The corpus strip comparison
(`norm_xiLine_le_strip`) bounds `‖F(w)‖` on `0 ≤ w ≤ 9/2` by `200(6 + X)‖F(9/2)‖`. This module
gives the sharp form.

**Theorem** (`exists_norm_xiLine_le_strip_convexity`). For `0 < η ≤ ½` there is `K > 0` such that
for `X ≥ 16`, `0 ≤ w ≤ ½ + η` and `1 ≤ u ≤ X`:

`‖F(w)‖ ≤ K · X^{(½+η−w)/2} · (X/2π)^{(w−u)/2} · ‖F(u)‖`.

**Proof.** Write `ξ(s) = ½s(s−1) π^{−s/2} Γ(s/2) ζ(s)`.
* The polynomial factors at `s_w`, `s_u` have ratio at most `2` (both moduli are `≍ X²`).
* `π^{−s/2}` contributes `π^{(u−w)/2}`.
* The vertical Gamma ratio (`norm_Gamma_vertical_le_rpow_mul`) gives `(X/2)^{(w−u)/2}e^{6(u−w)/X}`.
* Convexity (`exists_norm_riemannZeta_le_convexity`) gives `‖ζ(s_w)‖ ≤ C X^{(½+η−w)/2}`.
* `‖ζ(s_u)‖ ≥ c` on `Re s ≥ 3/2` (`exists_norm_riemannZeta_ge_three_halves`).

The factor `X^{(½+η−w)/2}` is the subconvexity exponent at work; with Lindelöf it would be
`X^{ε}`.
-/

open Complex Set

namespace RHTower.DeBruijn

noncomputable section

/-- The modulus of `ξ` on a horizontal line, factor by factor. -/
theorem norm_xiLine_eq_factors {X w : ℝ} (hX : 0 < X) (hw : 0 ≤ w) :
    ‖xiLine X w‖ =
      ‖(((w + 1 / 2 : ℝ) : ℂ) + X * I) * (((w + 1 / 2 : ℝ) : ℂ) + X * I - 1) / 2‖ *
        Real.pi ^ (-((w + 1 / 2) / 2)) *
        ‖Complex.Gamma ((((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ *
        ‖riemannZeta (((w + 1 / 2 : ℝ) : ℂ) + X * I)‖ := by
  set s : ℂ := ((w + 1 / 2 : ℝ) : ℂ) + X * I with hs
  have hsre : s.re = w + 1 / 2 := by simp [hs]
  have hsim : s.im = X := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hs1 : s ≠ 1 := fun h => by have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hG : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; linarith)
  have hxi : xiLine X w = s * (s - 1) / 2 * (s.Gammaℝ * riemannZeta s) := by
    unfold xiLine
    rw [xiLine_point, ← hs, xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
    field_simp
  have hhalf : s / 2 = (((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I := by
    rw [hs]; push_cast; ring
  rw [hxi, norm_mul, norm_mul, Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hhalf]
  have hre : (-s / 2).re = -((w + 1 / 2) / 2) := by simp [hsre]; ring
  rw [hre]
  ring

/-- **The strip comparison by convexity.** -/
theorem exists_norm_xiLine_le_strip_convexity {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖ := by
  obtain ⟨C, hC, hconv⟩ := exists_norm_riemannZeta_le_convexity hη hη2
  obtain ⟨c, hc, hlow⟩ := exists_norm_riemannZeta_ge_three_halves
  refine ⟨2 * Real.exp 6 * C / c, by positivity, fun X w u hX hw0 hwη hu1 huX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hu0 : 0 ≤ u := by linarith
  rw [norm_xiLine_eq_factors hX0 hw0, norm_xiLine_eq_factors hX0 hu0]
  set sw : ℂ := ((w + 1 / 2 : ℝ) : ℂ) + X * I with hsw
  set su : ℂ := ((u + 1 / 2 : ℝ) : ℂ) + X * I with hsu
  set Pw := ‖sw * (sw - 1) / 2‖ with hPw
  set Pu := ‖su * (su - 1) / 2‖ with hPu
  set Gw := ‖Complex.Gamma ((((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGw
  set Gu := ‖Complex.Gamma ((((u + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGu
  set Zw := ‖riemannZeta sw‖ with hZw
  set Zu := ‖riemannZeta su‖ with hZu
  -- the polynomial factors
  have hsuim : X ≤ ‖su‖ := by
    have := Complex.abs_im_le_norm su; simpa [hsu, abs_of_pos hX0] using this
  have hsu1im : X ≤ ‖su - 1‖ := by
    have := Complex.abs_im_le_norm (su - 1); simpa [hsu, abs_of_pos hX0] using this
  have hsw_le : ‖sw‖ ≤ X + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0, Complex.norm_I, mul_one]
    linarith
  have hsw1_le : ‖sw - 1‖ ≤ X + 1 := by
    have e : sw - 1 = (((w - 1 / 2 : ℝ)) : ℂ) + X * I := by rw [hsw]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX0, Complex.norm_I, mul_one]
    have : |w - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hPwu : Pw ≤ 2 * Pu := by
    rw [hPw, hPu, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖sw‖ * ‖sw - 1‖ ≤ (X + 2) * (X + 1) :=
      mul_le_mul hsw_le hsw1_le (norm_nonneg _) (by linarith)
    have h2 : X * X ≤ ‖su‖ * ‖su - 1‖ := mul_le_mul hsuim hsu1im hX0.le (norm_nonneg _)
    have h3 : (X + 2) * (X + 1) ≤ 2 * (X * X) := by nlinarith
    linarith
  -- the Gamma ratio
  have hGamma : Gw ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by
    have h := norm_Gamma_vertical_le_rpow_mul (a := (w + 1 / 2) / 2) (b := (u + 1 / 2) / 2)
      (y := X / 2) (by linarith) (by linarith) (by linarith)
    have hab : (w + 1 / 2) / 2 - (u + 1 / 2) / 2 = (w - u) / 2 := by ring
    rw [hab] at h
    have hexp : Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) ≤ Real.exp 6 := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc Gw ≤ (X / 2) ^ ((w - u) / 2) *
          Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) * Gu := h
      _ ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by gcongr
  -- the two `ζ` values
  have hZw_le : Zw ≤ C * X ^ ((1 / 2 + η - w) / 2) := by
    have h := hconv (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
    have e : (1 + η - (w + 1 / 2)) / 2 = (1 / 2 + η - w) / 2 := by ring
    rw [e] at h
    simpa [hZw, hsw] using h
  have hZu_ge : c ≤ Zu := hlow su (by simp [hsu]; linarith)
  -- the powers of `π`
  have hpi : Real.pi ^ (-((w + 1 / 2) / 2)) =
      Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  have hpow : (X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2) =
      (X / (2 * Real.pi)) ^ ((w - u) / 2) := by
    have e : (u - w) / 2 = -((w - u) / 2) := by ring
    rw [e, Real.rpow_neg Real.pi_pos.le, ← Real.inv_rpow Real.pi_pos.le,
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  -- assemble
  have hPu0 : 0 ≤ Pu := norm_nonneg _
  have hGu0 : 0 ≤ Gu := norm_nonneg _
  have hZw0 : 0 ≤ Zw := norm_nonneg _
  have hπu : 0 < Real.pi ^ (-((u + 1 / 2) / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hXp : 0 < X ^ ((1 / 2 + η - w) / 2) := Real.rpow_pos_of_pos hX0 _
  have hR : 0 < (X / (2 * Real.pi)) ^ ((w - u) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hX2 : 0 < (X / 2) ^ ((w - u) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hπuw : 0 < Real.pi ^ ((u - w) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  rw [hpi]
  calc Pw * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) * Gw * Zw
      ≤ (2 * Pu) * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) *
          ((X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu) * (C * X ^ ((1 / 2 + η - w) / 2)) := by
        gcongr
    _ = 2 * Real.exp 6 * C * X ^ ((1 / 2 + η - w) / 2) *
          ((X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2)) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by ring
    _ = 2 * Real.exp 6 * C * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by rw [hpow]
    _ ≤ 2 * Real.exp 6 * C * X ^ ((1 / 2 + η - w) / 2) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * (Zu / c)) := by
        have h1 : 1 ≤ Zu / c := by rw [le_div_iff₀ hc]; linarith
        have h0 : 0 ≤ Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu := by positivity
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h0 h1) (by positivity)
    _ = 2 * Real.exp 6 * C / c * X ^ ((1 / 2 + η - w) / 2) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * Zu) := by
        field_simp

end

end RHTower.DeBruijn
