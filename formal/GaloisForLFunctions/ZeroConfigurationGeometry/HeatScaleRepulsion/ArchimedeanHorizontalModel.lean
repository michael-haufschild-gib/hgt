import GaloisForLFunctions.RHTower.ArchimedeanFactorVerticalModel

/-!
# Horizontal growth of the archimedean factor

At height `X ≥ 200`, the factor `G` in `ξ = Gζ` follows the slope
`log(X/(2π))/2 + iπ/4` throughout `0 < Re s ≤ X/32`. This comparison
retains the exponential decay when moving left toward the critical line.
-/

open Complex Set
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The factorization is valid off the real axis, including the critical strip. -/
theorem xi_eq_archG_mul_zeta_offReal {s : ℂ} (hs : s.im ≠ 0) :
    xi s = archG s * riemannZeta s := by
  rw [xi_eq_four_factors_offReal hs, archG]
  ring

/-- Stirling's remainder stays bounded throughout the positive horizontal segment. -/
theorem norm_logDeriv_archG_sub_horizontalSlope_le_one {σ X : ℝ}
    (hσ : 0 < σ) (hσX : σ ≤ X / 32) (hX : 200 ≤ X) :
    ‖logDeriv archG ((σ : ℂ) + X * I) - horizontalSlope X‖ ≤ 1 := by
  have hX0 : 0 < X := by linarith only [hX]
  rw [logDeriv_archG_sub_horizontalSlope_eq hσ hX0]
  set s : ℂ := (σ : ℂ) + X * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = X := by simp [hs]
  have hsX : X ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rwa [hsim, abs_of_pos hX0] at h
  have hs1X : X ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rwa [Complex.sub_im, hsim, Complex.one_im, sub_zero, abs_of_pos hX0] at h
  have hs2 : X / 2 ≤ ‖s / 2‖ := by
    rw [norm_div, Complex.norm_ofNat]
    linarith only [hsX]
  have h1 : ‖1 / s‖ ≤ 1 / X := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hX0 hsX
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / X := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hX0 hs1X
  have h3 : ‖1 / (2 * s)‖ ≤ 1 / (2 * X) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hsX])
  have hD := HTGeometry.norm_digammaStirlingDefect_le
    (z := s / 2) (by simp [hsre, hσ]) (by linarith only [hs2, hX])
  have h4 : ‖HTGeometry.digammaStirlingDefect (s / 2) / 2‖ ≤ 12 / X ^ 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have hsq : (X / 2) ^ 2 ≤ ‖s / 2‖ ^ 2 := by gcongr
    have hdiv : 6 / ‖s / 2‖ ^ (2 : ℕ) ≤ 6 / (X / 2) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    calc ‖HTGeometry.digammaStirlingDefect (s / 2)‖ / 2
        ≤ 6 / (X / 2) ^ 2 / 2 := by gcongr; exact hD.trans hdiv
      _ = 12 / X ^ 2 := by field_simp; ring
  have h5 : ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ ≤ 1 / 32 := by
    have hz : ‖-(I * (σ / X : ℝ))‖ = σ / X := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsmall : σ / X ≤ 1 / 32 := by
      rw [div_le_iff₀ hX0]
      linarith only [hσX]
    have hl := norm_log_one_add_le_two_mul (z := -(I * (σ / X : ℝ)))
      (by rw [hz]; linarith only [hsmall])
    rw [← sub_eq_add_neg, hz] at hl
    rw [norm_div, Complex.norm_ofNat]
    linarith only [hl, hsmall]
  have hsmall : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 ≤ 3 / X := by
    have e : 1 / X + 1 / X + 1 / (2 * X) + 12 / X ^ 2 =
        (5 * X + 24) / (2 * X ^ 2) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hX0]
    have hx24 : 0 ≤ X - 24 := by linarith only [hX]
    nlinarith only [mul_nonneg hX0.le hx24]
  have hlast : 3 / X ≤ 3 / 200 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
  calc
    _ ≤ ‖Complex.log (1 - I * (σ / X : ℝ)) / 2‖ +
        (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖1 / (2 * s)‖ +
          ‖HTGeometry.digammaStirlingDefect (s / 2) / 2‖) := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_sub_le _ _).trans ?_
      gcongr
      exact norm_add_le _ _
    _ ≤ 1 := by linarith only [h1, h2, h3, h4, h5, hsmall, hlast]

theorem hasDerivAt_archG_horizontal {σ X : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun x : ℝ => archG ((x : ℂ) + X * I))
      (deriv archG ((σ : ℂ) + X * I)) σ := by
  have hd := (differentiableAt_archG (w := (σ : ℂ) + X * I) (by simpa using hσ)).hasDerivAt
  have hi : HasDerivAt (fun z : ℂ => z + X * I) 1 (σ : ℂ) :=
    (hasDerivAt_id (σ : ℂ)).add_const (X * I)
  have hc := hd.comp (σ : ℂ) hi
  rw [mul_one] at hc
  exact hc.comp_ofReal

/-- Horizontal transport of `G` has only a bounded relative logarithmic error. -/
theorem norm_archG_horizontal_sub_model_le {X u w : ℝ} (hX : 200 ≤ X)
    (hu : u ∈ Ioc 0 (X / 32)) (hw : w ∈ Ioc 0 (X / 32)) :
    ‖archG ((w : ℂ) + X * I) - archG ((u : ℂ) + X * I) *
        Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ ≤
      ‖archG ((u : ℂ) + X * I)‖ * Real.exp ((w - u) * (horizontalSlope X).re) *
        (Real.exp |w - u| - 1) := by
  have hsub : uIcc u w ⊆ Icc (min u w) (X / 32) :=
    uIcc_subset_Icc ⟨min_le_left _ _, hu.2⟩ ⟨min_le_right _ _, hw.2⟩
  have hpos : 0 < min u w := lt_min hu.1 hw.1
  have hderiv : ∀ x ∈ uIcc u w,
      ‖deriv archG ((x : ℂ) + X * I) - horizontalSlope X * archG ((x : ℂ) + X * I)‖ ≤
        1 * ‖archG ((x : ℂ) + X * I)‖ := by
    intro x hx
    have hx0 := hpos.trans_le (hsub hx).1
    have hne1 : (x : ℂ) + X * I ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add, one_im] at hi
      linarith only [hi, hX]
    have hne := archG_ne_zero (w := (x : ℂ) + X * I) (by simpa using hx0) hne1
    have he : deriv archG ((x : ℂ) + X * I) =
        logDeriv archG ((x : ℂ) + X * I) * archG ((x : ℂ) + X * I) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hne]
    rw [he, ← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_logDeriv_archG_sub_horizontalSlope_le_one hx0 (hsub hx).2 hX) (norm_nonneg _)
  have hm := HTGeometry.norm_sub_mul_exp_le (by norm_num : (0 : ℝ) < 1)
    (fun x hx => hasDerivAt_archG_horizontal (hpos.trans_le (hsub hx).1)) hderiv
  simpa only [one_mul] using hm

/-- The leftward decay factor is preserved in the modulus comparison. -/
theorem norm_archG_horizontal_le_model {X u w : ℝ} (hX : 200 ≤ X)
    (hu : u ∈ Ioc 0 (X / 32)) (hw : w ∈ Ioc 0 (X / 32)) :
    ‖archG ((w : ℂ) + X * I)‖ ≤
      ‖archG ((u : ℂ) + X * I)‖ * Real.exp ((w - u) * (horizontalSlope X).re) *
        Real.exp |w - u| := by
  have hm := norm_archG_horizontal_sub_model_le hX hu hw
  have hn := norm_sub_norm_le (archG ((w : ℂ) + X * I))
    (archG ((u : ℂ) + X * I) * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X))
  rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul] at hn
  nlinarith only [hm, hn]

#print axioms norm_archG_horizontal_le_model

end

end GaloisForLFunctions.ZeroConfigurationGeometry
