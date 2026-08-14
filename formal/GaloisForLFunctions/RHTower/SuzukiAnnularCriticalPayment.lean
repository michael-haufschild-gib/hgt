import GaloisForLFunctions.RHTower.SuzukiCriticalRadicalAnchor

/-!
# Exact annular payment by two critical-line witnesses

At the safe shift every atom has explicit rational coordinates: with `X = 1 + Re N`, `Y = Im N` for
the squared centered node `N`, and `D = X² + Y²`,

`a = X/D`,  `τ = (X² - Y²)/(X D)`,  `χ/a = Y²/(X² D)`.

The strip bound `u² < 1/4`, the off-line height gap `85 < h` and the sector `84 Y² < X²` turn these
into the two exact estimates the annular payment needs: the charge of an off-line atom is at most
`29/(625 (1+h)³)` after multiplication by the total mass, while one critical-line witness whose
squared ordinate lies in `[3h, (432/25) h]` contributes more than `16/(675 (1+h)³)`.  Two witnesses
therefore pay the charge with the exact margin `32/675 - 29/625 = 425/421875 > 0`.
-/

namespace RHTower

noncomputable section

/-! ## Safe-shift coordinates -/

theorem xiShiftedResponseMass_one_eq (q : XiZeroCopy) :
    xiShiftedResponseMass 1 q
      = (1 + (xiSquaredNode q).re)
        / ((1 + (xiSquaredNode q).re) ^ 2 + (xiSquaredNode q).im ^ 2) := by
  have hinv := xiShiftedReciprocalSquare_eq_inv (v := 1) (by norm_num) q
  rw [Complex.ofReal_one] at hinv
  rw [xiShiftedResponseMass, hinv, Complex.inv_re]
  have hre : ((1 : ℂ) + xiSquaredNode q).re = 1 + (xiSquaredNode q).re := by simp
  have hnorm : Complex.normSq ((1 : ℂ) + xiSquaredNode q)
      = (1 + (xiSquaredNode q).re) ^ 2 + (xiSquaredNode q).im ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hre, hnorm]

theorem xiShiftedResponseSlope_one_eq (q : XiZeroCopy) :
    xiShiftedResponseSlope 1 q
      = ((1 + (xiSquaredNode q).re) ^ 2 - (xiSquaredNode q).im ^ 2)
        / ((1 + (xiSquaredNode q).re)
          * ((1 + (xiSquaredNode q).re) ^ 2 + (xiSquaredNode q).im ^ 2)) := by
  set X : ℝ := 1 + (xiSquaredNode q).re with hX
  set Y : ℝ := (xiSquaredNode q).im with hY
  have hXpos : 0 < X := by
    rw [hX]
    have := xiSquaredNode_re_pos q
    linarith
  have hD : 0 < X ^ 2 + Y ^ 2 := by positivity
  have hinv := xiShiftedReciprocalSquare_eq_inv (v := 1) (by norm_num) q
  rw [Complex.ofReal_one] at hinv
  have hsq : (xiShiftedReciprocalSquare 1 q ^ 2).re
      = (X ^ 2 - Y ^ 2) / (X ^ 2 + Y ^ 2) ^ 2 := by
    rw [hinv, inv_pow, Complex.inv_re, Complex.normSq_apply]
    have hre2 : (((1 : ℂ) + xiSquaredNode q) ^ 2).re = X ^ 2 - Y ^ 2 := by
      rw [pow_two, Complex.mul_re]
      simp [hX, hY]
      ring
    have him2 : (((1 : ℂ) + xiSquaredNode q) ^ 2).im = 2 * X * Y := by
      rw [pow_two, Complex.mul_im]
      simp [hX, hY]
      ring
    rw [hre2, him2]
    have hnorm : (X ^ 2 - Y ^ 2) * (X ^ 2 - Y ^ 2) + 2 * X * Y * (2 * X * Y)
        = (X ^ 2 + Y ^ 2) ^ 2 := by ring
    rw [hnorm]
  rw [xiShiftedResponseSlope, hsq, xiShiftedResponseMass_one_eq q, ← hX, ← hY]
  field_simp

theorem xiShiftedTransverseChargeDensity_one_eq (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity 1 q
      = (xiSquaredNode q).im ^ 2
        / ((1 + (xiSquaredNode q).re)
          * ((1 + (xiSquaredNode q).re) ^ 2 + (xiSquaredNode q).im ^ 2) ^ 2) := by
  set X : ℝ := 1 + (xiSquaredNode q).re with hX
  set Y : ℝ := (xiSquaredNode q).im with hY
  have hXpos : 0 < X := by
    rw [hX]
    have := xiSquaredNode_re_pos q
    linarith
  have hD : 0 < X ^ 2 + Y ^ 2 := by positivity
  have hinv := xiShiftedReciprocalSquare_eq_inv (v := 1) (by norm_num) q
  rw [Complex.ofReal_one] at hinv
  have him : (xiShiftedReciprocalSquare 1 q).im = -Y / (X ^ 2 + Y ^ 2) := by
    rw [hinv, Complex.inv_im, Complex.normSq_apply]
    have h1 : ((1 : ℂ) + xiSquaredNode q).im = Y := by simp [hY]
    have h2 : ((1 : ℂ) + xiSquaredNode q).re = X := by simp [hX]
    rw [h1, h2]
    field_simp
  have hnormSq : Complex.normSq (xiShiftedReciprocalSquare 1 q) = 1 / (X ^ 2 + Y ^ 2) := by
    rw [hinv, Complex.normSq_inv, Complex.normSq_apply]
    have h1 : ((1 : ℂ) + xiSquaredNode q).im = Y := by simp [hY]
    have h2 : ((1 : ℂ) + xiSquaredNode q).re = X := by simp [hX]
    rw [h1, h2]
    field_simp
  rw [xiShiftedTransverseChargeDensity, him, hnormSq, xiShiftedResponseMass_one_eq q, ← hX, ← hY]
  field_simp

/-! ## The two exact height estimates -/

/-- **`(SR-64.15)`--`(SR-64.16)`: the atomwise charge-to-mass bound in height coordinates.** -/
theorem chargeRatio_lt_inv_cube (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity 1 q / xiShiftedResponseMass 1 q
      < 1 / (1 + (q.1 : ℂ).im ^ 2) ^ 3 := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  set u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu4 : u < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hheight : (41 / 2 : ℝ) < h := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hnre : (xiSquaredNode q).re = h - u := by
    rw [xiSquaredNode_re, hh, hu]
  have hnim : (xiSquaredNode q).im ^ 2 = 4 * u * h := by
    rw [xiSquaredNode_im, hu, hh]
    ring
  set X : ℝ := 1 + (xiSquaredNode q).re with hX
  set Y2 : ℝ := (xiSquaredNode q).im ^ 2 with hY2
  have hXval : X = 1 + h - u := by rw [hX, hnre]; ring
  have hXlarge : h + 3 / 4 < X := by rw [hXval]; linarith
  have hXpos : 0 < X := by linarith
  have hY2lt : Y2 < h := by
    rw [hnim]
    nlinarith [hheight, hu4, hu0]
  have hY20 : 0 ≤ Y2 := by rw [hY2]; positivity
  have hD : 0 < X ^ 2 + Y2 := by positivity
  have hratio : xiShiftedTransverseChargeDensity 1 q / xiShiftedResponseMass 1 q
      = Y2 / (X ^ 2 * (X ^ 2 + Y2)) := by
    rw [xiShiftedTransverseChargeDensity_one_eq, xiShiftedResponseMass_one_eq, ← hX, ← hY2]
    field_simp
  rw [hratio, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hcube : 0 < (1 + h) ^ 3 := by positivity
  have hkey : Y2 * (1 + h) ^ 3 < X ^ 2 * (X ^ 2 + Y2) := by
    have hX4 : X ^ 2 * (X ^ 2 + Y2) ≥ X ^ 4 := by nlinarith [hY20, sq_nonneg X]
    have hpoly : h * (1 + h) ^ 3 < (h + 3 / 4) ^ 4 := by nlinarith [hheight]
    have hXpow : (h + 3 / 4) ^ 4 < X ^ 4 := by
      have h1 : (0:ℝ) ≤ h + 3 / 4 := by linarith
      exact pow_lt_pow_left₀ hXlarge h1 (by norm_num)
    nlinarith [hY2lt, hcube, hpoly, hXpow, hX4]
  linarith

/-- **`(SR-64.18)`: the off-line response slope stays above the sector floor.** -/
theorem slope_gt_of_height (q : XiZeroCopy) :
    83 / (85 * (1 + (q.1 : ℂ).im ^ 2)) < xiShiftedResponseSlope 1 q := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  set u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu4 : u < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hheight : (41 / 2 : ℝ) < h := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hnre : (xiSquaredNode q).re = h - u := by rw [xiSquaredNode_re, hh, hu]
  set X : ℝ := 1 + (xiSquaredNode q).re with hX
  set Y2 : ℝ := (xiSquaredNode q).im ^ 2 with hY2
  have hXval : X = 1 + h - u := by rw [hX, hnre]; ring
  have hXpos : 0 < X := by rw [hXval]; linarith
  have hXsmall : X ≤ 1 + h := by rw [hXval]; linarith
  have hY20 : 0 ≤ Y2 := by rw [hY2]; positivity
  have hsector : 84 * Y2 < X ^ 2 := by
    have := eightyFour_mul_xiSquaredNode_im_sq_lt (y := 1) (by norm_num) q
    rw [hY2, hX]
    simpa using this
  have hslope : xiShiftedResponseSlope 1 q = (X ^ 2 - Y2) / (X * (X ^ 2 + Y2)) := by
    rw [xiShiftedResponseSlope_one_eq, ← hX, ← hY2]
  rw [hslope, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hsector, hY20, hXpos, hXsmall, hheight, sq_nonneg X, mul_pos hXpos hXpos]

/-- On the critical line both coordinates collapse to the reciprocal height. -/
theorem criticalLine_mass_and_slope (r : XiZeroCopy) (hcrit : (r.1 : ℂ).re = 1 / 2) :
    xiShiftedResponseMass 1 r = 1 / (1 + (r.1 : ℂ).im ^ 2) ∧
      xiShiftedResponseSlope 1 r = 1 / (1 + (r.1 : ℂ).im ^ 2) := by
  set k : ℝ := (r.1 : ℂ).im ^ 2 with hk
  have hnre : (xiSquaredNode r).re = k := by
    rw [xiSquaredNode_re, hcrit, hk]
    ring
  have hnim : (xiSquaredNode r).im = 0 := by
    rw [xiSquaredNode_im, hcrit]
    ring
  have hkpos : 0 < 1 + k := by
    have := xiZeroCopy_fortyOne_div_two_lt_im_sq r
    rw [← hk] at this
    linarith
  have hne : (1:ℝ) + k ≠ 0 := ne_of_gt hkpos
  constructor
  · rw [xiShiftedResponseMass_one_eq, hnre, hnim]
    rw [show ((0:ℝ)) ^ 2 = 0 by norm_num, add_zero, pow_two]
    field_simp
  · rw [xiShiftedResponseSlope_one_eq, hnre, hnim]
    rw [show ((0:ℝ)) ^ 2 = 0 by norm_num, add_zero, sub_zero, pow_two]
    field_simp

/-! ## The annular payment -/

/-- **`(SR-64.21)`: one critical-line witness in the annulus.** -/
theorem annular_single_witness (q r : XiZeroCopy) (hcrit : (r.1 : ℂ).re = 1 / 2)
    (hlow : 3 * (q.1 : ℂ).im ^ 2 ≤ (r.1 : ℂ).im ^ 2)
    (hhigh : (r.1 : ℂ).im ^ 2 ≤ (432 / 25 : ℝ) * (q.1 : ℂ).im ^ 2)
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ 2) :
    16 / (675 * (1 + (q.1 : ℂ).im ^ 2) ^ 3)
      < xiShiftedResponseMass 1 r
        * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  set k : ℝ := (r.1 : ℂ).im ^ 2 with hk
  have hh0 : 0 < h := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨hmass, hslope⟩ := criticalLine_mass_and_slope r hcrit
  rw [← hk] at hmass hslope
  have hq := slope_gt_of_height q
  rw [← hh] at hq
  have hden1 : (0:ℝ) < 1 + h := by linarith
  have hden3 : (0:ℝ) < 1 + 3 * h := by linarith
  have hdenk : (0:ℝ) < 1 + k := by linarith
  have hslope_r_le : xiShiftedResponseSlope 1 r ≤ 1 / (1 + 3 * h) := by
    rw [hslope]
    apply div_le_div_of_nonneg_left (by norm_num) hden3
    linarith
  have hgap : 16 / (25 * (1 + h)) < xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r := by
    have hstep : 16 / (25 * (1 + h)) ≤ 83 / (85 * (1 + h)) - 1 / (1 + 3 * h) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [hheight, hden1, hden3]
    linarith
  have hgapsq : 256 / (625 * (1 + h) ^ 2)
      < (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
    have hpos : (0:ℝ) < 16 / (25 * (1 + h)) := by positivity
    have hsq : (16 / (25 * (1 + h))) ^ 2 < (xiShiftedResponseSlope 1 q
        - xiShiftedResponseSlope 1 r) ^ 2 := by
      apply pow_lt_pow_left₀ hgap hpos.le (by norm_num)
    have hval : (16 / (25 * (1 + h))) ^ 2 = 256 / (625 * (1 + h) ^ 2) := by
      field_simp
      ring
    linarith [hval ▸ hsq]
  have hmass_ge : 25 / (432 * (1 + h)) ≤ xiShiftedResponseMass 1 r := by
    rw [hmass, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hhigh, hh0]
  have hprod : 25 / (432 * (1 + h)) * (256 / (625 * (1 + h) ^ 2))
      = 16 / (675 * (1 + h) ^ 3) := by
    field_simp
    ring
  calc 16 / (675 * (1 + h) ^ 3)
      = 25 / (432 * (1 + h)) * (256 / (625 * (1 + h) ^ 2)) := hprod.symm
    _ < xiShiftedResponseMass 1 r
        * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
        have hm0 : (0:ℝ) < 25 / (432 * (1 + h)) := by positivity
        have hs0 : (0:ℝ) < 256 / (625 * (1 + h) ^ 2) := by positivity
        nlinarith [hmass_ge, hgapsq, hm0, hs0]

/-- The complete safe-shift response mass is below the exact rational source cap. -/
theorem tsum_xiShiftedResponseMass_one_lt :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) < (29 / 625 : ℝ) := by
  have hle := re_xiShiftedReciprocalMoment_one_zero_le_normalizedPrimeArchMoment_zero
  have hlt := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  rw [← tsum_xiShiftedResponseMass_eq_moment_re (y := 1) (by norm_num)] at hle
  linarith

/-- **`(SR-64.22)`: two annular witnesses strictly pay one off-line atom's charge.** -/
theorem two_witness_annular_payment (q r₁ r₂ : XiZeroCopy)
    (hcrit₁ : (r₁.1 : ℂ).re = 1 / 2) (hcrit₂ : (r₂.1 : ℂ).re = 1 / 2)
    (hlow₁ : 3 * (q.1 : ℂ).im ^ 2 ≤ (r₁.1 : ℂ).im ^ 2)
    (hhigh₁ : (r₁.1 : ℂ).im ^ 2 ≤ (432 / 25 : ℝ) * (q.1 : ℂ).im ^ 2)
    (hlow₂ : 3 * (q.1 : ℂ).im ^ 2 ≤ (r₂.1 : ℂ).im ^ 2)
    (hhigh₂ : (r₂.1 : ℂ).im ^ 2 ≤ (432 / 25 : ℝ) * (q.1 : ℂ).im ^ 2)
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ 2) :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i)
        * xiShiftedTransverseChargeDensity 1 q
      < xiShiftedResponseMass 1 q
        * (xiShiftedResponseMass 1 r₁
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₁) ^ 2
          + xiShiftedResponseMass 1 r₂
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₂) ^ 2) := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  have hh0 : 0 < h := by linarith
  have hden : (0:ℝ) < (1 + h) ^ 3 := by positivity
  set A : ℝ := ∑' i : XiZeroCopy, xiShiftedResponseMass 1 i with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact tsum_nonneg fun i => (xiShiftedResponseMass_pos (by norm_num) i).le
  have hAlt : A < (29 / 625 : ℝ) := tsum_xiShiftedResponseMass_one_lt
  have hmq : 0 < xiShiftedResponseMass 1 q := xiShiftedResponseMass_pos (by norm_num) q
  have hratio := chargeRatio_lt_inv_cube q
  rw [← hh] at hratio
  have hchi : xiShiftedTransverseChargeDensity 1 q
      < 1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by
    rw [div_lt_iff₀ hmq] at hratio
    exact hratio
  have hXpos : (0:ℝ) < 1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by positivity
  have hchargebound : A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by
    calc A * xiShiftedTransverseChargeDensity 1 q
        ≤ A * (1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q) :=
          mul_le_mul_of_nonneg_left hchi.le hA0
      _ < (29 / 625 : ℝ) * (1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q) :=
          mul_lt_mul_of_pos_right hAlt hXpos
      _ = (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by ring
  have hw₁ := annular_single_witness q r₁ hcrit₁ hlow₁ hhigh₁ hheight
  have hw₂ := annular_single_witness q r₂ hcrit₂ hlow₂ hhigh₂ hheight
  rw [← hh] at hw₁ hw₂
  have hmargin : (29 / 625 : ℝ) / (1 + h) ^ 3 < 32 / (675 * (1 + h) ^ 3) := by
    rw [div_lt_div_iff₀ hden (by positivity)]
    nlinarith [hden]
  have hsum : 32 / (675 * (1 + h) ^ 3)
      < xiShiftedResponseMass 1 r₁
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₁) ^ 2
        + xiShiftedResponseMass 1 r₂
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₂) ^ 2 := by
    have hval : 32 / (675 * (1 + h) ^ 3) = 16 / (675 * (1 + h) ^ 3)
        + 16 / (675 * (1 + h) ^ 3) := by ring
    rw [hval]
    linarith
  calc A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := hchargebound
    _ < 32 / (675 * (1 + h) ^ 3) * xiShiftedResponseMass 1 q :=
        mul_lt_mul_of_pos_right hmargin hmq
    _ < xiShiftedResponseMass 1 q
        * (xiShiftedResponseMass 1 r₁
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₁) ^ 2
          + xiShiftedResponseMass 1 r₂
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r₂) ^ 2) := by
        have := mul_lt_mul_of_pos_left hsum hmq
        linarith

end

end RHTower
