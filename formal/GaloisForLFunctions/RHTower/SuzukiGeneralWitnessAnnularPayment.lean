import GaloisForLFunctions.RHTower.SuzukiAnnularTailSumPayment

/-!
# The annular payment needs no critical-line witness

The two exact height estimates behind the annular payment used the critical line only to make the
witness coordinates explicit.  The strip bound `u < 1/4` already pins both coordinates of an
arbitrary shifted atom: with `X = 1 + k - u` and `Y² = 4uk` for `k` the squared ordinate and `u` the
squared centered abscissa,

`τ = (X² - Y²)/(X(X² + Y²)) ≤ 1/X ≤ 1/(k + 3/4)`,
`a = X/(X² + Y²) ≥ 1/(k + 3)`,

because `X(k + 3) - X² = X(2 + u) ≥ 2k + 3/2 > 4uk = Y²`.  The slope of a high witness is therefore
small and its mass is of the exact reciprocal-height order, whether or not the witness sits on the
critical line.

Consequently the payment criterion is the same tail sum with the band floor moved from `3h` to
`3(1 + h)`, and the witnesses may be *any* Xi copies.  The zero-counting input drops from a
critical-line proportion to plain Riemann–von Mangoldt counting.
-/

open Finset

namespace RHTower

noncomputable section

/-! ## Coordinates of an arbitrary witness -/

/-- The squared centered node coordinates of a copy in height and abscissa variables. -/
theorem xiSquaredNode_coords (r : XiZeroCopy) :
    (xiSquaredNode r).re = (r.1 : ℂ).im ^ (2 : ℕ) - ((r.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) ∧
      (xiSquaredNode r).im ^ (2 : ℕ) = 4 * ((r.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) * (r.1 : ℂ).im ^ (2 : ℕ) := by
  refine ⟨xiSquaredNode_re r, ?_⟩
  rw [xiSquaredNode_im]
  ring

/-- **A high witness has a small response slope.**  No criticality is used: the strip bound alone
puts the slope below the reciprocal height. -/
theorem responseSlope_le_inv_height (r : XiZeroCopy) :
    xiShiftedResponseSlope 1 r ≤ 1 / ((r.1 : ℂ).im ^ (2 : ℕ) + 3 / 4) := by
  set k : ℝ := (r.1 : ℂ).im ^ (2 : ℕ) with hk
  set u : ℝ := ((r.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) with hu
  obtain ⟨hre, him⟩ := xiSquaredNode_coords r
  rw [← hk, ← hu] at hre him
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu4 : u < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter r.1
  have hk0 : (41 / 2 : ℝ) < k := xiZeroCopy_fortyOne_div_two_lt_im_sq r
  set X : ℝ := 1 + (xiSquaredNode r).re with hX
  set Y : ℝ := (xiSquaredNode r).im with hY
  have hXval : X = 1 + k - u := by rw [hX, hre]; ring
  have hXpos : 0 < X := by rw [hXval]; linarith
  have hXge : k + 3 / 4 ≤ X := by rw [hXval]; linarith
  have hD : 0 < X ^ (2 : ℕ) + Y ^ (2 : ℕ) := by positivity
  have hY0 : 0 ≤ Y ^ (2 : ℕ) := sq_nonneg Y
  have hslope : xiShiftedResponseSlope 1 r = (X ^ (2 : ℕ) - Y ^ (2 : ℕ)) / (X * (X ^ (2 : ℕ) + Y ^ (2 : ℕ))) := by
    rw [xiShiftedResponseSlope_one_eq, ← hX, ← hY]
  rw [hslope, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hXpos, hD, hY0, hXge, hk0, sq_nonneg X]

/-- **Every witness carries at least the reciprocal-height mass.**  The strip bound gives
`X(k + 3) - X² = X(2 + u) ≥ 2k + 3/2 > 4uk = Y²`. -/
theorem responseMass_ge_inv_height (r : XiZeroCopy) :
    1 / ((r.1 : ℂ).im ^ (2 : ℕ) + 3) ≤ xiShiftedResponseMass 1 r := by
  set k : ℝ := (r.1 : ℂ).im ^ (2 : ℕ) with hk
  set u : ℝ := ((r.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) with hu
  obtain ⟨hre, him⟩ := xiSquaredNode_coords r
  rw [← hk, ← hu] at hre him
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hu4 : u < 1 / 4 := xi_divisor_support_centered_re_sq_lt_quarter r.1
  have hk0 : (41 / 2 : ℝ) < k := xiZeroCopy_fortyOne_div_two_lt_im_sq r
  set X : ℝ := 1 + (xiSquaredNode r).re with hX
  set Y : ℝ := (xiSquaredNode r).im with hY
  have hXval : X = 1 + k - u := by rw [hX, hre]; ring
  have hY2 : Y ^ (2 : ℕ) = 4 * u * k := by rw [hY, him]
  have hXpos : 0 < X := by rw [hXval]; linarith
  have hD : 0 < X ^ (2 : ℕ) + Y ^ (2 : ℕ) := by positivity
  have hmass : xiShiftedResponseMass 1 r = X / (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) := by
    rw [xiShiftedResponseMass_one_eq, ← hX, ← hY]
  rw [hmass, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hY2, hXval]
  nlinarith [hu0, hu4, hk0]

/-! ## The general slope gap -/

/-- **The slope gap without criticality.**  Any copy whose squared ordinate clears `3(1 + h)` is
separated from an off-line atom of squared ordinate `h` by the sector floor. -/
theorem slope_gap_sq_gt_general (q r : XiZeroCopy)
    (hlow : 3 * (1 + (q.1 : ℂ).im ^ (2 : ℕ)) ≤ (r.1 : ℂ).im ^ (2 : ℕ))
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ (2 : ℕ)) :
    256 / (625 * (1 + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ))
      < (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) := by
  set h : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) with hh
  set k : ℝ := (r.1 : ℂ).im ^ (2 : ℕ) with hk
  have hh0 : 0 < h := by linarith
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hk34 : (0 : ℝ) < k + 3 / 4 := by nlinarith
  have hq := slope_gt_of_height q
  rw [← hh] at hq
  have hr := responseSlope_le_inv_height r
  rw [← hk] at hr
  have hstep : 1 / (k + 3 / 4) ≤ 143 / (425 * (1 + h)) := by
    rw [div_le_div_iff₀ hk34 (by positivity)]
    nlinarith [hlow, hden1]
  have hgap : 16 / (25 * (1 + h)) < xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r := by
    have harith : 16 / (25 * (1 + h)) = 83 / (85 * (1 + h)) - 143 / (425 * (1 + h)) := by
      field_simp
      ring
    rw [harith]
    linarith
  have hpos : (0 : ℝ) < 16 / (25 * (1 + h)) := by positivity
  have hsq : (16 / (25 * (1 + h))) ^ (2 : ℕ)
      < (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hgap hpos.le (by norm_num)
  have hval : (16 / (25 * (1 + h))) ^ (2 : ℕ) = 256 / (625 * (1 + h) ^ (2 : ℕ)) := by
    field_simp
    ring
  linarith [hval ▸ hsq]

/-! ## The general payment -/

/-- **`(SR-64.28)` without criticality.**  An arbitrary finite family of Xi copies above
`3(1 + h)` pays the complete-mass-normalized charge of one off-line atom as soon as its total
response mass clears `29/(256(1+h))`. -/
theorem tailSum_general_payment (q : XiZeroCopy) {S : Finset XiZeroCopy}
    (hS : S.Nonempty)
    (hlow : ∀ r ∈ S, 3 * (1 + (q.1 : ℂ).im ^ (2 : ℕ)) ≤ (r.1 : ℂ).im ^ (2 : ℕ))
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ (2 : ℕ))
    (hmass : 29 / (256 * (1 + (q.1 : ℂ).im ^ (2 : ℕ))) ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r) :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) * xiShiftedTransverseChargeDensity 1 q
      < xiShiftedResponseMass 1 q *
        ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) := by
  set h : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) with hh
  have hh0 : 0 < h := by linarith
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hmq : 0 < xiShiftedResponseMass 1 q := xiShiftedResponseMass_pos (by norm_num) q
  set A : ℝ := ∑' i : XiZeroCopy, xiShiftedResponseMass 1 i with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact tsum_nonneg fun i => (xiShiftedResponseMass_pos (by norm_num) i).le
  have hAlt : A < (29 / 625 : ℝ) := tsum_xiShiftedResponseMass_one_lt
  have hratio := chargeRatio_lt_inv_cube q
  rw [← hh] at hratio
  have hchi : xiShiftedTransverseChargeDensity 1 q
      < 1 / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q := by
    rw [div_lt_iff₀ hmq] at hratio
    exact hratio
  have hXpos : (0 : ℝ) < 1 / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q := by positivity
  have hchargebound : A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q := by
    calc A * xiShiftedTransverseChargeDensity 1 q
        ≤ A * (1 / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q) :=
          mul_le_mul_of_nonneg_left hchi.le hA0
      _ < (29 / 625 : ℝ) * (1 / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q) :=
          mul_lt_mul_of_pos_right hAlt hXpos
      _ = (29 / 625 : ℝ) / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q := by ring
  have hterm : ∀ r ∈ S,
      xiShiftedResponseMass 1 r * (256 / (625 * (1 + h) ^ (2 : ℕ)))
        < xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) := by
    intro r hr
    have hgap := slope_gap_sq_gt_general q r (by rw [← hh]; exact hlow r hr) hheight
    rw [← hh] at hgap
    exact mul_lt_mul_of_pos_left hgap (xiShiftedResponseMass_pos (by norm_num) r)
  have hsumlt : (∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ (2 : ℕ)))
      < ∑ r ∈ S, xiShiftedResponseMass 1 r
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_lt_sum_of_nonempty hS hterm
  have hfloor : (29 / 625 : ℝ) / (1 + h) ^ (3 : ℕ)
      ≤ (∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ (2 : ℕ))) := by
    have hcoef : (0 : ℝ) < 256 / (625 * (1 + h) ^ (2 : ℕ)) := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmass hcoef.le
    refine le_trans (le_of_eq ?_) hstep
    field_simp
  calc A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ (3 : ℕ) * xiShiftedResponseMass 1 q := hchargebound
    _ ≤ ((∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ (2 : ℕ))))
          * xiShiftedResponseMass 1 q := mul_le_mul_of_nonneg_right hfloor hmq.le
    _ < (∑ r ∈ S, xiShiftedResponseMass 1 r
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ))
          * xiShiftedResponseMass 1 q := mul_lt_mul_of_pos_right hsumlt hmq
    _ = xiShiftedResponseMass 1 q *
          ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) := by ring

/-- **The general annulus mass floor.**  A constant number of arbitrary Xi copies inside an annulus
of fixed ratio clears the payment floor. -/
theorem annulus_general_mass_floor (q : XiZeroCopy) {S : Finset XiZeroCopy} {K : ℝ}
    (hK : 1 ≤ K)
    (hhigh : ∀ r ∈ S, (r.1 : ℂ).im ^ (2 : ℕ) ≤ 3 * K ^ (2 : ℕ) * (1 + (q.1 : ℂ).im ^ (2 : ℕ)))
    (hcard : (87 / 256 : ℝ) * K ^ (2 : ℕ) + 1 ≤ (S.card : ℝ)) :
    29 / (256 * (1 + (q.1 : ℂ).im ^ (2 : ℕ))) ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := by
  set h : ℝ := (q.1 : ℂ).im ^ (2 : ℕ) with hh
  have hh0 : 0 < h := by
    have := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    rw [← hh] at this
    linarith
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hbig : (0 : ℝ) < 3 * K ^ (2 : ℕ) * (1 + h) + 3 := by positivity
  have hterm : ∀ r ∈ S, 1 / (3 * K ^ (2 : ℕ) * (1 + h) + 3) ≤ xiShiftedResponseMass 1 r := by
    intro r hr
    refine le_trans ?_ (responseMass_ge_inv_height r)
    have hk : (r.1 : ℂ).im ^ (2 : ℕ) ≤ 3 * K ^ (2 : ℕ) * (1 + h) := by
      rw [← hh] at *
      exact hhigh r hr
    have hkpos : (0 : ℝ) < (r.1 : ℂ).im ^ (2 : ℕ) + 3 := by
      have := xiZeroCopy_fortyOne_div_two_lt_im_sq r
      linarith
    apply div_le_div_of_nonneg_left (by norm_num) hkpos
    linarith
  have hsum : (S.card : ℝ) * (1 / (3 * K ^ (2 : ℕ) * (1 + h) + 3))
      ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := by
    calc (S.card : ℝ) * (1 / (3 * K ^ (2 : ℕ) * (1 + h) + 3))
        = ∑ _r ∈ S, (1 / (3 * K ^ (2 : ℕ) * (1 + h) + 3)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := Finset.sum_le_sum hterm
  refine le_trans ?_ hsum
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hcard
    (by positivity : (0 : ℝ) ≤ 1 / (3 * K ^ (2 : ℕ) * (1 + h) + 3)))
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hh0, hden1, hK0, sq_nonneg K, mul_nonneg (sq_nonneg K) hden1.le]

/-- **The general fixed-annulus payment.**  A constant number of Xi copies — on or off the critical
line — inside an annulus of any fixed ratio pays the complete-mass-normalized charge of one
off-line atom. -/
theorem annulus_general_payment (q : XiZeroCopy) {S : Finset XiZeroCopy} {K : ℝ}
    (hS : S.Nonempty) (hK : 1 ≤ K)
    (hlow : ∀ r ∈ S, 3 * (1 + (q.1 : ℂ).im ^ (2 : ℕ)) ≤ (r.1 : ℂ).im ^ (2 : ℕ))
    (hhigh : ∀ r ∈ S, (r.1 : ℂ).im ^ (2 : ℕ) ≤ 3 * K ^ (2 : ℕ) * (1 + (q.1 : ℂ).im ^ (2 : ℕ)))
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ (2 : ℕ))
    (hcard : (87 / 256 : ℝ) * K ^ (2 : ℕ) + 1 ≤ (S.card : ℝ)) :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) * xiShiftedTransverseChargeDensity 1 q
      < xiShiftedResponseMass 1 q *
        ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ (2 : ℕ) :=
  tailSum_general_payment q hS hlow hheight (annulus_general_mass_floor q hK hhigh hcard)

end

end RHTower
