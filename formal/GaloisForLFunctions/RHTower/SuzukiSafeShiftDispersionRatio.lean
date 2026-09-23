import GaloisForLFunctions.RHTower.SuzukiSafeShiftResponseChargeCancellation

/-!
# Quantitative safe-shift dispersion/charge ratio

Every positive shifted reciprocal-square Xi atom lies in the quadratic sector

`Im(lambda)^(2 : ℕ) <= Re(lambda)^(2 : ℕ) / 84`.

For its response mass `e`, response slope `x`, and transverse charge density `chi`, the sharp
endpoint algebra of that sector gives

`6889 chi <= 85 e x^(2 : ℕ)`.

After summation, the first shifted Hankel minor is therefore nonnegative as soon as the normalized
response dispersion carries the explicit coefficient-of-variation floor `85 / 6889`.  No zero
computation, RH assumption, or finite-divisor truncation enters the proof.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Shifted quadratic sector -/

/-- The node-side `1/84` sector is invariant under inversion, hence holds for every shifted
reciprocal-square Xi atom. -/
theorem xiShiftedReciprocalSquare_im_sq_le_one_div_eightyFour_re_sq
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) <=
      (1 / 84 : ℝ) * (xiShiftedReciprocalSquare y q).re ^ (2 : ℕ) := by
  let d : ℂ := (y : ℂ) + xiSquaredNode q
  have hd : d ≠ 0 := ofReal_add_xiSquaredNode_ne_zero hy.le q
  have hnorm : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd
  have hnode := eightyFour_mul_xiSquaredNode_im_sq_lt hy q
  have hdre : d.re = y + (xiSquaredNode q).re := by
    simp [d]
  have hdim : d.im = (xiSquaredNode q).im := by
    simp [d]
  rw [xiShiftedReciprocalSquare_eq_inv hy.le]
  change (d⁻¹).im ^ (2 : ℕ) <= (1 / 84 : ℝ) * (d⁻¹).re ^ (2 : ℕ)
  rw [Complex.inv_im, Complex.inv_re]
  rw [div_pow, div_pow]
  have hbase : d.im ^ (2 : ℕ) <= (1 / 84 : ℝ) * d.re ^ (2 : ℕ) := by
    rw [hdre, hdim]
    nlinarith
  calc
    (-d.im) ^ (2 : ℕ) / Complex.normSq d ^ (2 : ℕ) =
        d.im ^ (2 : ℕ) / Complex.normSq d ^ (2 : ℕ) := by ring
    _ <= ((1 / 84 : ℝ) * d.re ^ (2 : ℕ)) / Complex.normSq d ^ (2 : ℕ) :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hnorm)).2 hbase
    _ = (1 / 84 : ℝ) * (d.re ^ (2 : ℕ) / Complex.normSq d ^ (2 : ℕ)) := by ring

/-! ## Sharp atomwise response/charge comparison -/

/-- Sharp endpoint polynomial behind the constant `85 / 6889`.

Writing `X = Re(lambda)^(2 : ℕ)` and `U = Im(lambda)^(2 : ℕ)`, the difference factors as

`85 (X-U)^(2 : ℕ) - 6889 U (X+U) = (X-84U)(85X+81U)`.
-/
theorem transverseChargeDensity_ratio_polynomial
    {a b : ℝ} (hsector : b ^ (2 : ℕ) <= (1 / 84 : ℝ) * a ^ (2 : ℕ)) :
    6889 * (b ^ (2 : ℕ) * (a ^ (2 : ℕ) + b ^ (2 : ℕ))) <=
      85 * (a ^ (2 : ℕ) - b ^ (2 : ℕ)) ^ (2 : ℕ) := by
  have hcone : 0 <= a ^ (2 : ℕ) - 84 * b ^ (2 : ℕ) := by
    norm_num at hsector ⊢
    nlinarith
  have hfactor : 0 <= 85 * a ^ (2 : ℕ) + 81 * b ^ (2 : ℕ) := by positivity
  have hproduct := mul_nonneg hcone hfactor
  nlinarith

/-- Every shifted atom pays at most `85 / 6889` of its longitudinal second response energy as
transverse charge. -/
theorem sixThousandEightHundredEightyNine_mul_xiShiftedTransverseChargeDensity_le
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    6889 * xiShiftedTransverseChargeDensity y q <=
      85 * (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) := by
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < z.re := xiShiftedResponseMass_pos hy q
  have hsector : z.im ^ (2 : ℕ) <= (1 / 84 : ℝ) * z.re ^ (2 : ℕ) := by
    simpa only [z] using
      xiShiftedReciprocalSquare_im_sq_le_one_div_eightyFour_re_sq hy q
  have hpoly := transverseChargeDensity_ratio_polynomial hsector
  unfold xiShiftedTransverseChargeDensity xiShiftedResponseMass xiShiftedResponseSlope
  change 6889 * (z.im ^ (2 : ℕ) * Complex.normSq z / z.re) <=
    85 * (z.re * ((z ^ (2 : ℕ)).re / z.re) ^ (2 : ℕ))
  rw [Complex.normSq_apply, show (z ^ (2 : ℕ)).re = z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ) by
    rw [pow_two, Complex.mul_re]
    ring]
  calc
    6889 * (z.im ^ (2 : ℕ) * (z.re * z.re + z.im * z.im) / z.re) =
        (6889 * (z.im ^ (2 : ℕ) * (z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ)))) / z.re := by ring
    _ <= (85 * (z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ)) / z.re :=
      (div_le_div_iff_of_pos_right ha).2 hpoly
    _ = 85 * (z.re * ((z.re ^ (2 : ℕ) - z.im ^ (2 : ℕ)) / z.re) ^ (2 : ℕ)) := by
      field_simp [ha.ne']

/-! ## Complete coefficient-of-variation gate -/

/-- Zeroth-mass-normalized longitudinal response second energy. -/
def xiShiftedResponseSecondEnergy (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 0).re *
    ∑' q : XiZeroCopy,
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)

theorem xiShiftedResponseSecondEnergy_nonneg {y : ℝ} (hy : 0 < y) :
    0 <= xiShiftedResponseSecondEnergy y := by
  rw [xiShiftedResponseSecondEnergy]
  exact mul_nonneg
    (re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)).le
    (tsum_nonneg fun q => mul_nonneg
      (xiShiftedResponseMass_pos hy q).le (sq_nonneg _))

/-- Complete shifted charge inherits the sharp atomwise `85 / 6889` ratio. -/
theorem sixThousandEightHundredEightyNine_mul_xiShiftedTransverseCharge_le
    {y : ℝ} (hy : 0 < y) :
    6889 * xiShiftedTransverseCharge y <=
      85 * xiShiftedResponseSecondEnergy y := by
  have hsum :
      6889 * (∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q) <=
        85 * (∑' q : XiZeroCopy,
          xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact
      ((summable_xiShiftedTransverseChargeDensity hy).mul_left 6889).tsum_le_tsum
        (fun q =>
          sixThousandEightHundredEightyNine_mul_xiShiftedTransverseChargeDensity_le hy q)
        ((summable_xiShiftedResponseMass_mul_slope_sq hy).mul_left 85)
  rw [xiShiftedTransverseCharge, xiShiftedResponseSecondEnergy]
  have hmass : 0 <= (xiShiftedReciprocalMoment y 0).re :=
    (re_xiShiftedReciprocalMoment_pos hy (n := 0) (by norm_num)).le
  nlinarith [mul_nonneg hmass
    (sub_nonneg.mpr hsum)]

/-- **Exact coefficient-of-variation discharge.**  If complete response dispersion is at least
`85 / 6889` of the longitudinal second response energy, then it dominates all transverse charge
and the first shifted Hankel minor is nonnegative. -/
theorem xiShiftedHankelMinor_nonneg_of_dispersion_floor
    {y : ℝ} (hy : 0 < y)
    (hfloor :
      85 * xiShiftedResponseSecondEnergy y <=
        6889 * xiShiftedResponseHilbertDispersion y) :
    0 <=
      (xiShiftedReciprocalMoment y 0).re *
          (xiShiftedReciprocalMoment y 2).re -
        (xiShiftedReciprocalMoment y 1).re ^ (2 : ℕ) := by
  have hcharge :=
    sixThousandEightHundredEightyNine_mul_xiShiftedTransverseCharge_le hy
  have hdom : xiShiftedTransverseCharge y <=
      xiShiftedResponseHilbertDispersion y := by
    nlinarith
  rw [xiShiftedHankelMinor_eq_hilbertDispersion_sub_transverseCharge hy]
  exact sub_nonneg.mpr hdom

/-- Safe-shift source specialization of the quantitative coefficient-of-variation gate. -/
theorem primeArchSafeShiftHankelMinor_nonneg_of_dispersion_floor
    (hfloor :
      85 * xiShiftedResponseSecondEnergy 1 <=
        6889 * xiShiftedResponseHilbertDispersion 1) :
    0 <=
      (primeArchShiftedReciprocalMoment 1 0).re *
          (primeArchShiftedReciprocalMoment 1 2).re -
        (primeArchShiftedReciprocalMoment 1 1).re ^ (2 : ℕ) := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 0,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 1,
    ← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
      (y := 1) (by norm_num) (by norm_num) 2]
  exact xiShiftedHankelMinor_nonneg_of_dispersion_floor (by norm_num) hfloor

end

end RHTower
