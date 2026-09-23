import GaloisForLFunctions.RHTower.SuzukiSafeShiftTransverseChargeBudget
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniFourthCumulantCapNoGo

/-!
# Shifted degree-one phase-skewness reserve

The fourth shifted reciprocal response has an exact longitudinal/transverse splitting.  Besides
the existing transverse charge, it contains a new secondary phase tax

`κ_q = (Im(λ_q)^(2 : ℕ) / Re(λ_q)) χ_q`.

After centering at the response mean slope, degree-one terminal flux is exactly longitudinal
third response minus slope/charge covariance, twice the secondary tax, and the first-minor energy
gap.  On a flat face the gap vanishes.  The complete secondary tax is nonnegative and vanishes
exactly under RH.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Fourth-order phase tax carried by one shifted reciprocal Xi atom. -/
def xiShiftedSecondaryPhaseTaxDensity (y : ℝ) (q : XiZeroCopy) : ℝ :=
  (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) /
      xiShiftedResponseMass y q *
    xiShiftedTransverseChargeDensity y q

theorem xiShiftedSecondaryPhaseTaxDensity_nonneg
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    0 ≤ xiShiftedSecondaryPhaseTaxDensity y q := by
  exact mul_nonneg
    (div_nonneg (sq_nonneg _) (xiShiftedResponseMass_pos hy q).le)
    (xiShiftedTransverseChargeDensity_nonneg hy q)

/-- The fourth response coefficient splits into longitudinal slope cube, slope/charge coupling,
and the secondary phase tax. -/
theorem xiShiftedReciprocalSquare_fourth_re_eq_phaseSkewness
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    (xiShiftedReciprocalSquare y q ^ (4 : ℕ)).re =
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ) -
        3 * xiShiftedResponseSlope y q *
          xiShiftedTransverseChargeDensity y q -
        2 * xiShiftedSecondaryPhaseTaxDensity y q := by
  let z := xiShiftedReciprocalSquare y q
  have ha : z.re ≠ 0 := (xiShiftedResponseMass_pos hy q).ne'
  unfold xiShiftedResponseMass xiShiftedResponseSlope
    xiShiftedTransverseChargeDensity xiShiftedSecondaryPhaseTaxDensity
  change (z ^ (4 : ℕ)).re =
    z.re * ((z ^ (2 : ℕ)).re / z.re) ^ (3 : ℕ) -
      3 * ((z ^ (2 : ℕ)).re / z.re) *
        (z.im ^ (2 : ℕ) * Complex.normSq z / z.re) -
      2 * (z.im ^ (2 : ℕ) / z.re *
        (z.im ^ (2 : ℕ) * Complex.normSq z / z.re))
  rw [show z ^ (4 : ℕ) = z * z * z * z by ring,
    show z ^ (2 : ℕ) = z * z by ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  field_simp [ha]
  ring

/-- Public fourth-order bound for the existing transverse charge density. -/
theorem xiShiftedTransverseChargeDensity_le_two_mul_norm_cube
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedTransverseChargeDensity y q ≤
      2 * ‖xiShiftedReciprocalSquare y q‖ ^ (3 : ℕ) := by
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < z.re := xiShiftedResponseMass_pos hy q
  have hb : z.im ^ (2 : ℕ) ≤ z.re ^ (2 : ℕ) :=
    (xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q).le
  have hnormSq : Complex.normSq z ≤ 2 * z.re ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    nlinarith
  have hprod :
      z.im ^ (2 : ℕ) * Complex.normSq z ≤ z.re ^ (2 : ℕ) * (2 * z.re ^ (2 : ℕ)) :=
    mul_le_mul hb hnormSq (Complex.normSq_nonneg z) (sq_nonneg _)
  have hdiv :
      z.im ^ (2 : ℕ) * Complex.normSq z / z.re ≤ 2 * z.re ^ (3 : ℕ) := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hrele : 2 * z.re ^ (3 : ℕ) ≤ 2 * ‖z‖ ^ (3 : ℕ) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ha.le (Complex.re_le_norm z) 3) (by positivity)
  change z.im ^ (2 : ℕ) * Complex.normSq z / z.re ≤ 2 * ‖z‖ ^ (3 : ℕ)
  exact hdiv.trans hrele

private theorem summable_norm_xiShiftedReciprocalSquare_fourth
    {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun q : XiZeroCopy => ‖xiShiftedReciprocalSquare y q‖ ^ (4 : ℕ)) := by
  simpa only [norm_pow] using
    (summable_xiShiftedReciprocalSquare_pow hy 3).norm

theorem summable_xiShiftedResponseMass_mul_slope_cube
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ)) := by
  apply Summable.of_norm_bounded
    (summable_norm_xiShiftedReciprocalSquare_fourth hy.le)
  intro q
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < xiShiftedResponseMass y q := xiShiftedResponseMass_pos hy q
  have hh : 0 < xiShiftedResponseSlope y q := xiShiftedResponseSlope_pos hy q
  have hale : xiShiftedResponseMass y q ≤ ‖z‖ := by
    exact Complex.re_le_norm z
  have hhle : xiShiftedResponseSlope y q ≤ ‖z‖ :=
    xiShiftedResponseSlope_le_norm hy q
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le (pow_nonneg hh.le 3))]
  exact (mul_le_mul hale (pow_le_pow_left₀ hh.le hhle 3)
      (pow_nonneg hh.le 3) (norm_nonneg z)).trans_eq (by ring)

theorem summable_xiShiftedResponseSlope_mul_transverseChargeDensity
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseSlope y q * xiShiftedTransverseChargeDensity y q) := by
  apply Summable.of_norm_bounded
    ((summable_norm_xiShiftedReciprocalSquare_fourth hy.le).mul_left 2)
  intro q
  let z := xiShiftedReciprocalSquare y q
  have hh : 0 < xiShiftedResponseSlope y q := xiShiftedResponseSlope_pos hy q
  have hc : 0 ≤ xiShiftedTransverseChargeDensity y q :=
    xiShiftedTransverseChargeDensity_nonneg hy q
  have hhle : xiShiftedResponseSlope y q ≤ ‖z‖ :=
    xiShiftedResponseSlope_le_norm hy q
  have hcle : xiShiftedTransverseChargeDensity y q ≤ 2 * ‖z‖ ^ (3 : ℕ) :=
    xiShiftedTransverseChargeDensity_le_two_mul_norm_cube hy q
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.le hc)]
  have hmul := mul_le_mul hhle hcle hc (norm_nonneg z)
  calc
    xiShiftedResponseSlope y q * xiShiftedTransverseChargeDensity y q
        ≤ ‖z‖ * (2 * ‖z‖ ^ (3 : ℕ)) := hmul
    _ = 2 * ‖z‖ ^ (4 : ℕ) := by ring

theorem summable_xiShiftedSecondaryPhaseTaxDensity
    {y : ℝ} (hy : 0 < y) :
    Summable (xiShiftedSecondaryPhaseTaxDensity y) := by
  apply Summable.of_norm_bounded
    ((summable_norm_xiShiftedReciprocalSquare_fourth hy.le).mul_left 2)
  intro q
  let z := xiShiftedReciprocalSquare y q
  have ha : 0 < xiShiftedResponseMass y q := xiShiftedResponseMass_pos hy q
  have hb : z.im ^ (2 : ℕ) < z.re ^ (2 : ℕ) :=
    xiShiftedReciprocalSquare_im_sq_lt_re_sq hy q
  have hphase : z.im ^ (2 : ℕ) / xiShiftedResponseMass y q ≤ ‖z‖ := by
    have ha' : 0 < z.re := by
      simpa only [z, xiShiftedResponseMass] using ha
    have hlt : z.im ^ (2 : ℕ) / z.re < z.re := by
      rw [div_lt_iff₀ ha']
      simpa only [pow_two] using hb
    exact hlt.le.trans (Complex.re_le_norm z)
  have hc : 0 ≤ xiShiftedTransverseChargeDensity y q :=
    xiShiftedTransverseChargeDensity_nonneg hy q
  have hcle : xiShiftedTransverseChargeDensity y q ≤ 2 * ‖z‖ ^ (3 : ℕ) :=
    xiShiftedTransverseChargeDensity_le_two_mul_norm_cube hy q
  rw [Real.norm_eq_abs,
    abs_of_nonneg (xiShiftedSecondaryPhaseTaxDensity_nonneg hy q)]
  unfold xiShiftedSecondaryPhaseTaxDensity
  have hmul := mul_le_mul hphase hcle hc (norm_nonneg z)
  calc
    z.im ^ (2 : ℕ) / xiShiftedResponseMass y q *
          xiShiftedTransverseChargeDensity y q
        ≤ ‖z‖ * (2 * ‖z‖ ^ (3 : ℕ)) := hmul
    _ = 2 * ‖z‖ ^ (4 : ℕ) := by ring

/-- Complete centered longitudinal third response. -/
def xiShiftedResponseCenteredThird (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    xiShiftedResponseMass y q *
      (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) ^ (3 : ℕ)

/-- Complete covariance between centered response slope and transverse charge. -/
def xiShiftedSlopeChargeCovariance (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) *
      xiShiftedTransverseChargeDensity y q

/-- Complete secondary phase tax. -/
def xiShiftedSecondaryPhaseTax (y : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiShiftedSecondaryPhaseTaxDensity y q

/-- Centered longitudinal dispersion minus transverse charge, before zeroth-mass normalization. -/
def xiShiftedResponseEnergyGap (y : ℝ) : ℝ :=
  (∑' q : XiZeroCopy,
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) ^ (2 : ℕ)) -
    ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q

theorem summable_xiShiftedResponseCenteredThird
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) ^ (3 : ℕ)) := by
  let r := xiShiftedResponseMeanSlope y
  have h0 := summable_xiShiftedResponseMass hy.le
  have h1 := summable_xiShiftedResponseMass_mul_slope hy
  have h2 := summable_xiShiftedResponseMass_mul_slope_sq hy
  have h3 := summable_xiShiftedResponseMass_mul_slope_cube hy
  have hlinear : Summable (fun q : XiZeroCopy =>
      (-3 * r) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ))) :=
    h2.mul_left (-3 * r)
  have hquadratic : Summable (fun q : XiZeroCopy =>
      (3 * r ^ (2 : ℕ)) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q)) :=
    h1.mul_left (3 * r ^ (2 : ℕ))
  have hconstant : Summable (fun q : XiZeroCopy =>
      (-r ^ (3 : ℕ)) * xiShiftedResponseMass y q) :=
    h0.mul_left (-r ^ (3 : ℕ))
  have hsum := ((h3.add hlinear).add hquadratic).add hconstant
  apply hsum.congr
  intro q
  dsimp only [r]
  ring

theorem summable_xiShiftedSlopeChargeCovariance
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) *
        xiShiftedTransverseChargeDensity y q) := by
  have h1 := summable_xiShiftedResponseSlope_mul_transverseChargeDensity hy
  have h0 := summable_xiShiftedTransverseChargeDensity hy
  have hconstant : Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMeanSlope y * xiShiftedTransverseChargeDensity y q) :=
    h0.mul_left (xiShiftedResponseMeanSlope y)
  apply (h1.sub hconstant).congr
  intro q
  ring

theorem summable_xiShiftedResponseMass_mul_centeredSlope_sq
    {y : ℝ} (hy : 0 < y) :
    Summable (fun q : XiZeroCopy =>
      xiShiftedResponseMass y q *
        (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) ^ (2 : ℕ)) := by
  let r := xiShiftedResponseMeanSlope y
  have h0 := summable_xiShiftedResponseMass hy.le
  have h1 := summable_xiShiftedResponseMass_mul_slope hy
  have h2 := summable_xiShiftedResponseMass_mul_slope_sq hy
  have hlinear : Summable (fun q : XiZeroCopy =>
      (-2 * r) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q)) :=
    h1.mul_left (-2 * r)
  have hconstant : Summable (fun q : XiZeroCopy =>
      r ^ (2 : ℕ) * xiShiftedResponseMass y q) :=
    h0.mul_left (r ^ (2 : ℕ))
  have hsum := (h2.add hlinear).add hconstant
  apply hsum.congr
  intro q
  dsimp only [r]
  ring

theorem xiShiftedResponseCenteredThird_eq_raw
    {y : ℝ} (hy : 0 < y) :
    xiShiftedResponseCenteredThird y =
      (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ)) -
      3 * xiShiftedResponseMeanSlope y *
        (∑' q : XiZeroCopy,
          xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) +
      3 * xiShiftedResponseMeanSlope y ^ (2 : ℕ) *
        (∑' q : XiZeroCopy,
          xiShiftedResponseMass y q * xiShiftedResponseSlope y q) -
      xiShiftedResponseMeanSlope y ^ (3 : ℕ) *
        (∑' q : XiZeroCopy, xiShiftedResponseMass y q) := by
  let r := xiShiftedResponseMeanSlope y
  have h0 := summable_xiShiftedResponseMass hy.le
  have h1 := summable_xiShiftedResponseMass_mul_slope hy
  have h2 := summable_xiShiftedResponseMass_mul_slope_sq hy
  have h3 := summable_xiShiftedResponseMass_mul_slope_cube hy
  have hlinear : Summable (fun q : XiZeroCopy =>
      (-3 * r) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ))) :=
    h2.mul_left (-3 * r)
  have hquadratic : Summable (fun q : XiZeroCopy =>
      (3 * r ^ (2 : ℕ)) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q)) :=
    h1.mul_left (3 * r ^ (2 : ℕ))
  have hconstant : Summable (fun q : XiZeroCopy =>
      (-r ^ (3 : ℕ)) * xiShiftedResponseMass y q) :=
    h0.mul_left (-r ^ (3 : ℕ))
  rw [xiShiftedResponseCenteredThird]
  calc
    (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q *
          (xiShiftedResponseSlope y q - r) ^ (3 : ℕ)) =
        ∑' q : XiZeroCopy,
          (((xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ) +
              (-3 * r) * (xiShiftedResponseMass y q *
                xiShiftedResponseSlope y q ^ (2 : ℕ))) +
            (3 * r ^ (2 : ℕ)) * (xiShiftedResponseMass y q *
              xiShiftedResponseSlope y q)) +
            (-r ^ (3 : ℕ)) * xiShiftedResponseMass y q) := by
          apply tsum_congr
          intro q
          ring
    _ = _ := by
      rw [((h3.add hlinear).add hquadratic).tsum_add hconstant,
        (h3.add hlinear).tsum_add hquadratic,
        h3.tsum_add hlinear, tsum_mul_left, tsum_mul_left, tsum_mul_left]
      dsimp only [r]
      ring

theorem xiShiftedSlopeChargeCovariance_eq_raw
    {y : ℝ} (hy : 0 < y) :
    xiShiftedSlopeChargeCovariance y =
      (∑' q : XiZeroCopy,
        xiShiftedResponseSlope y q * xiShiftedTransverseChargeDensity y q) -
      xiShiftedResponseMeanSlope y *
        ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q := by
  have h1 := summable_xiShiftedResponseSlope_mul_transverseChargeDensity hy
  have h0 := summable_xiShiftedTransverseChargeDensity hy
  rw [xiShiftedSlopeChargeCovariance]
  calc
    (∑' q : XiZeroCopy,
        (xiShiftedResponseSlope y q - xiShiftedResponseMeanSlope y) *
          xiShiftedTransverseChargeDensity y q) =
        ∑' q : XiZeroCopy,
          (xiShiftedResponseSlope y q * xiShiftedTransverseChargeDensity y q -
            xiShiftedResponseMeanSlope y *
              xiShiftedTransverseChargeDensity y q) := by
          apply tsum_congr
          intro q
          ring
    _ = _ := by
      rw [h1.tsum_sub (h0.mul_left (xiShiftedResponseMeanSlope y)),
        tsum_mul_left]

theorem xiShiftedResponseEnergyGap_eq_raw
    {y : ℝ} (hy : 0 < y) :
    xiShiftedResponseEnergyGap y =
      (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ)) -
      2 * xiShiftedResponseMeanSlope y *
        (∑' q : XiZeroCopy,
          xiShiftedResponseMass y q * xiShiftedResponseSlope y q) +
      xiShiftedResponseMeanSlope y ^ (2 : ℕ) *
        (∑' q : XiZeroCopy, xiShiftedResponseMass y q) -
      ∑' q : XiZeroCopy, xiShiftedTransverseChargeDensity y q := by
  let r := xiShiftedResponseMeanSlope y
  have h0 := summable_xiShiftedResponseMass hy.le
  have h1 := summable_xiShiftedResponseMass_mul_slope hy
  have h2 := summable_xiShiftedResponseMass_mul_slope_sq hy
  have hlinear : Summable (fun q : XiZeroCopy =>
      (-2 * r) *
        (xiShiftedResponseMass y q * xiShiftedResponseSlope y q)) :=
    h1.mul_left (-2 * r)
  have hconstant : Summable (fun q : XiZeroCopy =>
      r ^ (2 : ℕ) * xiShiftedResponseMass y q) :=
    h0.mul_left (r ^ (2 : ℕ))
  rw [xiShiftedResponseEnergyGap]
  congr 1
  calc
    (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q *
          (xiShiftedResponseSlope y q - r) ^ (2 : ℕ)) =
        ∑' q : XiZeroCopy,
          ((xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (2 : ℕ) +
            (-2 * r) * (xiShiftedResponseMass y q *
              xiShiftedResponseSlope y q)) +
            r ^ (2 : ℕ) * xiShiftedResponseMass y q) := by
          apply tsum_congr
          intro q
          ring
    _ = _ := by
      rw [(h2.add hlinear).tsum_add hconstant,
        h2.tsum_add hlinear, tsum_mul_left, tsum_mul_left]
      dsimp only [r]
      ring

/-- Complete fourth-response identity. -/
theorem xiShiftedReciprocalMoment_three_re_eq_phaseSkewness
    {y : ℝ} (hy : 0 < y) :
    (xiShiftedReciprocalMoment y 3).re =
      (∑' q : XiZeroCopy,
        xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ)) -
      3 * (∑' q : XiZeroCopy,
        xiShiftedResponseSlope y q * xiShiftedTransverseChargeDensity y q) -
      2 * xiShiftedSecondaryPhaseTax y := by
  have h3 := summable_xiShiftedResponseMass_mul_slope_cube hy
  have hc := summable_xiShiftedResponseSlope_mul_transverseChargeDensity hy
  have hk := summable_xiShiftedSecondaryPhaseTaxDensity hy
  rw [xiShiftedReciprocalMoment,
    Complex.re_tsum (summable_xiShiftedReciprocalSquare_pow hy.le 3),
    xiShiftedSecondaryPhaseTax]
  calc
    (∑' q : XiZeroCopy, (xiShiftedReciprocalSquare y q ^ (3 + 1)).re) =
        ∑' q : XiZeroCopy,
          (xiShiftedResponseMass y q * xiShiftedResponseSlope y q ^ (3 : ℕ) -
            3 * (xiShiftedResponseSlope y q *
              xiShiftedTransverseChargeDensity y q) -
            2 * xiShiftedSecondaryPhaseTaxDensity y q) := by
          apply tsum_congr
          intro q
          simpa only [show 3 + 1 = 4 by omega, mul_assoc] using
            xiShiftedReciprocalSquare_fourth_re_eq_phaseSkewness hy q
    _ = _ := by
      rw [(h3.sub (hc.mul_left 3)).tsum_sub (hk.mul_left 2),
        h3.tsum_sub (hc.mul_left 3), tsum_mul_left, tsum_mul_left]

/-- The first shifted Hankel minor is zeroth mass times the centered response energy gap. -/
theorem xiShiftedDegreeOneHankelMinor_eq_mass_mul_responseEnergyGap
    {y : ℝ} (hy : 0 < y) :
    xiShiftedDegreeOneHankelMinor y =
      (xiShiftedReciprocalMoment y 0).re * xiShiftedResponseEnergyGap y := by
  have hm0 : 0 < (xiShiftedReciprocalMoment y 0).re :=
    re_xiShiftedReciprocalMoment_pos hy (by omega)
  rw [xiShiftedDegreeOneHankelMinor, xiShiftedCassiniResponse,
    xiShiftedResponseEnergyGap_eq_raw hy,
    tsum_xiShiftedResponseMass_eq_moment_re hy.le,
    tsum_xiShiftedResponseMass_mul_slope_eq_moment_re hy,
    ← tsum_xiShiftedResponseSlopeSq_sub_charge_eq_moment_re hy,
    xiShiftedResponseMeanSlope]
  field_simp [hm0.ne']
  ring

/-- **Exact phase-skewness reserve law.** -/
theorem xiShiftedDegreeOneNullRoot_eq_responseMeanSlope (y : ℝ) :
    xiShiftedDegreeOneNullRoot y = xiShiftedResponseMeanSlope y := by
  rfl

theorem xiShiftedDegreeOneTerminalFlux_eq_phaseSkewnessReserve
    {y : ℝ} (hy : 0 < y) :
    xiShiftedDegreeOneTerminalFlux y =
      xiShiftedResponseCenteredThird y -
        3 * xiShiftedSlopeChargeCovariance y -
        2 * xiShiftedSecondaryPhaseTax y +
        xiShiftedResponseMeanSlope y * xiShiftedResponseEnergyGap y := by
  rw [xiShiftedDegreeOneTerminalFlux_eq_moments,
    xiShiftedDegreeOneNullRoot_eq_responseMeanSlope,
    xiShiftedReciprocalMoment_three_re_eq_phaseSkewness hy,
    ← tsum_xiShiftedResponseSlopeSq_sub_charge_eq_moment_re hy]
  rw [
    xiShiftedResponseCenteredThird_eq_raw hy,
    xiShiftedSlopeChargeCovariance_eq_raw hy,
    xiShiftedResponseEnergyGap_eq_raw hy]
  rw [tsum_xiShiftedResponseMass_mul_slope_eq_moment_re hy]
  ring

/-- At a flat first face, no energy-gap term remains. -/
theorem xiShiftedDegreeOneTerminalFlux_eq_phaseSkewnessReserve_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    xiShiftedDegreeOneTerminalFlux y =
      xiShiftedResponseCenteredThird y -
        3 * xiShiftedSlopeChargeCovariance y -
        2 * xiShiftedSecondaryPhaseTax y := by
  have hm0 : 0 < (xiShiftedReciprocalMoment y 0).re :=
    re_xiShiftedReciprocalMoment_pos hy (by omega)
  have hgap : xiShiftedResponseEnergyGap y = 0 := by
    rw [xiShiftedDegreeOneHankelMinor_eq_mass_mul_responseEnergyGap hy] at hflat
    exact (mul_eq_zero.mp hflat).resolve_left hm0.ne'
  rw [xiShiftedDegreeOneTerminalFlux_eq_phaseSkewnessReserve hy, hgap, mul_zero,
    add_zero]

/-- Flat terminal orientation is exactly an arithmetic longitudinal reserve inequality. -/
theorem xiShiftedDegreeOneTerminalFlux_nonneg_iff_phaseSkewnessReserve_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    0 ≤ xiShiftedDegreeOneTerminalFlux y ↔
      3 * xiShiftedSlopeChargeCovariance y +
          2 * xiShiftedSecondaryPhaseTax y ≤
        xiShiftedResponseCenteredThird y := by
  rw [xiShiftedDegreeOneTerminalFlux_eq_phaseSkewnessReserve_of_flat hy hflat]
  constructor <;> intro h <;> linarith

theorem xiShiftedSecondaryPhaseTax_nonneg
    {y : ℝ} (hy : 0 < y) :
    0 ≤ xiShiftedSecondaryPhaseTax y := by
  rw [xiShiftedSecondaryPhaseTax]
  exact tsum_nonneg fun q => xiShiftedSecondaryPhaseTaxDensity_nonneg hy q

theorem xiShiftedSecondaryPhaseTaxDensity_eq_zero_iff
    {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    xiShiftedSecondaryPhaseTaxDensity y q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hm : xiShiftedResponseMass y q ≠ 0 :=
    (xiShiftedResponseMass_pos hy q).ne'
  rw [xiShiftedSecondaryPhaseTaxDensity]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hphase | hcharge
    · have himsq : (xiShiftedReciprocalSquare y q).im ^ (2 : ℕ) = 0 :=
        (div_eq_zero_iff.mp hphase).resolve_right hm
      exact (xiShiftedReciprocalSquare_im_eq_zero_iff_criticalLine hy q).mp
        (sq_eq_zero_iff.mp himsq)
    · exact (xiShiftedTransverseChargeDensity_eq_zero_iff hy q).mp hcharge
  · intro hline
    rw [(xiShiftedTransverseChargeDensity_eq_zero_iff hy q).mpr hline, mul_zero]

/-- **Higher-order RH radical.** The complete secondary phase tax vanishes exactly under RH. -/
theorem xiShiftedSecondaryPhaseTax_eq_zero_iff_riemannHypothesis
    {y : ℝ} (hy : 0 < y) :
    xiShiftedSecondaryPhaseTax y = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    have hsumZero :
        (∑' q : XiZeroCopy, xiShiftedSecondaryPhaseTaxDensity y q) = 0 := by
      simpa only [xiShiftedSecondaryPhaseTax] using hzero
    have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
      intro q
      have hle :=
        (summable_xiShiftedSecondaryPhaseTaxDensity hy).le_tsum q
          (fun r _ => xiShiftedSecondaryPhaseTaxDensity_nonneg hy r)
      have hqnonneg := xiShiftedSecondaryPhaseTaxDensity_nonneg hy q
      have hqzero : xiShiftedSecondaryPhaseTaxDensity y q = 0 := by
        apply le_antisymm
        · simpa only [hsumZero] using hle
        · exact hqnonneg
      exact (xiShiftedSecondaryPhaseTaxDensity_eq_zero_iff hy q).mp hqzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline q]
  · intro hRH
    rw [xiShiftedSecondaryPhaseTax]
    have hterm : ∀ q : XiZeroCopy,
        xiShiftedSecondaryPhaseTaxDensity y q = 0 := by
      intro q
      apply (xiShiftedSecondaryPhaseTaxDensity_eq_zero_iff hy q).mpr
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      have him := congrArg Complex.im ht
      simp [xiSpectralPoint] at him
      linarith
    simp_rw [hterm, tsum_zero]

end

end RHTower
