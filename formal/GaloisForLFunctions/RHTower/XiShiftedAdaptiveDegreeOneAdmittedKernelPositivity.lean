import GaloisForLFunctions.RHTower.XiShiftedAdaptiveMixedGammaKernelPointwiseNoGo
import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniContactFourthCumulant

/-!
# Admission restores positivity for the canonical degree-one adaptive kernel

Full affine-amplitude plane is Lorentzian, so arbitrary monic positive-root amplitudes can make
literal adaptive mixed Gamma kernel negative. Canonical shifted-Xi degree-one amplitude occupies
a narrower cone. Unconditional endpoint-height contraction gives

`w² m₁(w²) / m₀(w²) < 4/85`,  `0 < w < 1`.

Together with exact coefficientwise reverse-Bessel inequality
`48 B₃(z) < 85 B₄(z)`, `z ≥ 0`, this makes actual Gamma-averaged common kernel of
`X - m₁/m₀` strictly positive at every Euler source point.
-/

open Complex Matrix MeasureTheory Set Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact reverse-Bessel separation needed by safe degree-one admission cone. -/
theorem fortyEight_mul_reverseBesselPoly_three_lt_eightyFive_mul_four
    {z : ℝ} (hz : 0 ≤ z) :
  48 * reverseBesselPoly 3 z < 85 * reverseBesselPoly 4 z := by
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]
  have hz2 : 0 ≤ z ^ 2 := pow_nonneg hz 2
  have hz3 : 0 ≤ z ^ 3 := pow_nonneg hz 3
  have hz4 : 0 ≤ z ^ 4 := pow_nonneg hz 4
  nlinarith

/-- Canonical degree-one shifted-Xi null root is positive on every positive mass ray. -/
theorem xiShiftedDegreeOneNullRoot_pos
    {y : ℝ} (hy : 0 < y) :
    0 < xiShiftedDegreeOneNullRoot y := by
  exact div_pos
    (re_xiShiftedReciprocalMoment_pos hy (by norm_num))
    (xiShiftedCassiniResponse_pos hy)

/-- Coefficient vector of canonical monic degree-one candidate. -/
def xiShiftedDegreeOneNullVector (y : ℝ) : Fin 2 → ℝ :=
  ![-xiShiftedDegreeOneNullRoot y, 1]

/-- Canonical vector's raw coefficient polynomial is exactly `X-m₁/m₀`. -/
theorem finiteHankelNullPolynomial_xiShiftedDegreeOneNullVector_eq (y : ℝ) :
    HTGeometry.finiteHankelNullPolynomial (xiShiftedDegreeOneNullVector y) =
      xiShiftedDegreeOneNullPolynomial y := by
  rw [HTGeometry.finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_two]
  simp [xiShiftedDegreeOneNullVector, xiShiftedDegreeOneNullPolynomial,
    monomial_one_right_eq_X_pow]
  rw [sub_eq_add_neg]
  exact add_comm _ _

/-- Monic normalization leaves canonical degree-one coefficient polynomial unchanged. -/
theorem finiteHankelNullMonicPolynomial_xiShiftedDegreeOneNullVector_eq (y : ℝ) :
    HTGeometry.finiteHankelNullMonicPolynomial (xiShiftedDegreeOneNullVector y) =
      xiShiftedDegreeOneNullPolynomial y := by
  rw [HTGeometry.finiteHankelNullMonicPolynomial,
    finiteHankelNullPolynomial_xiShiftedDegreeOneNullVector_eq]
  simp [xiShiftedDegreeOneNullPolynomial]

/-- **Actual first-face incidence.**  At a flat first minor, canonical coefficient vector is
literally a kernel vector of shifted-Xi Hankel block. -/
theorem xiShiftedMomentHankelMatrix_two_mulVec_degreeOneNullVector_eq_zero_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    xiShiftedMomentHankelMatrix y 2 *ᵥ xiShiftedDegreeOneNullVector y = 0 := by
  have hm0 : xiShiftedCassiniResponse y ≠ 0 :=
    (xiShiftedCassiniResponse_pos hy).ne'
  have hm0' : (xiShiftedReciprocalMoment y 0).re ≠ 0 := by
    simpa [xiShiftedCassiniResponse] using hm0
  have hcontact :
      xiShiftedCassiniResponse y * (xiShiftedReciprocalMoment y 2).re =
        (xiShiftedReciprocalMoment y 1).re ^ 2 := by
    rw [xiShiftedDegreeOneHankelMinor] at hflat
    linarith
  funext i
  fin_cases i
  · simp [xiShiftedMomentHankelMatrix,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, xiShiftedDegreeOneNullVector,
      xiShiftedDegreeOneNullRoot, xiShiftedCassiniResponse]
    field_simp [hm0']
    ring
  · simp [xiShiftedMomentHankelMatrix,
      GaloisForLFunctions.HTGeometry.finiteHankelMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, xiShiftedDegreeOneNullVector,
      xiShiftedDegreeOneNullRoot]
    field_simp [hm0]
    nlinarith

/-- **Global endpoint-height contraction.**  Squared-node real-part separation confines the first
two shifted moments at every positive mass, without the auxiliary hypothesis `y < 1`. -/
theorem four_y_add_eightyOne_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
    {y : ℝ} (hy : 0 < y) :
    (4 * y + 81) * (xiShiftedReciprocalMoment y 1).re <
      4 * (xiShiftedReciprocalMoment y 0).re := by
  have hatom : ∀ q : XiZeroCopy,
      (4 * y + 81) * (xiShiftedReciprocalSquare y q ^ 2).re <
        4 * (xiShiftedReciprocalSquare y q).re := by
    intro q
    let A : ℝ := y + (xiSquaredNode q).re
    let B : ℝ := (xiSquaredNode q).im
    have hnode : 81 / 4 < (xiSquaredNode q).re := by
      rw [xiSquaredNode_re]
      have hv := xiZeroCopy_fortyOne_div_two_lt_im_sq q
      have hu := xi_divisor_support_centered_re_sq_lt_quarter q.1
      linarith
    have hA : (4 * y + 81) / 4 < A := by
      dsimp only [A]
      linarith
    have hA0 : 0 < A := by linarith
    have hden : 0 < A ^ 2 + B ^ 2 := by
      nlinarith [sq_pos_of_pos hA0, sq_nonneg B]
    have hcoord : (y : ℂ) + xiSquaredNode q =
        (A : ℂ) + (B : ℂ) * I := by
      apply Complex.ext <;> simp [A, B]
    rw [xiShiftedReciprocalSquare_eq_inv hy.le]
    change (4 * y + 81) * ((((y : ℂ) + xiSquaredNode q)⁻¹ ^ 2).re) <
      4 * (((y : ℂ) + xiSquaredNode q)⁻¹).re
    rw [hcoord, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, mul_one, add_zero, zero_add]
    have hgap : (4 * y + 81) * A < 4 * (A ^ 2 + B ^ 2) := by
      nlinarith [sq_nonneg B]
    field_simp
    nlinarith [hden, sq_nonneg (A ^ 2 + B ^ 2)]
  have hsum1C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (0 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy.le 0
  have hsum2C : Summable (fun q : XiZeroCopy =>
      xiShiftedReciprocalSquare y q ^ (1 + 1)) :=
    summable_xiShiftedReciprocalSquare_pow hy.le 1
  have hsum1 : Summable (fun q : XiZeroCopy =>
      4 * (xiShiftedReciprocalSquare y q).re) := by
    simpa using (Complex.reCLM.summable hsum1C).mul_left 4
  have hsum2 : Summable (fun q : XiZeroCopy =>
      (4 * y + 81) * (xiShiftedReciprocalSquare y q ^ 2).re) := by
    simpa using
      (Complex.reCLM.summable hsum2C).mul_left (4 * y + 81)
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  have hlt := hsum2.tsum_lt_tsum (i := q0)
    (fun q => (hatom q).le) (hatom q0) hsum1
  change (4 * y + 81) * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (1 + 1)).re <
    4 * (∑' q : XiZeroCopy,
      xiShiftedReciprocalSquare y q ^ (0 + 1)).re
  rw [Complex.re_tsum hsum2C, Complex.re_tsum hsum1C]
  simpa only [tsum_mul_left, zero_add, pow_one] using hlt

/-- Global dimensionless canonical-root bound forced by squared-node geometry. -/
theorem xiShiftedDegreeOneNullRoot_scaled_lt_heightEnvelope
    {y : ℝ} (hy : 0 < y) :
    y * xiShiftedDegreeOneNullRoot y < 4 * y / (4 * y + 81) := by
  have hm0 : 0 < xiShiftedCassiniResponse y := xiShiftedCassiniResponse_pos hy
  have hden : 0 < 4 * y + 81 := by linarith
  have hcontract :=
    four_y_add_eightyOne_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero hy
  rw [xiShiftedDegreeOneNullRoot]
  rw [show y * ((xiShiftedReciprocalMoment y 1).re /
      xiShiftedCassiniResponse y) =
        (y * (xiShiftedReciprocalMoment y 1).re) /
          xiShiftedCassiniResponse y by ring]
  rw [div_lt_div_iff₀ hm0 hden]
  change (4 * y + 81) * (xiShiftedReciprocalMoment y 1).re <
    4 * xiShiftedCassiniResponse y at hcontract
  have hmul := mul_lt_mul_of_pos_left hcontract hy
  nlinarith

/-- Exact reverse-Bessel order separation on the whole physical logarithmic ray. -/
theorem seven_mul_reverseBesselPoly_three_le_reverseBesselPoly_four
    {z : ℝ} (hz : 0 ≤ z) :
    7 * reverseBesselPoly 3 z ≤ reverseBesselPoly 4 z := by
  norm_num [reverseBesselPoly, Finset.sum_range_succ, squaredRadialJetWeight]
  have hquad : 0 ≤ z ^ 2 + 3 * z + 3 := by positivity
  nlinarith [mul_nonneg (sq_nonneg z) hquad]

/-- Universal positive chamber for monic affine amplitudes, expressed in dimensionless root
coordinate `w²r`. -/
theorem xiShiftedAdaptiveMixedGammaKernel_affineMonic_pos_of_scaledRoot_lt
    {w r x : ℝ} (hw : 0 < w) (hr : 0 < r)
    (hscaledRoot : w ^ 2 * r < 7 / 12) (hx : 1 ≤ x) :
    0 < xiShiftedAdaptiveMixedGammaKernel w
      (xiShiftedAdaptiveAffineAmplitude (-r) 1) x := by
  let t := w ^ 2 * r
  have ht : 0 < t := mul_pos (sq_pos_of_pos hw) hr
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw.le (Real.log_nonneg hx)
  have hB2 : 0 < reverseBesselPoly 2 (w * Real.log x) :=
    reverseBesselPoly_pos 2 hz
  have hB3 : 0 < reverseBesselPoly 3 (w * Real.log x) :=
    reverseBesselPoly_pos 3 hz
  have horder :=
    seven_mul_reverseBesselPoly_three_le_reverseBesselPoly_four hz
  have hscaled :
      12 * t * reverseBesselPoly 3 (w * Real.log x) <
        7 * reverseBesselPoly 3 (w * Real.log x) := by
    have h12 : 12 * t < 7 := by nlinarith
    exact mul_lt_mul_of_pos_right h12 hB3
  have hresidual :
      0 < reverseBesselPoly 4 (w * Real.log x) -
        12 * t * reverseBesselPoly 3 (w * Real.log x) := by
    linarith
  have hfirst :
      0 ≤ 24 * t ^ 2 * reverseBesselPoly 2 (w * Real.log x) := by positivity
  have hbracket :
      0 < 24 * (-r) ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) +
          12 * (-r) * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
          reverseBesselPoly 4 (w * Real.log x) := by
    have hrewrite :
        24 * (-r) ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) +
            12 * (-r) * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
            reverseBesselPoly 4 (w * Real.log x) =
          24 * t ^ 2 * reverseBesselPoly 2 (w * Real.log x) +
            (reverseBesselPoly 4 (w * Real.log x) -
              12 * t * reverseBesselPoly 3 (w * Real.log x)) := by
      dsimp only [t]
      ring
    rw [hrewrite]
    exact add_pos_of_nonneg_of_pos hfirst hresidual
  rw [xiShiftedAdaptiveMixedGammaKernel_affineAmplitude_eq hw (by norm_num)]
  norm_num only [one_pow, mul_one]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hprefactor : 0 < x ^ (-(1 / 2 + w)) / (96 * w ^ 9) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (mul_pos (by norm_num) (pow_pos hw 9))
  exact mul_pos hprefactor (by simpa only [one_mul] using hbracket)

/-- Endpoint-height gap confines dimensionless canonical degree-one root to strict safe interval
`(0,4/85)` throughout open theta strip. -/
theorem xiShiftedDegreeOneNullRoot_scaled_lt_four_div_eightyFive
    {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2) < 4 / 85 := by
  have hy0 : 0 < w ^ 2 := sq_pos_of_pos hw0
  have hy1 : w ^ 2 < 1 := by nlinarith
  have hbound :=
    eightyFive_mul_y_mul_re_xiShiftedReciprocalMoment_one_lt_four_mul_zero
      hy0 hy1
  have hm0 : 0 < xiShiftedCassiniResponse (w ^ 2) :=
    xiShiftedCassiniResponse_pos hy0
  have hscaled :
      85 * (w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2)) < 4 := by
    calc
      85 * (w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2)) =
          (85 * w ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 1).re) /
            xiShiftedCassiniResponse (w ^ 2) := by
              rw [xiShiftedDegreeOneNullRoot]
              ring
      _ < 4 := (div_lt_iff₀ hm0).2 (by
        change 85 * w ^ 2 * (xiShiftedReciprocalMoment (w ^ 2) 1).re <
          4 * xiShiftedCassiniResponse (w ^ 2)
        exact hbound)
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 85)).2 (by
    simpa [mul_comm] using hscaled)

/-- Before either source formation is aggregated, literal mixed Gamma kernel selected by
shifted-Xi first-face amplitude is strictly positive on whole Euler source ray. -/
theorem xiShiftedAdaptiveMixedGammaKernel_degreeOneNullPolynomial_pos
    {w x : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hx : 1 ≤ x) :
    0 < xiShiftedAdaptiveMixedGammaKernel w
      (xiShiftedDegreeOneNullPolynomial (w ^ 2)) x := by
  let r := xiShiftedDegreeOneNullRoot (w ^ 2)
  let t := w ^ 2 * r
  have hy0 : 0 < w ^ 2 := sq_pos_of_pos hw0
  have hr : 0 < r := xiShiftedDegreeOneNullRoot_pos hy0
  have ht : 0 < t := mul_pos (sq_pos_of_pos hw0) hr
  have htmax : t < 4 / 85 := by
    exact xiShiftedDegreeOneNullRoot_scaled_lt_four_div_eightyFive hw0 hw1
  have hz : 0 ≤ w * Real.log x := mul_nonneg hw0.le (Real.log_nonneg hx)
  have hB2 : 0 < reverseBesselPoly 2 (w * Real.log x) :=
    reverseBesselPoly_pos 2 hz
  have hB3 : 0 < reverseBesselPoly 3 (w * Real.log x) :=
    reverseBesselPoly_pos 3 hz
  have hBessel :=
    fortyEight_mul_reverseBesselPoly_three_lt_eightyFive_mul_four hz
  have hscaled :
      12 * t * reverseBesselPoly 3 (w * Real.log x) <
        (48 / 85) * reverseBesselPoly 3 (w * Real.log x) := by
    have h12 : 12 * t < 48 / 85 := by nlinarith
    exact mul_lt_mul_of_pos_right h12 hB3
  have hBessel' :
      (48 / 85) * reverseBesselPoly 3 (w * Real.log x) <
        reverseBesselPoly 4 (w * Real.log x) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 85)]
    simpa [mul_comm] using hBessel
  have hresidual :
      0 < reverseBesselPoly 4 (w * Real.log x) -
        12 * t * reverseBesselPoly 3 (w * Real.log x) := by
    linarith
  have hbracket :
      0 < 24 * r ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) -
          12 * r * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
          reverseBesselPoly 4 (w * Real.log x) := by
    have hfirst :
        0 ≤ 24 * t ^ 2 * reverseBesselPoly 2 (w * Real.log x) := by positivity
    have hrewrite :
        24 * r ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) -
            12 * r * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
            reverseBesselPoly 4 (w * Real.log x) =
          24 * t ^ 2 * reverseBesselPoly 2 (w * Real.log x) +
            (reverseBesselPoly 4 (w * Real.log x) -
              12 * t * reverseBesselPoly 3 (w * Real.log x)) := by
      dsimp only [t]
      ring
    rw [hrewrite]
    exact add_pos_of_nonneg_of_pos hfirst hresidual
  have hamp :
      xiShiftedDegreeOneNullPolynomial (w ^ 2) =
        xiShiftedAdaptiveAffineAmplitude (-r) 1 := by
    simp only [xiShiftedDegreeOneNullPolynomial,
      xiShiftedAdaptiveAffineAmplitude, r, map_one, one_mul]
    rw [sub_eq_add_neg, map_neg]
    exact add_comm _ _
  rw [hamp, xiShiftedAdaptiveMixedGammaKernel_affineAmplitude_eq hw0 (by norm_num)]
  norm_num only [one_pow, mul_one]
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hprefactor : 0 < x ^ (-(1 / 2 + w)) / (96 * w ^ 9) :=
    div_pos (Real.rpow_pos_of_pos hxpos _) (mul_pos (by norm_num) (pow_pos hw0 9))
  have hbracket' :
      0 < 24 * (-r) ^ 2 * w ^ 4 * reverseBesselPoly 2 (w * Real.log x) +
          12 * (-r) * w ^ 2 * reverseBesselPoly 3 (w * Real.log x) +
          reverseBesselPoly 4 (w * Real.log x) := by
    convert hbracket using 1
    ring
  exact mul_pos hprefactor (by simpa only [one_mul] using hbracket')

/-- **Full prime--Gamma-window admission theorem.**  Canonical degree-one shifted-Xi amplitude
stays in the positive common-kernel chamber throughout the entire source contact window. -/
theorem xiShiftedAdaptiveMixedGammaKernel_degreeOneNullPolynomial_pos_on_primeGammaWindow
    {w x : ℝ} (hw : 0 < w) (hwmax : w ^ 2 < 41 / 2) (hx : 1 ≤ x) :
    0 < xiShiftedAdaptiveMixedGammaKernel w
      (xiShiftedDegreeOneNullPolynomial (w ^ 2)) x := by
  let y := w ^ 2
  let r := xiShiftedDegreeOneNullRoot y
  have hy : 0 < y := sq_pos_of_pos hw
  have hr : 0 < r := xiShiftedDegreeOneNullRoot_pos hy
  have htEnvelope :
      y * r < 4 * y / (4 * y + 81) :=
    xiShiftedDegreeOneNullRoot_scaled_lt_heightEnvelope hy
  have hden : 0 < 4 * y + 81 := by linarith
  have hEnvelopeSafe : 4 * y / (4 * y + 81) < 7 / 12 := by
    rw [div_lt_iff₀ hden]
    dsimp only [y] at hwmax ⊢
    nlinarith
  have hscaled : w ^ 2 * r < 7 / 12 := by
    exact lt_trans htEnvelope hEnvelopeSafe
  have hamp :
      xiShiftedDegreeOneNullPolynomial (w ^ 2) =
        xiShiftedAdaptiveAffineAmplitude (-r) 1 := by
    simp only [xiShiftedDegreeOneNullPolynomial,
      xiShiftedAdaptiveAffineAmplitude, r, y, map_one, one_mul]
    rw [sub_eq_add_neg, map_neg]
    exact add_comm _ _
  rw [hamp]
  exact xiShiftedAdaptiveMixedGammaKernel_affineMonic_pos_of_scaledRoot_lt
    hw hr hscaled hx

/-- Route-window form used by mass-shifted spectral-face producer. -/
theorem xiShiftedAdaptiveMixedGammaKernel_degreeOneNullPolynomial_pos_on_routeWindow
    {w x : ℝ} (hw0 : 1 / 2 < w) (hw1 : w < 1) (hx : 1 ≤ x) :
    0 < xiShiftedAdaptiveMixedGammaKernel w
      (xiShiftedDegreeOneNullPolynomial (w ^ 2)) x :=
  xiShiftedAdaptiveMixedGammaKernel_degreeOneNullPolynomial_pos (by linarith) hw1 hx

end

end RHTower
