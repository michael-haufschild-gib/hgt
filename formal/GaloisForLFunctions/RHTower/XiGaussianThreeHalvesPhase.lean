import GaloisForLFunctions.RHTower.XiGaussianDebtDomination
import GaloisForLFunctions.RHTower.XiHeatQuarterPowerDebt
import GaloisForLFunctions.HTGeometry.ThreeHalvesWeightedInterpolation

/-!
# Fractional summation of the complete Xi Gaussian phase debt

Interpolating the two pointwise error bounds uses the actual reciprocal
three-halves divisor mass. The interpolation scale is free, and no polynomial
coefficient or cross term is discarded.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section
namespace RHTower

/-- The unweighted endpoint, with the linear strip-radius factor exposed. -/
theorem xiScaledEvenGaussian_error_sq_le_pointSlope (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    ‖xiScaledEvenGaussianAmplitude P r q -
        polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2 ≤
      (r : ℝ) ^ 2 / 4 * (gaussianStripSamplingFactor (2 * P.natDegree) 1 *
        gaussianVerticalDefectSlope (2 * P.natDegree) ((r : ℝ) / 2)) ^ 2 *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hr := r.property
  let Q := evenSquarePolynomial P
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, by positivity⟩
  have him : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    have he : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [he, abs_le]
    constructor <;> linarith only [hs.1, hs.2]
  let δ : Set.Icc (-(R : ℝ)) R := ⟨(r : ℝ) * (xiSpectralPoint q).im, by
    apply abs_le.mp
    change |(r : ℝ) * (xiSpectralPoint q).im| ≤ (r : ℝ) / 2
    rw [abs_mul, abs_of_pos r.property]
    nlinarith only [mul_le_mul_of_nonneg_left him r.property.le]⟩
  have hp := norm_entirePolynomialGaussian_vertical_sub_le Q R
    ((r : ℝ) * (xiSpectralPoint q).re) δ
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (verticalPolynomialGaussianDefect_le_radius_mul_slope Q.natDegree R)
      (gaussianStripSamplingFactor_nonneg Q.natDegree 1))
    (norm_nonneg ((polyGaussSchwartz Q).toLp 2 (volume : Measure ℝ)))
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hp.trans hs) 2
  simp only [entirePolynomialGaussian, Q, δ, ← xiScaledEvenGaussianAmplitude_vertical,
    natDegree_evenSquarePolynomial] at hh
  refine hh.trans_eq ?_
  change (gaussianStripSamplingFactor (2 * P.natDegree) 1 *
    ((r : ℝ) / 2 * gaussianVerticalDefectSlope (2 * P.natDegree) ((r : ℝ) / 2)) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖) ^ 2 = _
  ring

/-- The coordinate-square endpoint after cancelling its two radius factors. -/
theorem xiScaledEvenGaussian_error_sq_mul_norm_sq_le_slope (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ ^ 2 *
      ‖xiScaledEvenGaussianAmplitude P r q -
        polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2 ≤
      gaussianCoordinateVerticalSlope (2 * P.natDegree) ((r : ℝ) / 2) ^ 2 / 2 *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hr := r.property
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, by positivity⟩
  have hs := pow_le_pow_left₀ (gaussianCoordinateVerticalDefect_nonneg (2 * P.natDegree) R)
    (gaussianCoordinateVerticalDefect_le_radius_mul_slope (2 * P.natDegree) R) 2
  have hp := mul_le_mul_of_nonneg_left (xiScaledEvenGaussian_error_sq_le P r q)
    (sq_nonneg ‖xiSpectralPoint q‖)
  have hn : ‖xiSpectralPoint q‖ ≠ 0 := norm_ne_zero_iff.mpr (xiSpectralPoint_ne_zero q)
  have heq : ‖xiSpectralPoint q‖ ^ 2 *
      ((2 * gaussianCoordinateVerticalDefect (2 * P.natDegree) R ^ 2 / (r : ℝ) ^ 2 *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2) *
          (1 / ‖xiSpectralPoint q‖ ^ 2)) =
      (2 / (r : ℝ) ^ 2) * gaussianCoordinateVerticalDefect (2 * P.natDegree) R ^ 2 *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    field_simp
  change _ ≤ ‖xiSpectralPoint q‖ ^ 2 * ((2 * _ / (r : ℝ) ^ 2 * _) * _) at hp
  rw [heq] at hp
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 / (r : ℝ) ^ 2))
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  refine hp.trans (hb.trans_eq ?_)
  change (2 / (r : ℝ) ^ 2) *
    ((r : ℝ) / 2 * gaussianCoordinateVerticalSlope (2 * P.natDegree) ((r : ℝ) / 2)) ^ 2 *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 = _
  field_simp [hr.ne']

/-- Whole-polynomial phase budget with an independently adjustable interpolation scale. -/
def xiGaussianThreeHalvesPhaseBudget (d : ℕ) (r L : ℝ) : ℝ :=
  xiHeatThreeHalvesMass / (2 * Real.sqrt L) *
    (r ^ 2 * L ^ 2 * (gaussianStripSamplingFactor d 1 *
        gaussianVerticalDefectSlope d (r / 2)) ^ 2 +
      2 * gaussianCoordinateVerticalSlope d (r / 2) ^ 2)

/-- The actual full-divisor debt obeys the fractional budget, for every positive scale. -/
theorem xiScaledEvenGaussianPhaseDebt_le_threeHalves (P : Polynomial ℝ)
    (r L : {r : ℝ // 0 < r}) :
    xiScaledEvenGaussianPhaseDebt P r ≤
      xiGaussianThreeHalvesPhaseBudget (2 * P.natDegree) r L *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hL := L.property
  let M := ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖
  let B := ((r : ℝ) ^ 2 * (L : ℝ) ^ 2 *
      (gaussianStripSamplingFactor (2 * P.natDegree) 1 *
        gaussianVerticalDefectSlope (2 * P.natDegree) ((r : ℝ) / 2)) ^ 2 +
      2 * gaussianCoordinateVerticalSlope (2 * P.natDegree) ((r : ℝ) / 2) ^ 2) /
        (4 * Real.sqrt (L : ℝ)) * M ^ 2
  have hpoint (q : XiZeroCopy) :
      (xiScaledEvenGaussianAmplitude P r q).im ^ 2 ≤
        B * (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
    let e := xiScaledEvenGaussianAmplitude P r q -
      polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)
    have hp := xiScaledEvenGaussian_error_sq_le_pointSlope P r q
    have hc := xiScaledEvenGaussian_error_sq_mul_norm_sq_le_slope P r q
    have hw := mul_le_mul_of_nonneg_right
      (threeHalvesWeight_le_two_endpoint_weights ⟨‖xiSpectralPoint q‖, norm_nonneg _⟩ L)
      (sq_nonneg ‖e‖)
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg (L : ℝ))
    have he : (xiScaledEvenGaussianAmplitude P r q).im ^ 2 ≤ ‖e‖ ^ 2 := by
      have hi : e.im = (xiScaledEvenGaussianAmplitude P r q).im := by
        simp [e, polyGaussSchwartz_apply]
      rw [Complex.sq_norm, Complex.normSq_apply, hi]
      nlinarith only [sq_nonneg e.re]
    have hpos : 0 < ‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖ :=
      mul_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))
        (Real.sqrt_pos.mpr (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)))
    have hbound : ‖e‖ ^ 2 ≤ B / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖) := by
      rw [le_div_iff₀ hpos]
      dsimp only [B]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (L : ℝ))]
      change ‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖ * Real.sqrt (L : ℝ) *
        ‖e‖ ^ 2 ≤ ((L : ℝ) ^ 2 + ‖xiSpectralPoint q‖ ^ 2) * ‖e‖ ^ 2 at hw
      dsimp only [M, e] at hw ⊢
      nlinarith only [hw, hh, hc]
    simpa only [div_eq_mul_inv, one_mul] using he.trans hbound
  have hs := Summable.tsum_le_tsum hpoint
    (summable_xiScaledEvenGaussianAmplitude_im_sq P r)
    (xiSpectralPoint_inv_three_halves_summable.mul_left B)
  rw [tsum_mul_left] at hs
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2)
  change xiScaledEvenGaussianPhaseDebt P r ≤ _ at hh
  refine hh.trans_eq ?_
  dsimp only [xiGaussianThreeHalvesPhaseBudget, xiHeatThreeHalvesMass, B, M]
  ring

end RHTower
