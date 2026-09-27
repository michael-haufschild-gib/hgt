import GaloisForLFunctions.RHTower.XiScaledEvenGaussianEnergy
import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalError

/-!
# Full Xi phase debt in the complete Gaussian polynomial norm

Coordinate-weighted translation error and reciprocal-square divisor summability
bound every zero copy, including all multiplicities. The polynomial is evaluated
as a whole throughout; no coefficient cross term is removed.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The complete imaginary-square debt at the actual complex Xi coordinates. -/
def xiScaledEvenGaussianPhaseDebt (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}) : ℝ :=
  2 * ∑' q : XiZeroCopy, (xiScaledEvenGaussianAmplitude P r q).im ^ 2

/-- The degree-only defect at the full unconditional Xi strip width. -/
def xiGaussianFullPhaseBudget (d : ℕ) (r : {r : ℝ // 0 < r}) : ℝ :=
  4 * (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) / (r : ℝ) ^ 2 *
    gaussianCoordinateVerticalDefect d ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩ ^ 2

theorem summable_xiScaledEvenGaussianAmplitude_im_sq (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : XiZeroCopy => (xiScaledEvenGaussianAmplitude P r q).im ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => ?_) (summable_xiScaledEvenGaussianAmplitude_norm_sq P r)
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [sq_nonneg (xiScaledEvenGaussianAmplitude P r q).re]

/-- Every actual zero has a reciprocal-square error majorant in the whole polynomial norm. -/
theorem xiScaledEvenGaussian_error_sq_le (P : Polynomial ℝ) (r : {r : ℝ // 0 < r})
    (q : XiZeroCopy) :
    ‖xiScaledEvenGaussianAmplitude P r q -
        polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2 ≤
      (2 * gaussianCoordinateVerticalDefect (2 * P.natDegree)
          ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩ ^ 2 / (r : ℝ) ^ 2 *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2) *
          (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let Q := evenSquarePolynomial P
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  let M : ℝ := ‖(polyGaussSchwartz Q).toLp 2 (volume : Measure ℝ)‖
  let B : ℝ := gaussianCoordinateVerticalDefect Q.natDegree R
  let e : ℂ := xiScaledEvenGaussianAmplitude P r q -
    polyGaussSchwartz Q ((r : ℝ) * (xiSpectralPoint q).re)
  have hr : 0 < (r : ℝ) := r.property
  have him : -(1 / 2 : ℝ) ≤ (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im ≤ 1 / 2 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    have he : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [he]
    constructor <;> linarith only [hs.1, hs.2]
  let δ : Set.Icc (-(R : ℝ)) R := ⟨(r : ℝ) * (xiSpectralPoint q).im, by
    constructor
    · change -((r : ℝ) / 2) ≤ (r : ℝ) * (xiSpectralPoint q).im
      nlinarith only [mul_le_mul_of_nonneg_left him.1 hr.le]
    · change (r : ℝ) * (xiSpectralPoint q).im ≤ (r : ℝ) / 2
      nlinarith only [mul_le_mul_of_nonneg_left him.2 hr.le]⟩
  have he : |(r : ℝ) * (xiSpectralPoint q).re| * ‖e‖ ≤ B * M := by
    have h := abs_mul_norm_entirePolynomialGaussian_vertical_sub_le Q R
      ((r : ℝ) * (xiSpectralPoint q).re) δ
    simpa only [entirePolynomialGaussian, Q, δ, ← xiScaledEvenGaussianAmplitude_vertical] using h
  have he2 := pow_le_pow_left₀ (by positivity) he 2
  rw [mul_pow, sq_abs, mul_pow, mul_pow] at he2
  have hsector : ‖xiSpectralPoint q‖ ^ 2 ≤ 2 * (xiSpectralPoint q).re ^ 2 := by
    have hs := xiSpectralPoint_normSq_lt_two_mul_sq_re q
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two, Complex.mul_re] at hs ⊢
    nlinarith only [hs, sq_nonneg (xiSpectralPoint q).im]
  have hs := mul_le_mul_of_nonneg_right hsector
    (mul_nonneg (sq_nonneg (r : ℝ)) (sq_nonneg ‖e‖))
  have hN : 0 < ‖xiSpectralPoint q‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)) _
  have hb : ‖e‖ ^ 2 ≤ 2 * B ^ 2 * M ^ 2 / ((r : ℝ) ^ 2 * ‖xiSpectralPoint q‖ ^ 2) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hr _) hN)).mpr
    nlinarith only [he2, hs]
  dsimp only [B, M, Q, R, e] at hb
  rw [natDegree_evenSquarePolynomial] at hb
  convert hb using 1; ring

/-- The full vertical error series is summable, without selecting a subset of zeros. -/
theorem summable_xiScaledEvenGaussian_error_sq (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    Summable (fun q : XiZeroCopy => ‖xiScaledEvenGaussianAmplitude P r q -
      polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (xiScaledEvenGaussian_error_sq_le P r)
    (xiSpectralPoint_inv_sq_summable.mul_left _)

/-- Independent full-divisor debt bound; its norm retains every polynomial cross term. -/
theorem xiScaledEvenGaussianPhaseDebt_le (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}) :
    xiScaledEvenGaussianPhaseDebt P r ≤ xiGaussianFullPhaseBudget (2 * P.natDegree) r *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hp (q : XiZeroCopy) : (xiScaledEvenGaussianAmplitude P r q).im ^ 2 ≤
      ‖xiScaledEvenGaussianAmplitude P r q -
        polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)‖ ^ 2 := by
    have hi : (xiScaledEvenGaussianAmplitude P r q -
        polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)).im =
      (xiScaledEvenGaussianAmplitude P r q).im := by
      simp [polyGaussSchwartz_apply]
    rw [Complex.sq_norm, Complex.normSq_apply, hi]
    nlinarith only [sq_nonneg (xiScaledEvenGaussianAmplitude P r q -
      polyGaussSchwartz (evenSquarePolynomial P) ((r : ℝ) * (xiSpectralPoint q).re)).re]
  have hsum := Summable.tsum_le_tsum
    (fun q => (hp q).trans (xiScaledEvenGaussian_error_sq_le P r q))
    (summable_xiScaledEvenGaussianAmplitude_im_sq P r)
    (xiSpectralPoint_inv_sq_summable.mul_left
      (2 * gaussianCoordinateVerticalDefect (2 * P.natDegree)
          ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩ ^ 2 / (r : ℝ) ^ 2 *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2))
  rw [tsum_mul_left] at hsum
  have ht := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2)
  dsimp only [xiScaledEvenGaussianPhaseDebt, xiGaussianFullPhaseBudget]
  convert ht using 1
  · rfl
  · ring

/-- The existing actual polynomial heat trace is exactly full energy minus full phase debt. -/
theorem xiScaledEvenGaussian_trace_eq_energy_sub_debt (P : Polynomial ℝ)
    (r : {r : ℝ // 0 < r}) :
    xiPolynomialGaussianHeatTraceReal (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (2 * π * (r : ℝ) ^ 2) =
      xiScaledEvenGaussianEnergy P r - xiScaledEvenGaussianPhaseDebt P r := by
  have ht : 0 < 2 * π * (r : ℝ) ^ 2 :=
    mul_pos (mul_pos (by positivity) Real.pi_pos) (pow_pos r.property _)
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace,
    Complex.re_tsum (summable_xiPolynomialGaussianHeatTerm ht _)]
  have hterm (q : XiZeroCopy) :
      (xiPolynomialGaussianHeatTerm (P.comp (Polynomial.C ((r : ℝ) ^ 2) * Polynomial.X))
        (2 * π * (r : ℝ) ^ 2) q).re =
      ‖xiScaledEvenGaussianAmplitude P r q‖ ^ 2 - 2 * (xiScaledEvenGaussianAmplitude P r q).im ^ 2 := by
    rw [← xiScaledEvenGaussianAmplitude_sq, Complex.sq_norm, Complex.normSq_apply,
      pow_two, Complex.mul_re]
    ring
  simp_rw [hterm]
  rw [Summable.tsum_sub (summable_xiScaledEvenGaussianAmplitude_norm_sq P r)
    ((summable_xiScaledEvenGaussianAmplitude_im_sq P r).mul_left 2), tsum_mul_left]
  rfl

end RHTower
