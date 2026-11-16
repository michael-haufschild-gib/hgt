import GaloisForLFunctions.RHTower.SmoothAFELogGaussianMoment
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUntwistedSquarefreeSeriesIsHolomorphicInitially
import Mathlib.Analysis.MellinInversion

/-!
# Gaussian Mellin inversion for the arithmetic theta sum

The inverse Mellin transform of `exp(s²)` is
`exp(-(log x)²/4)/(2√π)`. Absolute ideal-zeta convergence on `Re s>1`
permits termwise integration of the signed squarefree theta series.
-/

noncomputable section
open MeasureTheory Complex
namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein

private theorem logGaussian_line_eq (c : ℝ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (-((c : ℂ) + t * I)) * Complex.exp (((c : ℂ) + t * I) ^ 2) =
      Complex.exp ((-1 : ℂ) * (t : ℂ) ^ 2 +
        (I * (2 * c - Real.log x)) * t + ((c : ℂ) ^ 2 - c * Real.log x)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 1
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem integrable_logGaussian_line (c : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ) ^ (-((c : ℂ) + t * I)) *
      Complex.exp (((c : ℂ) + t * I) ^ 2)) := by
  simp_rw [logGaussian_line_eq c hx]
  exact integrable_cexp_quadratic' (by norm_num : (-1 : ℂ).re < 0) _ _

/-- The inverse Mellin transform of `exp(s²)` is the normalized logarithmic Gaussian. -/
theorem integral_logGaussian_line (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
      (x : ℂ) ^ (-((c : ℂ) + t * I)) * Complex.exp (((c : ℂ) + t * I) ^ 2)) =
      (RHTower.smoothAFELogGaussian (Real.log x) : ℂ) := by
  simp_rw [logGaussian_line_eq c hx]
  rw [integral_cexp_quadratic (by norm_num : (-1 : ℂ).re < 0)]
  have hexp : ((c : ℂ) ^ 2 - c * Real.log x) -
      (I * (2 * c - Real.log x)) ^ 2 / (4 * (-1)) = -((Real.log x : ℂ) ^ 2) / 4 := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [hexp]
  have hroot : ((Real.pi : ℂ) / -(-1)) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    norm_num only [neg_neg, div_one]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [hroot, Complex.real_smul, RHTower.smoothAFELogGaussian]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
  have hsqrt : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hsqrt0 : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [← hsqrt]

/-- The actual squarefree theta sum with a normalized Gaussian in logarithmic scale. -/
def gaussianSmoothedUntwistedTheta (X : ℝ) : ℂ :=
  ∑' A : Ideal O, untwistedSquarefreeCoefficient A *
    (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ)

private def thetaGaussianLineTerm (c X : ℝ) (A : Ideal O) (t : ℝ) : ℂ :=
  let s : ℂ := (c : ℂ) + t * I
  (X : ℂ) ^ s * Complex.exp (s ^ 2) *
    (unramifiedNormWeight s A * untwistedSquarefreeCoefficient A)

private theorem thetaGaussian_integrable_majorant :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
  simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)

private theorem norm_thetaGaussianLineTerm_le (c : ℝ) {X : ℝ} (hX : 0 < X)
    (A : Ideal O) (t : ℝ) :
    ‖thetaGaussianLineTerm c X A t‖ ≤
      ‖unramifiedNormWeight (c : ℂ) A‖ *
        (X ^ c * Real.exp (c ^ 2)) * Real.exp (-(t ^ 2)) := by
  let s : ℂ := (c : ℂ) + t * I
  have hs : s.re = c := by simp [s]
  have hsq : (s ^ 2).re = c ^ 2 - t ^ 2 := by
    dsimp only [s]
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hw := unramifiedNormWeight_norm_mono c s hs.ge A
  change ‖(X : ℂ) ^ s * Complex.exp (s ^ 2) *
    (unramifiedNormWeight s A * untwistedSquarefreeCoefficient A)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    hs, Complex.norm_exp, hsq, Real.exp_sub]
  have he : (Real.exp (t ^ 2))⁻¹ = Real.exp (-(t ^ 2)) := (Real.exp_neg _).symm
  rw [div_eq_mul_inv, he]
  calc
    _ ≤ X ^ c * (Real.exp (c ^ 2) * Real.exp (-(t ^ 2))) *
        (‖unramifiedNormWeight (c : ℂ) A‖ * 1) := by
      gcongr
      exact norm_untwistedSquarefreeCoefficient_le A
    _ = _ := by ring

private theorem integrable_thetaGaussianLineTerm (c : ℝ) {X : ℝ} (hX : 0 < X)
    (A : Ideal O) : Integrable (thetaGaussianLineTerm c X A) := by
  refine Integrable.mono'
    (thetaGaussian_integrable_majorant.const_mul
      (‖unramifiedNormWeight (c : ℂ) A‖ * (X ^ c * Real.exp (c ^ 2)))) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hs : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
    exact (((hs.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (Complex.continuous_exp.comp (hs.pow 2))).mul
        (((unramifiedNormWeight_differentiable A).continuous.comp hs).mul continuous_const))
  · filter_upwards with t
    simpa only [one_mul] using norm_thetaGaussianLineTerm_le c hX A t

private theorem cpow_scale_identity (s : ℂ) {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    (X : ℂ) ^ s * (N : ℂ) ^ (-s) = ((N / X : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hX).ne'),
    ← Complex.ofReal_log hX.le, ← Complex.ofReal_log hN.le,
    ← Complex.ofReal_log (div_pos hN hX).le, Real.log_div hN.ne' hX.ne',
    Complex.ofReal_sub, ← Complex.exp_add]
  congr 1
  ring

private theorem integral_thetaGaussianLineTerm (c : ℝ) {X : ℝ} (hX : 0 < X)
    (A : Ideal O) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, thetaGaussianLineTerm c X A t) =
      untwistedSquarefreeCoefficient A *
        (RHTower.smoothAFELogGaussian (Real.log ((Ideal.absNorm A : ℝ) / X)) : ℂ) := by
  by_cases hA : primaryIdealGenerator A = 0
  · simp only [thetaGaussianLineTerm, unramifiedNormWeight_of_bad _ A hA,
      untwistedSquarefreeCoefficient_of_bad A hA, zero_mul, mul_zero, integral_zero, smul_zero]
  · have hN : 0 < (Ideal.absNorm A : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryIdealGenerator_ne_zero_ideal A hA)))
    have he (t : ℝ) : thetaGaussianLineTerm c X A t = untwistedSquarefreeCoefficient A *
        ((((Ideal.absNorm A : ℝ) / X : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
          Complex.exp (((c : ℂ) + t * I) ^ 2)) := by
      rw [thetaGaussianLineTerm, unramifiedNormWeight_of_good _ A hA,
        ← cpow_scale_identity _ hN hX]
      simp only [Complex.ofReal_natCast]
      ring
    simp_rw [he]
    rw [integral_const_mul, Complex.real_smul, mul_left_comm, ← Complex.real_smul,
      integral_logGaussian_line c (div_pos hN hX)]

/-- Absolute Mellin inversion identifies the Gaussian contour with the arithmetic theta sum. -/
theorem gaussianSmoothedUntwistedTheta_eq_integral (c : ℝ) (hc : 1 < c)
    {X : ℝ} (hX : 0 < X) :
    gaussianSmoothedUntwistedTheta X =
      (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
        (X : ℂ) ^ ((c : ℂ) + t * I) * Complex.exp (((c : ℂ) + t * I) ^ 2) *
          twistedSquarefreeSeries 1 ((c : ℂ) + t * I)) := by
  letI : Countable O := Eisenstein.Coordinates.coordinateEquiv.injective.countable
  letI : Countable (Ideal O) := cubicIdealGenerator_injective.countable
  let K : ℝ := (X ^ c * Real.exp (c ^ 2)) * ∫ t : ℝ, Real.exp (-(t ^ 2))
  have hsum : Summable (fun A : Ideal O => ∫ t : ℝ, ‖thetaGaussianLineTerm c X A t‖) := by
    refine Summable.of_nonneg_of_le (fun A => integral_nonneg fun t => norm_nonneg _) (fun A => ?_)
      ((unramifiedNormWeight_summable_norm (c : ℂ) (by simpa using hc)).mul_right K)
    calc
      _ ≤ ∫ t : ℝ, ‖unramifiedNormWeight (c : ℂ) A‖ *
          (X ^ c * Real.exp (c ^ 2)) * Real.exp (-(t ^ 2)) := by
        apply integral_mono_ae (integrable_thetaGaussianLineTerm c hX A).norm
          (thetaGaussian_integrable_majorant.const_mul _)
        filter_upwards with t
        exact norm_thetaGaussianLineTerm_le c hX A t
      _ = _ := by rw [integral_const_mul]; dsimp only [K]; ring
  have hi := (hasSum_integral_of_summable_integral_norm
    (fun A => integrable_thetaGaussianLineTerm c hX A) hsum).const_smul (1 / (2 * Real.pi) : ℝ)
  simp only [integral_thetaGaussianLineTerm c hX] at hi
  rw [gaussianSmoothedUntwistedTheta, hi.tsum_eq]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [thetaGaussianLineTerm, tsum_mul_left, twistedSquarefreeSeries_one_eq]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
