import GaloisForLFunctions.RHTower.SoninSemilocalGammaDifferentialFrame
import GaloisForLFunctions.RHTower.SoninSemilocalGammaMeasureCharacteristic
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# All moments of the normalized archimedean Gamma density

The quarter-Gamma log kernel has integrable derivatives of every order.  The Fourier derivative
theorem therefore places every polynomially weighted Fourier transform in `L²`.  Cauchy--Schwarz
then gives every polynomial moment of the squared Gamma transform, and an exact rescaling gives
every moment of the normalized archimedean Gamma density.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped ENNReal FourierTransform

namespace RHTower

theorem memLp_two_fourier_iteratedDeriv_semilocalGammaQuarterKernel (n : ℕ) :
    MemLp (FourierTransform.fourier
      (iteratedDeriv n semilocalGammaQuarterKernel)) 2 volume := by
  apply memLp_two_fourier_of_integrable_of_norm_le
    (integrable_iteratedDeriv_semilocalGammaQuarterKernel n)
  intro x
  rw [iteratedDeriv_semilocalGammaQuarterKernel]
  exact norm_semilocalGammaDifferentialFrame_le _ x

theorem fourier_iteratedDeriv_semilocalGammaQuarterKernel (n : ℕ) :
    FourierTransform.fourier (iteratedDeriv n semilocalGammaQuarterKernel) =
      fun xi : ℝ =>
        ((2 * Real.pi * Complex.I * xi) ^ n) *
          FourierTransform.fourier semilocalGammaQuarterKernel xi := by
  simpa only [smul_eq_mul] using
    (Real.fourier_iteratedDeriv (N := (n : ℕ∞))
      (contDiff_semilocalGammaQuarterKernel.of_le (by simp))
      (fun k _hk => integrable_iteratedDeriv_semilocalGammaQuarterKernel k)
      (by simp))

theorem memLp_two_pow_mul_fourier_semilocalGammaQuarterKernel (n : ℕ) :
    MemLp (fun xi : ℝ =>
      ((xi : ℂ) ^ n) * FourierTransform.fourier semilocalGammaQuarterKernel xi)
      2 volume := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hscaled : MemLp (fun xi : ℝ =>
      (c * xi) ^ n * FourierTransform.fourier semilocalGammaQuarterKernel xi)
      2 volume := by
    have h := memLp_two_fourier_iteratedDeriv_semilocalGammaQuarterKernel n
    rw [fourier_iteratedDeriv_semilocalGammaQuarterKernel] at h
    simpa [c, mul_assoc] using h
  have hinv := hscaled.const_smul (c ^ n)⁻¹
  apply (memLp_congr_ae (Eventually.of_forall fun xi => ?_)).mpr hinv
  change (xi : ℂ) ^ n * FourierTransform.fourier semilocalGammaQuarterKernel xi =
    (c ^ n)⁻¹ *
      ((c * (xi : ℂ)) ^ n * FourierTransform.fourier semilocalGammaQuarterKernel xi)
  field_simp [hc]
  simp only [c, mul_pow]
  ring

theorem integrable_pow_mul_normSq_fourier_semilocalGammaQuarterKernel (n : ℕ) :
    Integrable (fun xi : ℝ =>
      (xi : ℂ) ^ n *
        (Complex.normSq
          (FourierTransform.fourier semilocalGammaQuarterKernel xi) : ℂ)) := by
  have hn := memLp_two_pow_mul_fourier_semilocalGammaQuarterKernel n
  have hzero : MemLp
      (FourierTransform.fourier semilocalGammaQuarterKernel) 2 volume := by
    simpa using memLp_two_pow_mul_fourier_semilocalGammaQuarterKernel 0
  have hprod := hn.integrable_mul hzero.star
  apply hprod.congr
  filter_upwards with xi
  simp only [Pi.mul_apply, Pi.star_apply]
  rw [Complex.star_def, mul_assoc, Complex.mul_conj]

theorem integrable_pow_mul_normSq_Gamma_quarter_frequency (n : ℕ) :
    Integrable (fun xi : ℝ =>
      (xi : ℂ) ^ n *
        (Complex.normSq
          (Complex.Gamma ((1 : ℝ) / 4 +
            (2 * Real.pi * xi) * Complex.I)) : ℂ)) := by
  apply (integrable_pow_mul_normSq_fourier_semilocalGammaQuarterKernel n).congr
  filter_upwards with xi
  rw [fourier_semilocalGammaQuarterKernel]

theorem integrable_pow_mul_semilocalArchimedeanGammaDensity_complex (n : ℕ) :
    Integrable (fun s : ℝ =>
      (s : ℂ) ^ n * (semilocalArchimedeanGammaDensity s : ℂ)) := by
  let B : ℝ := 4 * Real.pi
  have hB : B ≠ 0 := by
    dsimp [B]
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcomp :=
    (integrable_pow_mul_normSq_Gamma_quarter_frequency n).comp_mul_left'
      (inv_ne_zero hB)
  have hscaled := hcomp.const_mul
    ((((2 * Real.pi) ^ (-(3 : ℝ) / 2) * B ^ n : ℝ)) : ℂ)
  apply hscaled.congr
  filter_upwards with s
  have hfreq : 2 * Real.pi * (B⁻¹ * s) = s / 2 := by
    dsimp [B]
    field_simp [Real.pi_ne_zero]
    ring
  unfold semilocalArchimedeanGammaDensity
  push_cast
  have hfreqC := congrArg Complex.ofReal hfreq
  push_cast at hfreqC
  rw [hfreqC]
  have hBC : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  rw [mul_pow, inv_pow]
  field_simp [hBC]

theorem integrable_pow_mul_semilocalArchimedeanGammaDensity (n : ℕ) :
    Integrable (fun s : ℝ => s ^ n * semilocalArchimedeanGammaDensity s) := by
  have hcomplex :=
    (integrable_pow_mul_semilocalArchimedeanGammaDensity_complex n).re
  apply hcomplex.congr
  filter_upwards with s
  change ((s : ℂ) ^ n * (semilocalArchimedeanGammaDensity s : ℂ)).re =
    s ^ n * semilocalArchimedeanGammaDensity s
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem integrable_abs_pow_mul_semilocalArchimedeanGammaDensity (n : ℕ) :
    Integrable (fun s : ℝ => |s| ^ n * semilocalArchimedeanGammaDensity s) := by
  convert (integrable_pow_mul_semilocalArchimedeanGammaDensity n).norm using 1
  funext s
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (semilocalArchimedeanGammaDensity_nonneg s)]

noncomputable instance semilocalArchimedeanGammaMeasure_isFiniteMeasure :
    IsFiniteMeasure semilocalArchimedeanGammaMeasure := by
  unfold semilocalArchimedeanGammaMeasure
  have hfun :
      (fun s : ℝ => (semilocalArchimedeanGammaDensityNNReal s : ℝ≥0∞)) =
        fun s : ℝ => ENNReal.ofReal (semilocalArchimedeanGammaDensity s) := by
    funext s
    rw [ENNReal.ofReal_eq_coe_nnreal
      (semilocalArchimedeanGammaDensity_nonneg s)]
    rfl
  rw [hfun]
  exact isFiniteMeasure_withDensity_ofReal
    integrable_semilocalArchimedeanGammaDensity.hasFiniteIntegral

theorem integral_semilocalArchimedeanGammaDensity_eq_one :
    (∫ s : ℝ, semilocalArchimedeanGammaDensity s) = 1 := by
  have h := congrArg Complex.re
    (integral_cexp_mul_semilocalArchimedeanGammaDensity 0)
  have h' :
      ((∫ s : ℝ, (semilocalArchimedeanGammaDensity s : ℂ))).re = 1 := by
    simpa [semilocalArchimedeanCharacteristic] using h
  rw [integral_complex_ofReal] at h'
  exact h'

theorem memLp_id_semilocalArchimedeanGammaMeasure (n : ℕ) :
    MemLp id n semilocalArchimedeanGammaMeasure := by
  cases n with
  | zero =>
      norm_num only [Nat.cast_zero]
      rw [memLp_zero_iff_aestronglyMeasurable]
      fun_prop
  | succ n =>
      rw [← integrable_norm_rpow_iff (f := id)
        (by fun_prop) (by simp) (by simp)]
      rw [semilocalArchimedeanGammaMeasure,
        integrable_withDensity_iff_integrable_smul
          continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
      have h := integrable_abs_pow_mul_semilocalArchimedeanGammaDensity (n + 1)
      convert h using 1
      funext x
      simp only [id_eq, ENNReal.toReal_natCast, Real.norm_eq_abs,
        Real.rpow_natCast, NNReal.smul_def]
      change semilocalArchimedeanGammaDensity x * |x| ^ (n + 1) =
        |x| ^ (n + 1) * semilocalArchimedeanGammaDensity x
      ring

end RHTower
