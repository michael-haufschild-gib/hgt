import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryMoments
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryIdentity
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageLogSaving

/-!
# The actual Narain source as a Fourier profile

Exact Mellin normalization identifies the physical remainder with its
Fourier profile. The arithmetic saving gives rapid decay on the negative ray.
-/

open Complex RHTower MeasureTheory Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The Fourier profile retains the exact inverse-Mellin normalization and frequency sign. -/
theorem narainMeanBoundaryFourier_eq_integral (Y Z : Height) (L : ℝ) :
    narainMeanBoundaryFourier Y Z L = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, Complex.exp ((-L : ℂ) * ((t : ℂ) * I)) *
        narainMellinMean Y Z ((t : ℂ) * I) := by
  have h := narainMean_boundary_normalized_identity Y Z (Real.exp_pos L)
  rw [narainMean_boundary_fourier_identity Y Z (Real.exp_pos L),
    Real.fourierInv_eq_fourier_neg, Real.log_exp, neg_neg] at h
  change FourierTransform.fourier
    (fun t : ℝ => narainMellinMean Y Z (2 * (Real.pi : ℂ) * (t : ℂ) * I)) L = _
  simpa only [Complex.ofReal_neg] using h

/-- The actual source remainder is exactly its Fourier profile at logarithmic height. -/
theorem narainScalarHeatAverage_remainder_eq_fourier (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z =
        (y : ℂ) ^ (1 / 2 : ℂ) * narainMeanBoundaryFourier Y Z (Real.log y) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsq : (y : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ) = y := by
    rw [← Complex.cpow_add _ _ hyc]
    norm_num
  have hf := narainMean_boundary_fourier_identity Y Z hy
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hf
  change (y : ℂ) ^ (1 / 2 : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y =
    narainMeanBoundaryFourier Y Z (Real.log y) at hf
  calc
    _ = (y : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y :=
      narainScalarHeatAverage_boundary_identity Y Z hy
    _ = ((y : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)) *
        mellinInv (1 / 2) (narainMeanMellin Y Z) y := by rw [hsq]
    _ = _ := by rw [mul_assoc, hf]

/-- The Fourier profile norm is the physical remainder divided by its square-root height. -/
theorem norm_narainMeanBoundaryFourier_log (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    ‖narainMeanBoundaryFourier Y Z (Real.log y)‖ =
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ /
          y ^ ((1 : ℝ) / 2) := by
  have h := congrArg norm (narainScalarHeatAverage_remainder_eq_fourier Y Z hy)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
    show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num] at h
  apply (eq_div_iff (Real.rpow_pos_of_pos hy _).ne').mpr
  exact (mul_comm _ _).trans h.symm

/-- Every polynomially weighted negative-frequency value tends to zero. -/
theorem tendsto_pow_mul_narainMeanBoundaryFourier_neg (Y Z : Height) (N : ℕ) :
    Tendsto (fun L : ℝ => L ^ N * ‖narainMeanBoundaryFourier Y Z (-L)‖) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hb⟩ := exists_narainMeanBoundary_vk_decay Y Z
  have hlim := (tendsto_pow_mul_exp_neg_vkWidth hc N).const_mul (C / (2 * Real.pi))
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hbound hL
  rw [Real.norm_of_nonneg (by positivity), narainMeanBoundaryFourier_eq_integral]
  simp only [Complex.ofReal_neg, neg_neg]
  rw [norm_mul, Complex.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  calc
    _ ≤ L ^ N * (1 / (2 * Real.pi) * (C * Real.exp (-(c * L * vkHadamardWidth L)))) := by gcongr
    _ = _ := by ring

#print axioms narainScalarHeatAverage_remainder_eq_fourier
#print axioms norm_narainMeanBoundaryFourier_log
#print axioms tendsto_pow_mul_narainMeanBoundaryFourier_neg
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
