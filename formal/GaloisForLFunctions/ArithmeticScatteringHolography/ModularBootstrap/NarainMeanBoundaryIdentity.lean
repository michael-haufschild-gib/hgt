import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageBoundaryRate
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryTail

/-!
# Exact Fourier normalization of the averaged scalar remainder

The physical remainder is the boundary Fourier integral multiplied by
its square-root height factor and the inverse Mellin constant.
-/

open Complex RHTower MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Normalizing the actual inverse Mellin integral leaves its boundary Fourier integral. -/
theorem narainMean_boundary_normalized_identity (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, Complex.exp (((-Real.log y : ℝ) : ℂ) * ((t : ℂ) * I)) *
          narainMellinMean Y Z ((t : ℂ) * I) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [mellinInv, Complex.real_smul]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, narainMeanMellin]
  have hs : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1 / 2 = (t : ℂ) * I := by
    push_cast
    ring
  rw [hs, ← mul_assoc, ← Complex.cpow_add _ _ hyc]
  have he : (1 / 2 : ℂ) + -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = -((t : ℂ) * I) := by
    push_cast
    ring
  rw [he, Complex.cpow_def_of_ne_zero hyc, ← Complex.ofReal_log hy.le]
  push_cast
  congr 2
  ring

/-- The normalized inverse Mellin transform uses the usual inverse Fourier convention. -/
theorem narainMean_boundary_fourier_identity (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (1 / 2 : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y =
      FourierTransform.fourierInv
        (fun t : ℝ => narainMellinMean Y Z (2 * Real.pi * t * I)) (-Real.log y) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [mellinInv_eq_fourierInv (1 / 2) (narainMeanMellin Y Z) hy, smul_eq_mul,
    ← mul_assoc, ← Complex.cpow_add _ _ hyc]
  have he : (1 / 2 : ℂ) + (-(1 / 2 : ℝ) : ℂ) = 0 := by norm_num
  rw [he, Complex.cpow_zero, one_mul]
  have hf : (fun t : ℝ => narainMeanMellin Y Z (((1 / 2 : ℝ) : ℂ) + 2 * Real.pi * t * I)) =
      fun t : ℝ => narainMellinMean Y Z (2 * Real.pi * t * I) := by
    funext t
    unfold narainMeanMellin
    congr 1
    push_cast
    ring
  rw [hf]

/-- The actual source remainder is the square-root factor times its boundary Fourier integral. -/
theorem narainScalarHeatAverage_remainder_eq_boundary (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z =
        (y : ℂ) ^ (1 / 2 : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Complex.exp (((-Real.log y : ℝ) : ℂ) * ((t : ℂ) * I)) *
            narainMellinMean Y Z ((t : ℂ) * I) := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsq : (y : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ) = y := by
    rw [← Complex.cpow_add _ _ hyc]
    norm_num
  calc
    _ = (y : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y :=
      narainScalarHeatAverage_boundary_identity Y Z hy
    _ = ((y : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ (1 / 2 : ℂ)) *
        mellinInv (1 / 2) (narainMeanMellin Y Z) y := by rw [hsq]
    _ = _ := by rw [mul_assoc, narainMean_boundary_normalized_identity Y Z hy, ← mul_assoc]

/-- The physical scalar remainder has exactly the square-root prefactor of the boundary integral. -/
theorem norm_narainScalarHeatAverage_remainder_eq (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ =
        y ^ ((1 : ℝ) / 2) / (2 * Real.pi) *
          ‖∫ t : ℝ, Complex.exp (((-Real.log y : ℝ) : ℂ) * ((t : ℂ) * I)) *
            narainMellinMean Y Z ((t : ℂ) * I)‖ := by
  rw [narainScalarHeatAverage_remainder_eq_boundary Y Z hy, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num,
    Complex.norm_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  ring

#print axioms narainMean_boundary_fourier_identity
#print axioms narainScalarHeatAverage_remainder_eq_boundary
#print axioms narainMean_boundary_normalized_identity
#print axioms norm_narainScalarHeatAverage_remainder_eq
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
