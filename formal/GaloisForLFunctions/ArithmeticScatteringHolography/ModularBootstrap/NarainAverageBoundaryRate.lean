import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanContour
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.MellinBoundaryDecay

/-!
# The unconditional square-root boundary of the averaged Narain source

The exact remainder is the boundary inverse Mellin integral. Fourier decay in the
logarithmic variable makes its normalized value tend to zero at small height.
-/

open Complex RHTower Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The exact logarithmic remainder is the boundary inverse Mellin integral. -/
theorem narainScalarHeatAverage_boundary_identity (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z =
        (y : ℂ) * mellinInv (1 / 2) (narainMeanMellin Y Z) y := by
  have h := narainMeanMellin_contour_shift Y Z hy
  rw [mellinInv_narainMeanMellin Y Z hy, Complex.cpow_neg, Complex.cpow_one] at h
  have h' := congrArg (fun z : ℂ => (y : ℂ) * z) h
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne'), one_mul] at h'
  linear_combination h'

/-- The normalized actual remainder tends to zero at the square-root boundary. -/
theorem tendsto_narainScalarHeatAverage_boundary_remainder (Y Z : Height) :
    Tendsto (fun y : ℝ =>
      ‖(y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z‖ /
          y ^ ((1 : ℝ) / 2)) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_normalized_mellinInv_zero (1 / 2) (narainMeanMellin Y Z)).norm
  simp only [norm_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 < y := hy
  rw [narainScalarHeatAverage_boundary_identity Y Z hy0]
  simp only [norm_mul, Complex.norm_of_nonneg hy0.le,
    Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re]
  have hp : y ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hy0 _).ne'
  have hs : y ^ ((1 : ℝ) / 2) * y ^ ((1 : ℝ) / 2) = y := by
    rw [← Real.rpow_add hy0]
    norm_num
  apply (eq_div_iff hp).mpr
  linear_combination congrArg (fun r : ℝ => r * ‖mellinInv (1 / 2) (narainMeanMellin Y Z) y‖) hs

/-- The actual averaged scalar source has an unconditional little-o square-root remainder. -/
theorem narainScalarHeatAverage_boundary_rate (Y Z : Height) :
    (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)
      =o[𝓝[>] 0] (fun y : ℝ => y ^ ((1 : ℝ) / 2)) := by
  rw [← isLittleO_norm_left]
  apply (isLittleO_iff_tendsto' ?_).mpr (tendsto_narainScalarHeatAverage_boundary_remainder Y Z)
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hn : y ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  exact fun h => (hn h).elim

#print axioms narainScalarHeatAverage_boundary_identity
#print axioms narainScalarHeatAverage_boundary_rate
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
