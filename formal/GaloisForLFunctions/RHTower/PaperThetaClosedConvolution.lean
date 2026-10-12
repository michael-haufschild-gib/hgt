import GaloisForLFunctions.RHTower.PaperThetaContinuousCircle
import GaloisForLFunctions.HTGeometry.PaperDirichletPeriodicPrimitive

/-! # Literal source coefficients on the closed quantile interval

Assigning the common seam trace preserves every source coefficient. Finite
summation then expresses the original full symmetric sums as convolution of
the closed quantile mode with the exact Dirichlet kernel.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

theorem sourceCoeff_eq_closedQuantile_integral
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (k : ℤ) :
    sourceCoeff z.val k = ∫ y in (0 : ℝ)..1,
      closedQuantileMode z.val y * Period.phase (-k : ℤ) y := by
  rw [← fourierCoeff_seamCorrectedCircleMode, fourierCoeff_eq_integral,
    ← Period.map_circle_volume]
  rw [integral_map
    (f := fun x : Torus => seamCorrectedCircleMode z.val x * fourier (-k) x)
    Period.measurable_circle.aemeasurable
    (((continuous_seamCorrectedCircleMode z).mul (fourier (-k)).continuous).aestronglyMeasurable)]
  rw [← Period.seg_eq_interval _ zero_le_one]
  change (∫ y in Ico (0 : ℝ) 1,
    seamCorrectedCircleMode z.val (Period.circle y) * fourier (-k) (Period.circle y)) = _
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with y hy
  rw [seamCorrectedCircleMode_eq_closedQuantileMode, Period.coord_circle_eq hy,
    Period.fourier_circle]

/-- Every original frequency and coefficient is retained in the closed-interval convolution. -/
theorem sourcePartialSum_eq_closed_convolution
    (z : {z : ℂ // z = 0 ∨ XiC z = 0}) (N : ℕ) (t : ℝ) :
    sourcePartialSum z.val N t = ∫ y in (0 : ℝ)..1,
      closedQuantileMode z.val y * Period.dirichlet N (t - y) := by
  have hi (k : ℤ) : IntervalIntegrable
      (fun y => closedQuantileMode z.val y * Period.phase (k : ℝ) (t - y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_closedQuantileMode z).mul
      ((Period.phase_cont k).comp (continuous_const.sub continuous_id)).continuousOn
  unfold sourcePartialSum
  simp_rw [sourceCoeff_eq_closedQuantile_integral z, ← intervalIntegral.integral_mul_const]
  have he (k : ℤ) (y : ℝ) :
      (closedQuantileMode z.val y * Period.phase (-k : ℤ) y) * Period.phase k t =
        closedQuantileMode z.val y * Period.phase k (t - y) := by
    rw [Period.phase_sub]
    push_cast
    ring
  simp_rw [he]
  rw [← intervalIntegral.integral_finsetSum (fun k _ => hi k)]
  apply intervalIntegral.integral_congr
  intro y _
  simp only [Period.dirichlet, Finset.mul_sum]

end RHTower.PaperThetaEndpoint
