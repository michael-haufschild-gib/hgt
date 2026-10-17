import GaloisForLFunctions.HTGeometry.LevyLaplaceKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Holomorphic jump exponents, including infinite activity, from finite control measures. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal
noncomputable section
namespace GaloisForLFunctions.HTGeometry

def levyLaplaceJump (η : Measure ℝ≥0) (z : ℂ) : ℂ :=
  ∫ h, levyLaplaceKernel z h ∂η

variable (η : Measure ℝ≥0) [IsFiniteMeasure η]

theorem integrable_levyLaplaceKernel {z : ℂ} (hz : 0 ≤ z.re) :
    Integrable (levyLaplaceKernel z) η := by
  exact (integrable_const (2 + ‖z‖)).mono'
    (measurable_levyLaplaceKernel z).aestronglyMeasurable
    (Eventually.of_forall fun h => norm_levyLaplaceKernel_le hz h)

theorem integrable_levyLaplaceKernelDeriv {z : ℂ} (hz : 0 < z.re) :
    Integrable (levyLaplaceKernelDeriv z) η := by
  exact (integrable_const (1 + 1 / z.re)).mono'
    (measurable_levyLaplaceKernelDeriv z).aestronglyMeasurable
    (Eventually.of_forall fun h => norm_levyLaplaceKernelDeriv_le hz le_rfl h)

theorem levyLaplaceJump_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (levyLaplaceJump η z).re := by
  have he : (∫ h, (levyLaplaceKernel z h).re ∂η) = (levyLaplaceJump η z).re :=
    integral_re (integrable_levyLaplaceKernel η hz)
  rw [← he]
  exact integral_nonneg fun h => levyLaplaceKernel_re_nonneg hz h

omit [IsFiniteMeasure η] in
@[simp] theorem levyLaplaceJump_zero : levyLaplaceJump η 0 = 0 := by
  simp [levyLaplaceJump]

theorem hasDerivAt_levyLaplaceJump {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (levyLaplaceJump η) (∫ h, levyLaplaceKernelDeriv z h ∂η) z := by
  have hδ : 0 < z.re / 2 := half_pos hz
  have hball (w : ℂ) (hw : w ∈ Metric.ball z (z.re / 2)) : z.re / 2 ≤ w.re := by
    have hn : ‖w - z‖ < z.re / 2 := by simpa [dist_eq_norm] using hw
    have hr := (abs_le.mp (Complex.abs_re_le_norm (w - z))).1
    simp only [Complex.sub_re] at hr
    linarith
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := η)
    (F := fun w h => levyLaplaceKernel w h)
    (F' := fun w h => levyLaplaceKernelDeriv w h)
    (bound := fun _ => 1 + 1 / (z.re / 2))
    (Metric.ball_mem_nhds z hδ)
    (Eventually.of_forall fun w => (measurable_levyLaplaceKernel w).aestronglyMeasurable)
    (integrable_levyLaplaceKernel η hz.le)
    (measurable_levyLaplaceKernelDeriv z).aestronglyMeasurable
    (Eventually.of_forall fun h w hw => norm_levyLaplaceKernelDeriv_le hδ (hball w hw) h)
    (integrable_const _)
    (Eventually.of_forall fun h w _ => hasDerivAt_levyLaplaceKernel w h)
  exact hd.2

theorem analyticOnNhd_levyLaplaceJump :
    AnalyticOnNhd ℂ (levyLaplaceJump η) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  exact (hasDerivAt_levyLaplaceJump η hz).differentiableAt.differentiableWithinAt

theorem levyLaplaceJump_add_measure (ξ : Measure ℝ≥0) [IsFiniteMeasure ξ]
    {z : ℂ} (hz : 0 ≤ z.re) :
    levyLaplaceJump (η + ξ) z = levyLaplaceJump η z + levyLaplaceJump ξ z := by
  exact integral_add_measure (integrable_levyLaplaceKernel η hz)
    (integrable_levyLaplaceKernel ξ hz)

end GaloisForLFunctions.HTGeometry
