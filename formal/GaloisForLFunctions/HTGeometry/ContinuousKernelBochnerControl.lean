import GaloisForLFunctions.HTGeometry.LinftyDensityControl
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Continuous scalar control of an integrable Banach-valued kernel

The existing bounded-density control restricts along the continuous-map
inclusion into L-infinity. No finite-dimensional assumption is needed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (μ : Measure K) [IsFiniteMeasure μ]

def continuousKernelBochnerControl (k : K → V) (hk : MemLp k 1 μ) : C(K, ℝ) →L[ℝ] V :=
  (linftyBochnerControl μ k hk).comp (ContinuousMap.toLp ∞ μ ℝ)

theorem continuousKernelBochnerControl_apply (k : K → V) (hk : MemLp k 1 μ)
    (f : C(K, ℝ)) :
    continuousKernelBochnerControl μ k hk f = ∫ x, f x • k x ∂μ := by
  rw [continuousKernelBochnerControl, ContinuousLinearMap.comp_apply, linftyBochnerControl_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := ∞) (μ := μ) (𝕜 := ℝ) f] with x hx
  rw [hx]

end GaloisForLFunctions.HTGeometry
