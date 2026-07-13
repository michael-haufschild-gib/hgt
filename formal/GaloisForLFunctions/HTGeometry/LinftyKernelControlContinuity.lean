import GaloisForLFunctions.HTGeometry.LinftyDensityControl

/-!
# Operator-norm continuity of bounded-density controls in the kernel

The `L∞` Bochner control is not only continuous in the density variable.  As a function of its
`L¹` kernel it is itself a continuous linear map into the operator-norm space of controls.  Thus
an `L¹`-continuous family of finite packet kernels produces an operator-norm-continuous family of
bounded-density control maps, exactly the topology used by compact uniform finite probes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {α V H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The continuous linear assignment sending an `L¹` vector kernel to its `L∞` density-control
operator. -/
noncomputable def linftyLpKernelControl
    (μ : Measure α) :
    Lp V 1 μ →L[ℝ] (Lp ℝ ∞ μ →L[ℝ] V) :=
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)).lpPairing μ ∞ 1).flip

@[simp]
theorem linftyLpKernelControl_apply
    (μ : Measure α) (K : Lp V 1 μ) :
    linftyLpKernelControl μ K = linftyLpPairingRight μ K :=
  rfl

/-- An `L¹`-continuous kernel family gives an operator-norm-continuous `L∞` control family. -/
theorem continuous_linftyLpPairingRight_of_continuous_kernel
    [TopologicalSpace H] (μ : Measure α) (K : H → Lp V 1 μ)
    (hK : Continuous K) :
    Continuous (fun h => linftyLpPairingRight μ (K h)) := by
  simpa only [← linftyLpKernelControl_apply] using
    (linftyLpKernelControl μ).continuous.comp hK

/-- Pointwise kernels may be used directly once their canonical `L¹` classes vary continuously. -/
theorem continuous_linftyBochnerControl_of_continuous_toLp
    [TopologicalSpace H] (μ : Measure α)
    (K : H → α → V) (hK : ∀ h, MemLp (K h) 1 μ)
    (hKtoLp : Continuous (fun h => (hK h).toLp (K h))) :
    Continuous (fun h => linftyBochnerControl μ (K h) (hK h)) := by
  simpa only [linftyBochnerControl] using
    continuous_linftyLpPairingRight_of_continuous_kernel
      μ (fun h => (hK h).toLp (K h)) hKtoLp

end

end GaloisForLFunctions.HTGeometry
