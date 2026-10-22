import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadialDirichletGraph
import GaloisForLFunctions.HTGeometry.L2NegativeHalfLineExtension
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier

/-! The original Dirichlet graph has a zero extension with its actual L2 derivative. -/
open Complex Set Filter Topology MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
namespace RHTower.D4BMJointWave
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem zeroExtension_eq (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ))
    (hs : Function.support f ⊆ Iio 0) :
    negativeZeroExtension ((hf.restrict (Iio 0)).toLp f) = hf.toLp f := by
  apply Lp.ext
  have ha := (ae_restrict_iff' measurableSet_Iio).mp (hf.restrict (Iio 0)).coeFn_toLp
  filter_upwards [negativeZeroExtension_ae ((hf.restrict (Iio 0)).toLp f),hf.coeFn_toLp,ha]
    with t ht hf' ha
  rw [ht,hf']
  by_cases hi : t ∈ Iio (0:ℝ)
  · rw [negativeZeroExtensionFun,indicator_of_mem hi,ha hi]
  · have hz : f t = 0 := Function.notMem_support.mp (fun h => hi (hs h))
    simp [negativeZeroExtensionFun,hi,hz]

/-- The zero extension of the actual smooth core value is its original whole-line function. -/
theorem radialValue_zeroExtension (f : RadialCore) :
    negativeZeroExtension (radialValue f) =
      (f.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := (volume : Measure ℝ)) f.compact).toLp f.field :=
  zeroExtension_eq _ _ ((subset_tsupport _).trans f.support)

/-- The zero extension of the actual core derivative is the original whole-line derivative. -/
theorem radialDerivative_zeroExtension (f : RadialCore) :
    negativeZeroExtension (radialDerivative f) =
      ((f.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport
        (p := 2) (μ := (volume : Measure ℝ)) f.compact.deriv).toLp (deriv f.field) :=
  zeroExtension_eq _ _ ((subset_tsupport _).trans ((tsupport_deriv_subset (f := f.field)).trans f.support))

private def zeroDerivativeConstraint : RadialDerivativeSpace →L[ℂ] 𝓢'(ℝ,ℂ) :=
  (LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℝ,ℂ) (1:ℝ)).comp
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2).comp
      (negativeZeroExtension.comp (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 0)))-
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2).comp
      (negativeZeroExtension.comp (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 1))

private theorem zeroDerivativeConstraint_core (f : RadialCore) :
    zeroDerivativeConstraint (radialDirichletGraph f) = 0 := by
  change ∂_{(1:ℝ)} ((negativeZeroExtension (radialValue f) : FourierRealL2) : 𝓢'(ℝ,ℂ))-
    ((negativeZeroExtension (radialDerivative f) : FourierRealL2) : 𝓢'(ℝ,ℂ)) = 0
  rw [radialValue_zeroExtension,radialDerivative_zeroExtension]
  apply sub_eq_zero.mpr
  exact lineDerivOp_toTemperedDistribution_eq _ _
    (fun t => (f.smooth.differentiable (by simp)).differentiableAt.hasDerivAt)

/-- Completion preserves the actual distributional derivative of the zero extension; no endpoint delta is introduced. -/
theorem radialDirichlet_zeroExtension_derivative (v : radialDirichletDomain) :
    ∂_{(1:ℝ)} ((negativeZeroExtension ((v : RadialDerivativeSpace) 0) : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      ((negativeZeroExtension ((v : RadialDerivativeSpace) 1) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  have hs : radialDirichletDomain ≤ zeroDerivativeConstraint.toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨f,rfl⟩
      exact zeroDerivativeConstraint_core f
    · exact zeroDerivativeConstraint.isClosed_ker
  exact sub_eq_zero.mp (hs v.property)

end
end RHTower.D4BMJointWave
