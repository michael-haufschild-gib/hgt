import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadialDirichletZeroExtension
import GaloisForLFunctions.HTGeometry.RealSobolevDerivativeGain
import GaloisForLFunctions.HTGeometry.RealSobolevContinuousRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual zero endpoint traces for the completed original radial Dirichlet graph. -/
open Complex Set Filter Topology MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
namespace RHTower.D4BMJointWave
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The zero extension of an original radial Dirichlet value is an actual order-one Sobolev distribution. -/
theorem radialDirichlet_zeroExtension_sobolev (v : radialDirichletDomain) :
    MemSobolev 1 2 ((negativeZeroExtension ((v : RadialDerivativeSpace) 0) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  have hu : MemSobolev 0 2 ((negativeZeroExtension ((v : RadialDerivativeSpace) 0) : FourierRealL2) : 𝓢'(ℝ,ℂ)) :=
    memSobolev_zero_iff.mpr ⟨_,rfl⟩
  have hd : MemSobolev 0 2 (∂_{(1:ℝ)} ((negativeZeroExtension ((v : RadialDerivativeSpace) 0) : FourierRealL2) : 𝓢'(ℝ,ℂ))) := by
    rw [radialDirichlet_zeroExtension_derivative]
    exact memSobolev_zero_iff.mpr ⟨_,rfl⟩
  simpa only [zero_add] using real_sobolev_gain_one hu hd

/-- The original Dirichlet value has a continuous representative with literal zero boundary value. -/
theorem radialDirichlet_zero_trace (v : radialDirichletDomain) :
    ∃ f : ℝ → ℂ, Continuous f ∧ f =ᵐ[radialMeasure] ((v : RadialDerivativeSpace) 0) ∧
      (∀ t : ℝ, 0 ≤ t → f t = 0) := by
  let u := negativeZeroExtension ((v : RadialDerivativeSpace) 0)
  obtain ⟨f,hf,ha⟩ := real_sobolev_continuous_representative u 1 (by norm_num)
    (radialDirichlet_zeroExtension_sobolev v)
  have he := negativeZeroExtension_ae ((v : RadialDerivativeSpace) 0)
  have hn : f =ᵐ[radialMeasure] ((v : RadialDerivativeSpace) 0) := by
    filter_upwards [ha.filter_mono (ae_mono Measure.restrict_le_self),
      he.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem measurableSet_Iio] with t ha he ht
    rw [ha,he,negativeZeroExtensionFun,indicator_of_mem ht]
  have hp : f =ᵐ[volume.restrict (Ici (0:ℝ))] (fun _ => (0:ℂ)) := by
    filter_upwards [ha.filter_mono (ae_mono Measure.restrict_le_self),
      he.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem measurableSet_Ici] with t ha he ht
    have hi : t ∉ Iio (0:ℝ) := by
      change ¬t < 0
      change 0 ≤ t at ht
      exact not_lt.mpr ht
    rw [ha,he,negativeZeroExtensionFun,indicator_of_notMem hi]
  have hz := Measure.eqOn_of_ae_eq hp hf.continuousOn continuous_const.continuousOn
    (show Ici (0:ℝ) ⊆ closure (interior (Ici (0:ℝ))) by simp)
  exact ⟨f,hf,hn,fun t ht => hz ht⟩

end
end RHTower.D4BMJointWave
