import GaloisForLFunctions.HTGeometry.UnitWaveSine
import GaloisForLFunctions.HTGeometry.VolterraCausalConstraints
/-! The physical retarded kernel with a bounded, possibly complex, spatial potential. -/
open MeasureTheory
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

def unitWaveKernel (W : FourierRealL2 →L[ℂ] FourierRealL2) (τ σ : ℝ) :
    FourierRealL2 →L[ℝ] FourierRealL2 :=
  ((unitWaveSine (τ-σ)).comp W).restrictScalars ℝ

theorem unitWaveKernel_apply (W : FourierRealL2 →L[ℂ] FourierRealL2) (τ σ : ℝ)
    (f : FourierRealL2) : unitWaveKernel W τ σ f = unitWaveSine (τ-σ) (W f) := rfl

theorem unitWaveKernel_norm_le (W : FourierRealL2 →L[ℂ] FourierRealL2) (τ σ : ℝ) :
    ‖unitWaveKernel W τ σ‖ ≤ (2*Real.pi)⁻¹*‖W‖ := by
  rw [unitWaveKernel,ContinuousLinearMap.norm_restrictScalars]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (unitWaveSine_norm_le (τ-σ)) (norm_nonneg _))

theorem unitWaveKernel_strong (W : FourierRealL2 →L[ℂ] FourierRealL2) :
    StrongKernel (unitWaveKernel W) := by
  intro f hf
  exact unitWaveSine_continuous_comp _ _ (continuous_fst.sub continuous_snd)
    (W.continuous.comp (hf.comp continuous_snd))

/-- Even complex potentials retain the original reflection symmetry of the causal kernel. -/
theorem unitWaveKernel_reflection (W : FourierRealL2 →L[ℂ] FourierRealL2)
    (hW : ∀ f, W (l2Reflection f) = l2Reflection (W f)) (τ σ : ℝ) (f : FourierRealL2) :
    l2Reflection (unitWaveKernel W τ σ f) = unitWaveKernel W τ σ (l2Reflection f) := by
  simp only [unitWaveKernel_apply,hW,unitWaveSine_reflection]

end
end GaloisForLFunctions.HTGeometry
