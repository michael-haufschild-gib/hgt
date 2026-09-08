import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointKernelCoherence

/-! Full right-half-plane Laplace identification of the original joint response. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every positive Laplace frequency gives an absolutely convergent transform of the fixed kernel. -/
theorem waveCausalKernel_integrable_rightHalfPlane (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t => expRay w t • waveCausalKernel J hJ F δ hδ t) (Ioi (0:ℝ)) := by
  have he : 0 < w.re/4 := by positivity
  have hi := waveCausalKernel_integrable J hJ F (w.re/4) he w (by linarith)
  apply hi.congr
  filter_upwards [waveCausalKernel_independent_on_ray J hJ F (w.re/4) δ he hδ] with t ht
  exact congrArg (fun u : H => expRay w t • u) ht

/-- Damping independence removes the extra half-plane restriction from causal inversion. -/
theorem waveCausalKernel_laplace_rightHalfPlane (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • waveCausalKernel J hJ F δ hδ t) =
      waveSpatialResolvent J w F := by
  have he : 0 < w.re/4 := by positivity
  calc
    _ = ∫ t in Ioi (0:ℝ), expRay w t • waveCausalKernel J hJ F (w.re/4) he t := by
      apply integral_congr_ae
      filter_upwards [waveCausalKernel_independent_on_ray J hJ F δ (w.re/4) hδ he] with t ht
      exact congrArg (fun u : H => expRay w t • u) ht
    _ = _ := waveCausalKernel_laplace J hJ F (w.re/4) he w (by linarith)

theorem jointCausalKernel_integrable (F : SpatialSpace) (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t => expRay w t • jointCausalKernel F t) (Ioi (0:ℝ)) :=
  waveCausalKernel_integrable_rightHalfPlane jointEmbedding jointEmbedding_norm_le F 1 one_pos w hw

/-- The original selected spatial response is a causal Laplace transform throughout Re(w)>0. -/
theorem jointCausalKernel_originalResponse_rightHalfPlane (F : SpatialSpace)
    (w : ℂ) (hw : 0 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • jointCausalKernel F t) =
      jointEmbedding (jointWaveResponse w hw F) := by
  have he := waveCausalKernel_laplace_rightHalfPlane jointEmbedding jointEmbedding_norm_le
    F 1 one_pos w hw
  change (∫ t in Ioi (0:ℝ), expRay w t • jointCausalKernel F t) =
    jointEmbedding (waveEnergyInverse jointEmbedding w (jointEmbedding.adjoint F)) at he
  rw [waveEnergyInverse_jointResponse w hw] at he
  exact he

/-- Every positive exponential damping of the original causal response belongs to spatial-vector L². -/
theorem jointCausalKernel_memLp_pos (F : SpatialSpace) (c : ℝ) (hc : 0 < c) :
    MemLp (fun t => expRay c t • jointCausalKernel F t) 2 (volume.restrict (Ioi (0:ℝ))) :=
  waveDampedKernel_memLp_pos jointEmbedding jointEmbedding_norm_le F 1 one_pos c hc

end
end RHTower.D4BMJointWave
