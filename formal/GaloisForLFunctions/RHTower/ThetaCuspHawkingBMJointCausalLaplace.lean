import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointCausalKernel

/-! The actual vector causal kernel has the original joint resolvent as its convergent Laplace transform. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem expRay_mul_realExp (w : ℂ) (c t : ℝ) :
    expRay w t * (Real.exp (c*t) : ℂ) = expRay (w-c) t := by
  simp only [expRay,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem waveCausalKernel_integrand (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (t : ℝ) :
    expRay w t • waveCausalKernel J hJ F δ hδ t =
      expRay (w-(2*δ)) t • waveLinePreimage J hJ F δ hδ δ hδ t := by
  rw [waveCausalKernel,smul_smul,expRay_mul_realExp]
  push_cast
  rfl

/-- Absolute Bochner integrability is proved from the actual weighted L² kernel. -/
theorem waveCausalKernel_integrable (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 2*δ < w.re) :
    IntegrableOn (fun t => expRay w t • waveCausalKernel J hJ F δ hδ t) (Ioi (0:ℝ)) := by
  have hw' : 0 < (w-(2*(δ:ℂ))).re := by
    have hr : (w-(2*(δ:ℂ))).re = w.re-2*δ := by simp
    rw [hr]
    linarith
  have hE := memLp_two_expRay_restrict hw' 0
  have hQ := (Lp.memLp (waveLinePreimage J hJ F δ hδ δ hδ)).restrict (Ioi (0:ℝ))
  have hi : IntegrableOn (fun t => expRay (w-(2*δ)) t •
      waveLinePreimage J hJ F δ hδ δ hδ t) (Ioi (0:ℝ)) :=
    (hE.norm.integrable_mul hQ.norm).mono'
      (hE.aestronglyMeasurable.smul hQ.aestronglyMeasurable)
      (Eventually.of_forall (fun t => (norm_smul _ _).le))
  simpa only [waveCausalKernel_integrand] using hi

theorem waveCausalKernel_laplace_probe (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 2*δ < w.re) (ℓ : H →L[ℂ] ℂ) :
    ℓ (∫ t in Ioi (0:ℝ), expRay w t • waveCausalKernel J hJ F δ hδ t) =
      ℓ (waveSpatialResolvent J w F) := by
  have hw' : 0 < (w-(δ:ℂ)).re := by
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith
  calc
    _ = ∫ t in Ioi (0:ℝ), ℓ (expRay w t • waveCausalKernel J hJ F δ hδ t) :=
      (ℓ.integral_comp_comm (waveCausalKernel_integrable J hJ F δ hδ w hw)).symm
    _ = laplaceRay (waveProbeCausalDatum J hJ F ℓ δ hδ) (w-δ) := by
      unfold laplaceRay
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (waveCausalKernel_probe J hJ F δ hδ ℓ)] with t ht
      rw [map_smul,smul_eq_mul,ht,← mul_assoc,expRay_mul_realExp,mul_comm]
    _ = ℓ (waveSpatialResolvent J ((w-δ)+δ) F) :=
      waveProbeCausalDatum_laplace J hJ F ℓ δ hδ (w-δ) hw'
    _ = _ := by rw [sub_add_cancel]

/-- Causal inversion identifies the original spatial vector, not only separately assigned scalar outputs. -/
theorem waveCausalKernel_laplace (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 2*δ < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • waveCausalKernel J hJ F δ hδ t) =
      waveSpatialResolvent J w F := by
  apply ext_inner_left ℂ
  intro v
  exact waveCausalKernel_laplace_probe J hJ F δ hδ w hw (innerSL ℂ v)

/-- A fixed, frequency-independent causal kernel in the original joint spatial Hilbert space. -/
def jointCausalKernel (F : SpatialSpace) : ℝ → SpatialSpace :=
  waveCausalKernel jointEmbedding jointEmbedding_norm_le F 1 one_pos

theorem jointCausalKernel_support (F : SpatialSpace) :
    ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → jointCausalKernel F t = 0 :=
  waveCausalKernel_support jointEmbedding jointEmbedding_norm_le F 1 one_pos

theorem jointCausalKernel_weighted_memLp (F : SpatialSpace) :
    MemLp (fun t => (Real.exp (-(2*t)) : ℂ) • jointCausalKernel F t) 2 volume := by
  simpa only [jointCausalKernel,mul_one] using
    waveCausalKernel_weighted_memLp jointEmbedding jointEmbedding_norm_le F 1 one_pos

/-- The original selected energy response is the actual Laplace transform of a causal spatial kernel. -/
theorem jointCausalKernel_originalResponse (F : SpatialSpace) (w : ℂ) (hw : 2 < w.re) :
    (∫ t in Ioi (0:ℝ), expRay w t • jointCausalKernel F t) =
      jointEmbedding (jointWaveResponse w (by linarith) F) := by
  have he := waveCausalKernel_laplace jointEmbedding jointEmbedding_norm_le F 1 one_pos w
    (by simpa only [mul_one] using hw)
  change (∫ t in Ioi (0:ℝ), expRay w t • jointCausalKernel F t) =
    jointEmbedding (waveEnergyInverse jointEmbedding w (jointEmbedding.adjoint F)) at he
  rw [waveEnergyInverse_jointResponse w (by linarith)] at he
  exact he

end
end RHTower.D4BMJointWave
