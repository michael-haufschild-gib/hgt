import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointVectorBoundary
import GaloisForLFunctions.HTGeometry.BochnerL2ProbeTotality

/-! One actual Hilbert-valued causal kernel for the original spatial resolvent. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem waveLinePreimage_probe_ae (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) (ℓ : H →L[ℂ] ℂ) :
    (fun t => ℓ (waveLinePreimage J hJ F δ hδ σ hσ t)) =ᵐ[volume]
      (hardyPreimage (shiftedWaveProbe J F ℓ δ) σ
        ((shiftedWaveProbe_hardy J hJ F ℓ δ hδ).memLp σ hσ) : ℝ → ℂ) := by
  have he := ℓ.coeFn_compLp (waveLinePreimage J hJ F δ hδ σ hσ)
  rw [waveLinePreimage_probe] at he
  exact Filter.EventuallyEq.symm he

/-- The actual vector inverse Fourier transform vanishes before time zero. -/
theorem waveLinePreimage_support (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → waveLinePreimage J hJ F δ hδ σ hσ t = 0 := by
  apply bochnerL2_ae_zero_on_of_inner_probes _ (Lp.memLp _) (Iio (0:ℝ)) measurableSet_Iio
  intro v
  let ℓ : H →L[ℂ] ℂ := innerSL ℂ v
  have hP := shiftedWaveProbe_hardy J hJ F ℓ δ hδ
  filter_upwards [waveLinePreimage_probe_ae J hJ F δ hδ σ hσ ℓ,
    hardyDatum_weight_ae hP hσ,hardyDatum_ae_zero_of_neg hP] with t hp hw hc
  intro ht
  change ℓ (waveLinePreimage J hJ F δ hδ σ hσ t) = 0
  rw [hp,← hw,hc ht,mul_zero]

/-- Undoing the Fourier-line damping gives one spatial-vector-valued causal kernel. -/
def waveCausalKernel (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) : H :=
  (Real.exp ((2*δ)*t) : ℂ) • waveLinePreimage J hJ F δ hδ δ hδ t

theorem waveCausalKernel_support (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → waveCausalKernel J hJ F δ hδ t = 0 := by
  filter_upwards [waveLinePreimage_support J hJ F δ hδ δ hδ] with t ht
  intro hneg
  simp only [waveCausalKernel,ht hneg,smul_zero]

theorem waveCausalKernel_damping (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    (Real.exp (-((2*δ)*t)) : ℂ) • waveCausalKernel J hJ F δ hδ t =
      waveLinePreimage J hJ F δ hδ δ hδ t := by
  rw [waveCausalKernel,smul_smul,← Complex.ofReal_mul,← Real.exp_add]
  simp

/-- Exponential damping of this actual kernel belongs to the original Hilbert-valued L² space. -/
theorem waveCausalKernel_weighted_memLp (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun t => (Real.exp (-((2*δ)*t)) : ℂ) • waveCausalKernel J hJ F δ hδ t) 2 volume := by
  simp only [waveCausalKernel_damping]
  exact Lp.memLp _

/-- All scalar causal data are observations of this single vector kernel. -/
theorem waveCausalKernel_probe (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (ℓ : H →L[ℂ] ℂ) :
    (fun t => ℓ (waveCausalKernel J hJ F δ hδ t)) =ᵐ[volume]
      (fun t => (Real.exp (δ*t) : ℂ)*waveProbeCausalDatum J hJ F ℓ δ hδ t) := by
  have hP := shiftedWaveProbe_hardy J hJ F ℓ δ hδ
  filter_upwards [waveLinePreimage_probe_ae J hJ F δ hδ δ hδ ℓ,
    hardyDatum_weight_ae hP hδ] with t ht hd
  simp only [waveCausalKernel,map_smul,smul_eq_mul,ht]
  rw [← hd,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  rw [show (2*δ)*t+ -(δ*t) = δ*t by ring]
  rfl

end
end RHTower.D4BMJointWave
