import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointHardyResponse
import GaloisForLFunctions.HTGeometry.HilbertL2FourierNaturality

/-! Actual Hilbert-valued vertical boundary vectors and their common inverse Fourier transform. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shiftedWaveVector_bound (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    ‖waveSpatialResolvent J (w+δ) F‖ ≤ (‖F‖/δ)*‖(w+(δ:ℂ))⁻¹‖ := by
  have hs : 0 < (w+(δ:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  have hn : 0 < ‖w+(δ:ℂ)‖ := lt_of_lt_of_le hs (Complex.re_le_norm _)
  calc
    _ ≤ ‖F‖/((w+(δ:ℂ)).re*‖w+(δ:ℂ)‖) := waveSpatialResolvent_bound J hJ _ hs F
    _ ≤ ‖F‖/(δ*‖w+(δ:ℂ)‖) := div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hδ hn)
      (mul_le_mul_of_nonneg_right (by simp only [Complex.add_re,Complex.ofReal_re]; linarith) hn.le)
    _ = _ := by rw [norm_inv]; ring

theorem shiftedWaveVector_memLp (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) :
    MemLp (fun ξ : ℝ => waveSpatialResolvent J (rayLine σ ξ+δ) F) 2 volume := by
  have hi := isHalfPlaneHardy_inv_shift (c := (δ:ℂ)) (by simpa using hδ)
  have hd : DifferentiableOn ℂ (fun z : ℂ => waveSpatialResolvent J (z+δ) F)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    have hs : 0 < (z+(δ:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
    exact (DifferentiableAt.comp (f := fun w : ℂ => w+(δ:ℂ))
      (g := fun w : ℂ => waveSpatialResolvent J w F) z
      (waveSpatialResolvent_apply_differentiableAt J hJ F (z+δ) hs)
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hc : Continuous (fun ξ : ℝ => waveSpatialResolvent J (rayLine σ ξ+δ) F) :=
    hd.continuousOn.comp_continuous (by unfold rayLine; fun_prop) (fun ξ => by simpa using hσ)
  apply MemLp.mono' ((hi.memLp σ hσ).norm.const_mul (‖F‖/δ)) hc.aestronglyMeasurable
  exact Eventually.of_forall (fun ξ => shiftedWaveVector_bound J hJ F δ hδ _ (by simpa using hσ))

def waveLineVector (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) : Lp H 2 (volume : Measure ℝ) :=
  (shiftedWaveVector_memLp J hJ F δ hδ σ hσ).toLp _

def waveLinePreimage (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) : Lp H 2 (volume : Measure ℝ) :=
  𝓕⁻ (waveLineVector J hJ F δ hδ σ hσ)

/-- Every continuous probe observes the same original Hilbert-valued boundary vector. -/
theorem waveLineVector_probe (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) (ℓ : H →L[ℂ] ℂ) :
    ℓ.compLp (waveLineVector J hJ F δ hδ σ hσ) =
      ((shiftedWaveProbe_hardy J hJ F ℓ δ hδ).memLp σ hσ).toLp _ := by
  apply Lp.ext
  filter_upwards [ℓ.coeFn_compLp (waveLineVector J hJ F δ hδ σ hσ),
    (shiftedWaveVector_memLp J hJ F δ hδ σ hσ).coeFn_toLp,
    ((shiftedWaveProbe_hardy J hJ F ℓ δ hδ).memLp σ hσ).coeFn_toLp] with ξ hL hV hP
  simp only [waveLineVector] at hL ⊢
  rw [hL,hV,hP]
  rfl

/-- Probe inversion is induced by one actual vector inverse Fourier transform. -/
theorem waveLinePreimage_probe (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (δ : ℝ) (hδ : 0 < δ) (σ : ℝ) (hσ : 0 < σ) (ℓ : H →L[ℂ] ℂ) :
    ℓ.compLp (waveLinePreimage J hJ F δ hδ σ hσ) =
      hardyPreimage (shiftedWaveProbe J F ℓ δ) σ
        ((shiftedWaveProbe_hardy J hJ F ℓ δ hδ).memLp σ hσ) := by
  unfold waveLinePreimage hardyPreimage
  rw [compLp_fourierInv,waveLineVector_probe]

end
end RHTower.D4BMJointWave
