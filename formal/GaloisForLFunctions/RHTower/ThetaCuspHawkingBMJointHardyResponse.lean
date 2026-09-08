import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointAnalyticInverse
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift
import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane

/-! The actual joint resolvent has causal Laplace representatives under every continuous spatial probe. -/
namespace RHTower.D4BMJointWave
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shiftedWaveProbe (J : V →L[ℂ] H) (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (w : ℂ) : ℂ :=
  ℓ (waveSpatialResolvent J (w+δ) F)

theorem shiftedWaveProbe_differentiableAt (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ (shiftedWaveProbe J F ℓ δ) w := by
  have hs : 0 < (w+(δ:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  have hc : DifferentiableAt ℂ (fun z : ℂ => waveSpatialResolvent J (z+δ) F) w :=
    DifferentiableAt.comp (f := fun z : ℂ => z+(δ:ℂ))
      (g := fun z : ℂ => waveSpatialResolvent J z F) w
      (waveSpatialResolvent_apply_differentiableAt J hJ F (w+δ) hs)
      (differentiableAt_id.add_const _)
  exact ℓ.differentiableAt.comp w hc

/-- Removing one Cauchy decay factor leaves a bounded holomorphic response on every shifted half-plane. -/
theorem shiftedWaveProbe_multiplier_bound (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    ‖(w+δ)*shiftedWaveProbe J F ℓ δ w‖ ≤ (‖ℓ‖*‖F‖)/δ := by
  have hs : 0 < (w+(δ:ℂ)).re := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  have hn : 0 < ‖w+(δ:ℂ)‖ := lt_of_lt_of_le hs (Complex.re_le_norm _)
  have hb := waveSpatialResolvent_bound J hJ (w+δ) hs F
  calc
    ‖(w+δ)*shiftedWaveProbe J F ℓ δ w‖ =
        ‖w+(δ:ℂ)‖*‖ℓ (waveSpatialResolvent J (w+δ) F)‖ := norm_mul _ _
    _ ≤ ‖w+(δ:ℂ)‖*(‖ℓ‖*(‖F‖/((w+(δ:ℂ)).re*‖w+(δ:ℂ)‖))) :=
      mul_le_mul_of_nonneg_left
        ((ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) hn.le
    _ = (‖ℓ‖*‖F‖)/(w+(δ:ℂ)).re := by field_simp
    _ ≤ (‖ℓ‖*‖F‖)/δ := div_le_div_of_nonneg_left
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hδ (by
        simp only [Complex.add_re,Complex.ofReal_re]; linarith)

/-- The Hardy hypotheses follow from the actual inverse, with no supplied frequency-family bound. -/
theorem shiftedWaveProbe_hardy (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) :
    IsHalfPlaneHardy (shiftedWaveProbe J F ℓ δ)
      (((‖ℓ‖*‖F‖)/δ)^2 * (1/(2*δ))) := by
  have hi := isHalfPlaneHardy_inv_shift (c := (δ:ℂ)) (by simpa using hδ)
  have hg : DifferentiableOn ℂ (fun w : ℂ => (w+δ)*shiftedWaveProbe J F ℓ δ w)
      {w : ℂ | 0 < w.re} := by
    intro w hw
    exact ((differentiableAt_id.add_const _).mul
      (shiftedWaveProbe_differentiableAt J hJ F ℓ δ hδ w hw)).differentiableWithinAt
  have hp := isHalfPlaneHardy_mul_of_bounded hi hg
    (shiftedWaveProbe_multiplier_bound J hJ F ℓ δ hδ)
  apply hp.congr
  intro w hw
  have h0 : w+(δ:ℂ) ≠ 0 := by
    intro hz
    have hz' := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hz'
    linarith
  rw [← mul_assoc,inv_mul_cancel₀ h0,one_mul]

/-- A concrete inverse-Fourier datum of the original measured spatial response. -/
def waveProbeCausalDatum (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) : ℝ → ℂ :=
  hardyDatum _ (shiftedWaveProbe_hardy J hJ F ℓ δ hδ)

theorem waveProbeCausalDatum_memLp (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) :
    MemLp (waveProbeCausalDatum J hJ F ℓ δ hδ) 2 (volume.restrict (Ioi (0:ℝ))) :=
  memLp_two_hardyDatum (shiftedWaveProbe_hardy J hJ F ℓ δ hδ)

/-- Causality is proved as actual almost-everywhere vanishing before time zero. -/
theorem waveProbeCausalDatum_support (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t < 0 → waveProbeCausalDatum J hJ F ℓ δ hδ t = 0 :=
  hardyDatum_ae_zero_of_neg (shiftedWaveProbe_hardy J hJ F ℓ δ hδ)

/-- Its Laplace transform equals the actual original spatial response at independent frequency. -/
theorem waveProbeCausalDatum_laplace (J : V →L[ℂ] H) (hJ : ∀ v, ‖J v‖ ≤ ‖v‖)
    (F : H) (ℓ : H →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) (w : ℂ) (hw : 0 < w.re) :
    laplaceRay (waveProbeCausalDatum J hJ F ℓ δ hδ) w =
      ℓ (waveSpatialResolvent J (w+δ) F) :=
  (isHalfPlaneHardy_eq_laplaceRay (shiftedWaveProbe_hardy J hJ F ℓ δ hδ) hw).symm

end
end RHTower.D4BMJointWave
