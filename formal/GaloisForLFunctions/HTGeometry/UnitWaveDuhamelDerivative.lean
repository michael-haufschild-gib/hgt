import GaloisForLFunctions.HTGeometry.UnitWaveDuhamel
import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelFirstDerivative

/-! The actual first time derivative of the physical retarded convolution. -/
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section

private def kgConvolution (F : ℝ → FourierRealL2) (τ : ℝ) : FourierRealL2 :=
  ∫ σ in (0:ℝ)..τ, kgSinFreqOp (τ-σ) (F σ)

private theorem kgConvolution_hasDerivAt (F : ℝ → FourierRealL2) (hF : Continuous F) (τ : ℝ) :
    HasDerivAt (kgConvolution F) (∫ σ in (0:ℝ)..τ, kgCosOp (τ-σ) (F σ)) τ := by
  have h := hasDerivAt_kgDuhamel hF τ
  rw [kgDuhamel_deriv_eq hF τ] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [] with t
  exact intervalIntegral_kgFieldKernel_separated (ContinuousLinearMap.id ℂ FourierRealL2) hF t

private theorem rescaledConvolution (A : ℝ → FourierRealL2 →L[ℂ] FourierRealL2)
    (F : ℝ → FourierRealL2) (c : ℝ) (hc : c ≠ 0) (τ : ℝ) :
    (∫ σ in (0:ℝ)..τ, A (c*(τ-σ)) (F σ)) =
      c⁻¹ • ∫ σ in (0:ℝ)..(c*τ), A (c*τ-σ) (F (σ/c)) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun σ => A (c*τ-σ) (F (σ/c))) (a := (0:ℝ)) (b := τ) hc
  simp only [mul_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro σ _
  change A (c*(τ-σ)) (F σ) = A (c*τ-c*σ) (F (c*σ/c))
  rw [mul_div_cancel_left₀ σ hc,mul_sub]

private theorem unitWaveDuhamel_rescaled (F : ℝ → FourierRealL2) (τ : ℝ) :
    unitWaveDuhamel F τ = ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
      kgConvolution (fun σ => F (σ/(2*Real.pi))) (2*Real.pi*τ) := by
  change (∫ σ in (0:ℝ)..τ, ((2*Real.pi)⁻¹:ℝ) • kgSinFreqOp (2*Real.pi*(τ-σ)) (F σ)) = _
  rw [intervalIntegral.integral_smul,rescaledConvolution kgSinFreqOp F (2*Real.pi)
    (by positivity) τ,smul_smul]
  rfl

/-- The true derivative is the physical cosine convolution, including all `2*pi` factors. -/
theorem unitWaveDuhamel_hasDerivAt (F : ℝ → FourierRealL2) (hF : Continuous F) (τ : ℝ) :
    HasDerivAt (unitWaveDuhamel F)
      (∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F σ)) τ := by
  have hc : 2*Real.pi ≠ 0 := by positivity
  have hg : Continuous (fun σ => F (σ/(2*Real.pi))) := hF.comp (continuous_id.div_const _)
  have h := (kgConvolution_hasDerivAt _ hg (2*Real.pi*τ)).scomp τ
    ((hasDerivAt_id τ).const_mul (2*Real.pi))
  have hs := h.const_smul ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ)
  have hd : ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
      ((2*Real.pi*1) • ∫ σ in (0:ℝ)..(2*Real.pi*τ),
        kgCosOp (2*Real.pi*τ-σ) (F (σ/(2*Real.pi)))) =
      ∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F σ) := by
    rw [mul_one,smul_smul,rescaledConvolution kgCosOp F (2*Real.pi) hc τ]
    congr 1
    field_simp
  apply (hs.congr_deriv hd).congr_of_eventuallyEq
  filter_upwards [] with t
  exact unitWaveDuhamel_rescaled F t

/-- The first time derivative depends continuously on time for every continuous actual forcing. -/
theorem unitWaveDuhamel_deriv_continuous (F : ℝ → FourierRealL2) (hF : Continuous F) :
    Continuous (deriv (unitWaveDuhamel F)) := by
  have he : deriv (unitWaveDuhamel F) =
      fun τ => ∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F σ) :=
    funext (fun τ => (unitWaveDuhamel_hasDerivAt F hF τ).deriv)
  rw [he]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous ?_ continuous_id
  exact continuous_kgCosOp_comp (continuous_const.mul (continuous_fst.sub continuous_snd))
    (hF.comp continuous_snd)

/-- Retarded integration gains one exact inverse-frequency factor in the spatial variable. -/
theorem unitWaveDuhamel_freqInv (F : ℝ → FourierRealL2) (hF : Continuous F) (τ : ℝ) :
    unitWaveDuhamel F τ = kgFreqInvOp (((2*Real.pi)⁻¹:ℝ) •
      ∫ σ in (0:ℝ)..τ, kgSinOp (2*Real.pi*(τ-σ)) (F σ)) := by
  have hi : IntervalIntegrable (fun σ => kgSinOp (2*Real.pi*(τ-σ)) (F σ)) volume 0 τ :=
    (continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.mul (continuous_const.sub continuous_id)) hF).intervalIntegrable 0 τ
  change (∫ σ in (0:ℝ)..τ, ((2*Real.pi)⁻¹:ℝ) • kgSinFreqOp (2*Real.pi*(τ-σ)) (F σ)) = _
  change (∫ σ in (0:ℝ)..τ, ((2*Real.pi)⁻¹:ℝ) • kgSinFreqOp (2*Real.pi*(τ-σ)) (F σ)) =
    (kgFreqInvOp.restrictScalars ℝ) (((2*Real.pi)⁻¹:ℝ) •
      ∫ σ in (0:ℝ)..τ, kgSinOp (2*Real.pi*(τ-σ)) (F σ))
  rw [map_smul,← (kgFreqInvOp.restrictScalars ℝ).intervalIntegral_comp_comm hi,
    ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro σ _
  change ((2*Real.pi)⁻¹:ℝ) • kgSinFreqOp (2*Real.pi*(τ-σ)) (F σ) = _
  rw [kgSinFreqOp_apply_freqInv]
  rfl

end
end GaloisForLFunctions.HTGeometry
