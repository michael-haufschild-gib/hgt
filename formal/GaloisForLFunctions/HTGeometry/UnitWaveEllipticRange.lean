import GaloisForLFunctions.HTGeometry.UnitWaveTimeIntegration
import GaloisForLFunctions.HTGeometry.KleinGordonStrongSolution

/-! Two spatial inverse-frequency factors from time regularity of the actual forcing. -/
open MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The physical inverse elliptic multiplier `(2*pi)^(-2)<D>^(-2)`. -/
def unitWaveEllipticInv : FourierRealL2 →L[ℝ] FourierRealL2 :=
  ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
    ((kgFreqInvOp.comp kgFreqInvOp).restrictScalars ℝ)

private theorem elliptic_cos_hasDerivAt (τ : ℝ) (f : FourierRealL2) :
    HasDerivAt (fun t : ℝ => unitWaveEllipticInv (kgCosOp (2*Real.pi*t) f))
      (-unitWaveSine τ f) τ := by
  have h := (hasDerivAt_kgCosOp_freqInv (2*Real.pi*τ) (kgFreqInvOp f)).scomp τ
    ((hasDerivAt_id τ).const_mul (2*Real.pi))
  have hs := h.const_smul ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ)
  have he : (fun t : ℝ => ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
      kgCosOp (2*Real.pi*t) (kgFreqInvOp (kgFreqInvOp f))) =
      (fun t => unitWaveEllipticInv (kgCosOp (2*Real.pi*t) f)) := by
    funext t
    change ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
      kgCosOp (2*Real.pi*t) (kgFreqInvOp (kgFreqInvOp f)) =
      ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) • kgFreqInvOp (kgFreqInvOp (kgCosOp (2*Real.pi*t) f))
    rw [kgFreqInvOp_kgCosOp,kgFreqInvOp_kgCosOp]
  change HasDerivAt (fun t : ℝ => ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ) •
    kgCosOp (2*Real.pi*t) (kgFreqInvOp (kgFreqInvOp f))) _ τ at hs
  rw [he] at hs
  apply hs.congr_deriv
  simp only [mul_one,smul_neg,smul_smul]
  rw [← kgFreqInvOp_kgSinOp,← kgSinFreqOp_apply_freqInv]
  change -( ((2*Real.pi)⁻¹*(2*Real.pi)⁻¹*(2*Real.pi):ℝ) • kgSinFreqOp (2*Real.pi*τ) f) =
    -(((2*Real.pi)⁻¹:ℝ) • kgSinFreqOp (2*Real.pi*τ) f)
  congr 2
  field_simp

/-- Time integration by parts proves exact membership in the twice-regularized spatial range. -/
theorem unitWaveDuhamel_elliptic_range (F F' : ℝ → FourierRealL2)
    (hF : Continuous F) (hF' : Continuous F') (hd : ∀ t, HasDerivAt F (F' t) t) (τ : ℝ) :
    unitWaveDuhamel F τ = unitWaveEllipticInv
      (F τ-kgCosOp (2*Real.pi*τ) (F 0)-
        ∫ σ in (0:ℝ)..τ, kgCosOp (2*Real.pi*(τ-σ)) (F' σ)) := by
  let T (r : ℝ) : FourierRealL2 →L[ℝ] FourierRealL2 :=
    unitWaveEllipticInv.comp ((kgCosOp (2*Real.pi*(τ-r))).restrictScalars ℝ)
  have hM (r : ℝ) : ‖T r‖ ≤ ‖unitWaveEllipticInv‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact (mul_le_mul_of_nonneg_left (norm_kgCosOp_le _) (norm_nonneg _)).trans_eq (mul_one _)
  have hT (σ : ℝ) : HasDerivAt (fun r => T r (F r))
      (T σ (F' σ)+unitWaveSine (τ-σ) (F σ)) σ := by
    have h := (elliptic_cos_hasDerivAt (τ-σ) (F σ)).scomp σ
      ((hasDerivAt_const σ τ).sub (hasDerivAt_id σ))
    have h' : HasDerivAt (fun r => T r (F σ)) (unitWaveSine (τ-σ) (F σ)) σ := by
      convert h using 1 <;> first | rfl | simp
    exact hasDerivAt_strong_apply hM
      (fun x => unitWaveEllipticInv.continuous.comp (continuous_kgCosOp_comp
        (continuous_const.mul (continuous_const.sub continuous_id)) continuous_const)) (hd σ) h'
  have hiC := (continuous_kgCosOp_comp (r := fun σ : ℝ => 2*Real.pi*(τ-σ))
    (continuous_const.mul (continuous_const.sub continuous_id)) hF').intervalIntegrable (μ := volume) 0 τ
  have hiT := (unitWaveEllipticInv.continuous.comp (continuous_kgCosOp_comp (r := fun σ : ℝ => 2*Real.pi*(τ-σ))
    (continuous_const.mul (continuous_const.sub continuous_id)) hF')).intervalIntegrable (μ := volume) 0 τ
  have hiD := (unitWaveSine_continuous_comp (fun σ : ℝ => τ-σ) F
    (continuous_const.sub continuous_id) hF).intervalIntegrable (μ := volume) 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hT σ) (hiT.add hiD)
  simp only [T,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars'] at h
  have hadd := intervalIntegral.integral_add hiT hiD
  simp only [Function.comp_def] at hadd
  rw [hadd] at h
  change (∫ σ in (0:ℝ)..τ, unitWaveEllipticInv (kgCosOp (2*Real.pi*(τ-σ)) (F' σ)))+
    unitWaveDuhamel F τ = unitWaveEllipticInv (kgCosOp (2*Real.pi*(τ-τ)) (F τ))-
      unitWaveEllipticInv (kgCosOp (2*Real.pi*(τ-0)) (F 0)) at h
  rw [unitWaveEllipticInv.intervalIntegral_comp_comm hiC,sub_self,mul_zero,kgCosOp_zero,
    ContinuousLinearMap.id_apply,sub_zero] at h
  rw [map_sub,map_sub]
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact h

/-- The twice-regularized identity is the strong wave graph equation for a zero-onset forcing. -/
theorem unitWaveDuhamel_wave_graph (F F' : ℝ → FourierRealL2)
    (hF : Continuous F) (hF' : Continuous F') (hd : ∀ t, HasDerivAt F (F' t) t)
    (h₀ : F 0 = 0) (τ : ℝ) :
    unitWaveDuhamel F τ = unitWaveEllipticInv (F τ-deriv (deriv (unitWaveDuhamel F)) τ) := by
  rw [(unitWaveDuhamel_second_hasDerivAt F F' hF hF' hd h₀ τ).deriv,
    unitWaveDuhamel_elliptic_range F F' hF hF' hd τ,h₀,map_zero,sub_zero]

end
end GaloisForLFunctions.HTGeometry
