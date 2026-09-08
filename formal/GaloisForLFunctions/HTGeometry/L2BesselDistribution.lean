import GaloisForLFunctions.HTGeometry.UnitWaveEllipticRange

/-! The actual L² inverse-frequency operator agrees with the distributional Bessel potential. -/
open MeasureTheory Filter FourierTransform TemperedDistribution
open scoped SchwartzMap
namespace GaloisForLFunctions.HTGeometry
open RHTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The bounded pointwise multiplier and the tempered-distribution multiplier agree on original L² classes. -/
theorem lpBoundedMulCLM_toDistribution {φ : ℝ → ℂ} (hφ : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖φ x‖ ≤ C) (ht : φ.HasTemperateGrowth) (f : FourierRealL2) :
    ((lpBoundedMulCLM hφ hC hb f : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      smulLeftCLM ℂ φ (f : 𝓢'(ℝ,ℂ)) := by
  ext ψ
  simp only [Lp.toTemperedDistribution_apply,smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := volume) hφ hC hb f] with x hx
  rw [hx,SchwartzMap.smulLeftCLM_apply_apply ht]
  simp only [smul_eq_mul]
  ring

/-- Fourier conjugation preserves the exact distribution associated with the L² multiplier. -/
theorem fourierMulCLM_toDistribution {φ : ℝ → ℂ} (hφ : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖φ x‖ ≤ C) (ht : φ.HasTemperateGrowth) (f : FourierRealL2) :
    ((fourierMulCLM hφ hC hb f : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ φ (f : 𝓢'(ℝ,ℂ)) := by
  rw [fourierMulCLM_apply]
  change Lp.toTemperedDistribution (𝓕⁻ (lpBoundedMulCLM hφ hC hb (𝓕 f))) = _
  rw [← Lp.fourierInv_toTemperedDistribution_eq,lpBoundedMulCLM_toDistribution hφ C hC hb ht,
    ← Lp.fourier_toTemperedDistribution_eq]
  rfl

private theorem kgFreqInv_besselSymbol :
    (kgFreqInv : ℝ → ℂ) = fun x => (((1+‖x‖^2)^((-1:ℝ)/2):ℝ):ℂ) := by
  funext x
  rw [kgFreqInv,kgFreq,Real.sqrt_eq_rpow,← Real.rpow_neg (by positivity)]
  congr 2
  ring

/-- The single inverse frequency is the original negative-order Bessel potential. -/
theorem kgFreqInvOp_toDistribution (f : FourierRealL2) :
    ((kgFreqInvOp f : FourierRealL2) : 𝓢'(ℝ,ℂ)) = besselPotential ℝ ℂ (-1) (f : 𝓢'(ℝ,ℂ)) := by
  have ht : (kgFreqInv : ℝ → ℂ).HasTemperateGrowth := by
    rw [kgFreqInv_besselSymbol]
    fun_prop
  rw [kgFreqInvOp,fourierMulCLM_toDistribution _ 1 zero_le_one norm_kgFreqInv_le ht,
    kgFreqInv_besselSymbol]
  rfl

/-- The twice-regularized class belongs to Sobolev order two with its actual L² preimage. -/
theorem kgFreqInvOp_two_memSobolev (f : FourierRealL2) :
    MemSobolev 2 2 ((kgFreqInvOp (kgFreqInvOp f) : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  refine ⟨f,?_⟩
  rw [kgFreqInvOp_toDistribution,kgFreqInvOp_toDistribution,
    besselPotential_besselPotential_apply,besselPotential_besselPotential_apply]
  norm_num

/-- The restored inverse elliptic operator has the exact distributional normalization. -/
theorem unitWaveEllipticInv_toDistribution (f : FourierRealL2) :
    ((unitWaveEllipticInv f : FourierRealL2) : 𝓢'(ℝ,ℂ)) =
      (((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ):ℂ) • besselPotential ℝ ℂ (-2) (f : 𝓢'(ℝ,ℂ)) := by
  change Lp.toTemperedDistribution
    ((((2*Real.pi)⁻¹*(2*Real.pi)⁻¹:ℝ):ℂ) • kgFreqInvOp (kgFreqInvOp f)) = _
  rw [← Lp.toTemperedDistributionCLM_apply,map_smul,Lp.toTemperedDistributionCLM_apply,
    kgFreqInvOp_toDistribution,kgFreqInvOp_toDistribution,besselPotential_besselPotential_apply]
  norm_num

/-- The actual inverse elliptic image is admitted to the required spatial Sobolev domain. -/
theorem unitWaveEllipticInv_memSobolev (f : FourierRealL2) :
    MemSobolev 2 2 ((unitWaveEllipticInv f : FourierRealL2) : 𝓢'(ℝ,ℂ)) := by
  rw [unitWaveEllipticInv_toDistribution]
  apply MemSobolev.smul
  apply memSobolev_besselPotential_iff.mpr
  norm_num only [neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨f,rfl⟩

end
end GaloisForLFunctions.HTGeometry
