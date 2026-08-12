import GaloisForLFunctions.RHTower.CCMArchimedeanGeometricCompositeKernel
import GaloisForLFunctions.RHTower.CCMArchimedeanMellinTransport

/-!
# Spectral--geometric bridge for the CCM archimedean phase

This module identifies the literal geometric operator constructed from the sharp multiplicative
projection with the already trace-ideal-controlled spectral logarithmic phase differential.  The
essential analytic step is the exact conjugacy between the Hardy projection and multiplication by
`1_[1,∞)` under the normalized Mellin transform.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

theorem ccmPositiveHalfLineProjection_dilation
    (r : ℝ) (hr : 0 < r) (f : SoninL2) :
    ccmPositiveHalfLineProjection (dilation r hr f) =
      dilation r hr (ccmPositiveHalfLineProjection f) := by
  apply Lp.ext
  have hinner :=
    (indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f).comp_tendsto
      (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [
    indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici (dilation r hr f),
    dilation_ae r hr f,
    dilation_ae r hr (ccmPositiveHalfLineProjection f),
    hinner
  ] with x hleft hdil hright hcut
  change
    ((indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici (dilation r hr f) : SoninL2) :
        ℝ → ℂ) x =
      ((dilation r hr
        (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) : SoninL2) :
          ℝ → ℂ) x
  have hright' :
      ((dilation r hr
        (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) : SoninL2) :
          ℝ → ℂ) x =
        (Real.sqrt r : ℂ) *
          ((indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f : SoninL2) :
            ℝ → ℂ) (r * x) := by
    simpa only [ccmPositiveHalfLineProjection] using hright
  rw [hleft, hright']
  have hcut' :
      ((indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f : SoninL2) :
          ℝ → ℂ) (r * x) =
        (Ici (0 : ℝ)).indicator (fun y => f y) (r * x) := by
    simpa only [Function.comp_apply] using hcut
  rw [hcut']
  by_cases hx : 0 ≤ x
  · have hrx : 0 ≤ r * x := mul_nonneg hr.le hx
    simp [hx, hrx, hdil]
  · have hrx : ¬ 0 ≤ r * x := by
      intro h
      apply hx
      nlinarith
    simp [hx, hrx]

theorem ccmHardyProjection_mellinCore
    (f : SoninL2) :
    ccmHardyProjection
        (dilation MellinL2.spectralNormalization
          MellinL2.spectralNormalization_pos (fourierUnitary f)) =
      dilation MellinL2.spectralNormalization
        MellinL2.spectralNormalization_pos
        (fourierUnitary (ccmPositiveHalfLineProjection f)) := by
  let c := MellinL2.spectralNormalization
  have hc : 0 < c := MellinL2.spectralNormalization_pos
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hFourier :
      fourierUnitary (dilation c⁻¹ hcinv f) =
        dilation c hc (fourierUnitary f) := by
    simpa [inv_inv] using fourierUnitary_dilation c⁻¹ hcinv f
  change ccmHardyProjection
      (dilation c hc (fourierUnitary f)) =
    dilation c hc (fourierUnitary (ccmPositiveHalfLineProjection f))
  rw [← hFourier]
  rw [ccmHardyProjection_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [ccmPositiveHalfLineProjection_dilation c⁻¹ hcinv]
  simpa [inv_inv] using
    (fourierUnitary_dilation c⁻¹ hcinv (ccmPositiveHalfLineProjection f))

theorem expPullbackUnitary_ccmGeometricSharpProjection
    (f : CCMMultiplicativeL2) :
    MellinL2.expPullbackUnitary (ccmGeometricSharpProjection f) =
      ccmPositiveHalfLineProjection (MellinL2.expPullbackUnitary f) := by
  apply Lp.ext
  have hsharp := (ccmGeometricSharpProjection_ae f).comp_tendsto
    MellinL2.exp_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hpullOut := Lp.coeFn_compMeasurePreserving
    (ccmGeometricSharpProjection f) MellinL2.exp_measurePreserving
  have hpullIn := Lp.coeFn_compMeasurePreserving f MellinL2.exp_measurePreserving
  have hcut := indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici
    (MellinL2.expPullbackUnitary f)
  filter_upwards [hpullOut, hpullIn, hsharp, hcut] with t hout hin hsharp_t hcut_t
  change
    ((Lp.compMeasurePreserving MellinL2.expMeasurableEquiv
      MellinL2.exp_measurePreserving (ccmGeometricSharpProjection f) : SoninL2) :
        ℝ → ℂ) t =
      ((indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici
        (MellinL2.expPullbackUnitary f) : SoninL2) : ℝ → ℂ) t
  rw [hout, hcut_t]
  simp only [Function.comp_apply] at hsharp_t hin ⊢
  rw [hsharp_t]
  have hin' :
      ((MellinL2.expPullbackUnitary f : SoninL2) : ℝ → ℂ) t =
        f (MellinL2.expMeasurableEquiv t) := by
    change
      ((Lp.compMeasurePreserving MellinL2.expMeasurableEquiv
        MellinL2.exp_measurePreserving f : SoninL2) : ℝ → ℂ) t = _
    exact hin
  by_cases ht : 0 ≤ t
  · have hmem : (1 : ℝ) ≤ (MellinL2.expMeasurableEquiv t : ℝ) := by
      change (1 : ℝ) ≤ Real.exp t
      exact (Real.one_le_exp_iff).2 ht
    have hti : t ∈ Ici (0 : ℝ) := ht
    rw [ccmGeometricSharpValue, if_pos hmem, one_mul,
      Set.indicator_of_mem hti, hin']
  · have hmem : ¬ (1 : ℝ) ≤ (MellinL2.expMeasurableEquiv t : ℝ) := by
      change ¬ (1 : ℝ) ≤ Real.exp t
      simpa [Real.one_le_exp_iff] using ht
    have hti : t ∉ Ici (0 : ℝ) := ht
    rw [ccmGeometricSharpValue, if_neg hmem, zero_mul,
      Set.indicator_of_notMem hti]

theorem mellinUnitary_ccmGeometricSharpProjection
    (f : CCMMultiplicativeL2) :
    MellinL2.mellinUnitary (ccmGeometricSharpProjection f) =
      ccmHardyProjection (MellinL2.mellinUnitary f) := by
  change dilation MellinL2.spectralNormalization
      MellinL2.spectralNormalization_pos
      (fourierUnitary
        (MellinL2.expPullbackUnitary (ccmGeometricSharpProjection f))) = _
  rw [expPullbackUnitary_ccmGeometricSharpProjection]
  exact (ccmHardyProjection_mellinCore
    (MellinL2.expPullbackUnitary f)).symm

/-! ## Exact phase-product conjugacy -/

/-- The geometric scattering operator as a single unitary conjugate. -/
def ccmArchimedeanGeometricScatteringUnitary :
    CCMMultiplicativeL2 ≃ₗᵢ[ℂ] CCMMultiplicativeL2 :=
  MellinL2.mellinUnitary.trans
    (ccmArchimedeanScatteringL2Unitary.trans MellinL2.mellinUnitary.symm)

theorem ccmArchimedeanGeometricScattering_eq_unitaryCLM :
    ccmArchimedeanGeometricScattering =
      ccmArchimedeanGeometricScatteringUnitary.toLinearIsometry.toContinuousLinearMap :=
  rfl

theorem star_ccmArchimedeanScatteringL2Multiplier :
    star ccmArchimedeanScatteringL2Multiplier =
      ccmArchimedeanScatteringConjL2Multiplier := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
      (ccmArchimedeanScatteringL2Unitary : SoninL2 →L[ℂ] SoninL2) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm ccmArchimedeanScatteringL2Unitary]
  rfl

theorem star_ccmArchimedeanGeometricScattering :
    star ccmArchimedeanGeometricScattering =
      MellinL2.mellinUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
        ccmArchimedeanScatteringConjL2Multiplier ∘L
          MellinL2.mellinUnitary.toLinearIsometry.toContinuousLinearMap := by
  rw [ccmArchimedeanGeometricScattering_eq_unitaryCLM,
    ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
      (ccmArchimedeanGeometricScatteringUnitary :
        CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm
    ccmArchimedeanGeometricScatteringUnitary]
  rfl

theorem mellinUnitary_ccmArchimedeanGeometricScattering
    (f : CCMMultiplicativeL2) :
    MellinL2.mellinUnitary (ccmArchimedeanGeometricScattering f) =
      ccmArchimedeanScatteringL2Multiplier (MellinL2.mellinUnitary f) := by
  change MellinL2.mellinUnitary
      (MellinL2.mellinUnitary.symm
        (ccmArchimedeanScatteringL2Multiplier (MellinL2.mellinUnitary f))) = _
  rw [MellinL2.mellinUnitary.apply_symm_apply]

theorem mellinUnitary_star_ccmArchimedeanGeometricScattering
    (f : CCMMultiplicativeL2) :
    MellinL2.mellinUnitary ((star ccmArchimedeanGeometricScattering) f) =
      ccmArchimedeanScatteringConjL2Multiplier (MellinL2.mellinUnitary f) := by
  rw [star_ccmArchimedeanGeometricScattering]
  change MellinL2.mellinUnitary
      (MellinL2.mellinUnitary.symm
        (ccmArchimedeanScatteringConjL2Multiplier (MellinL2.mellinUnitary f))) = _
  rw [MellinL2.mellinUnitary.apply_symm_apply]

/-- The factor `1/2` and `H=2Q-1` cancel exactly, leaving `u* [Q,u]`. -/
theorem ccmArchimedeanScatteringLogDifferential_apply_eq_projectionCommutator
    (f : SoninL2) :
    ccmArchimedeanScatteringLogDifferential f =
      ccmArchimedeanScatteringConjL2Multiplier
        (ccmHardyProjection (ccmArchimedeanScatteringL2Multiplier f) -
          ccmArchimedeanScatteringL2Multiplier (ccmHardyProjection f)) := by
  unfold ccmArchimedeanScatteringLogDifferential
  change (1 / 2 : ℂ) •
      ccmArchimedeanScatteringConjL2Multiplier
        (ccmHardyInvolution (ccmArchimedeanScatteringL2Multiplier f) -
          ccmArchimedeanScatteringL2Multiplier (ccmHardyInvolution f)) = _
  rw [ccmHardyInvolution_apply, ccmHardyInvolution_apply]
  simp only [map_sub, map_smul]
  module

/-- Exact spectral image of the literal geometric composite `u* [P,u]`. -/
theorem mellinUnitary_ccmArchimedeanGeometricComposite
    (f : CCMMultiplicativeL2) :
    MellinL2.mellinUnitary (ccmArchimedeanGeometricComposite f) =
      ccmArchimedeanScatteringLogDifferential (MellinL2.mellinUnitary f) := by
  rw [ccmArchimedeanScatteringLogDifferential_apply_eq_projectionCommutator]
  unfold ccmArchimedeanGeometricComposite
  change MellinL2.mellinUnitary
      ((star ccmArchimedeanGeometricScattering)
        (ccmGeometricSharpProjection (ccmArchimedeanGeometricScattering f) -
          ccmArchimedeanGeometricScattering (ccmGeometricSharpProjection f))) = _
  rw [mellinUnitary_star_ccmArchimedeanGeometricScattering,
    map_sub,
    mellinUnitary_ccmGeometricSharpProjection,
    mellinUnitary_ccmArchimedeanGeometricScattering,
    mellinUnitary_ccmArchimedeanGeometricScattering,
    mellinUnitary_ccmGeometricSharpProjection]

/-- Literal geometric composite is the normalized-Mellin conjugate of the spectral logarithmic
phase differential. -/
theorem ccmArchimedeanGeometricComposite_eq_mellinConjugate :
    ccmArchimedeanGeometricComposite =
      MellinL2.mellinUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
        ccmArchimedeanScatteringLogDifferential ∘L
          MellinL2.mellinUnitary.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply MellinL2.mellinUnitary.injective
  rw [mellinUnitary_ccmArchimedeanGeometricComposite]
  change _ = MellinL2.mellinUnitary
      (MellinL2.mellinUnitary.symm
        (ccmArchimedeanScatteringLogDifferential (MellinL2.mellinUnitary f)))
  rw [MellinL2.mellinUnitary.apply_symm_apply]

/-- Compatibility with the physical-even realization used by the pre-existing trace-class
theorem. -/
theorem ccmArchimedeanGeometricComposite_evenTransport (f : evenSubspace) :
    ccmArchimedeanGeometricComposite (evenToMultiplicativeHaarUnitary f) =
      evenToMultiplicativeHaarUnitary
        (ccmArchimedeanGeometricScatteringLogDifferential f) := by
  apply MellinL2.mellinUnitary.injective
  rw [mellinUnitary_ccmArchimedeanGeometricComposite]
  change ccmArchimedeanScatteringLogDifferential (archimedeanMellinUnitary f) =
    archimedeanMellinUnitary (ccmArchimedeanGeometricScatteringLogDifferential f)
  change _ = archimedeanMellinUnitary
      (archimedeanMellinUnitary.symm
        (ccmArchimedeanScatteringLogDifferential (archimedeanMellinUnitary f)))
  rw [archimedeanMellinUnitary.apply_symm_apply]

theorem ccmArchimedeanGeometricComposite_eq_evenTransport :
    ccmArchimedeanGeometricComposite =
      evenToMultiplicativeHaarUnitary.toLinearIsometry.toContinuousLinearMap ∘L
        ccmArchimedeanGeometricScatteringLogDifferential ∘L
          evenToMultiplicativeHaarUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  have h := ccmArchimedeanGeometricComposite_evenTransport
    (evenToMultiplicativeHaarUnitary.symm f)
  rw [evenToMultiplicativeHaarUnitary.apply_symm_apply] at h
  exact h

/-! ## Tested literal geometric operator -/

/-- Integrated scaling representation transported to the literal multiplicative-Haar carrier. -/
def ccmMultiplicativeIntegratedScaling (g : CCMLogKernel) :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  evenToMultiplicativeHaarUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    ccmIntegratedScaling g ∘L
      evenToMultiplicativeHaarUnitary.symm.toLinearIsometry.toContinuousLinearMap

/-- Literal tested operator from Proposition `lemsch7(iv)`. -/
def ccmArchimedeanGeometricTestedComposite (g : 𝓢(ℝ, ℂ)) :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  ccmMultiplicativeIntegratedScaling (ccmSchwartzLogKernel g) ∘L
    ccmArchimedeanGeometricComposite

theorem ccmArchimedeanGeometricTestedComposite_eq_evenTransport
    (g : 𝓢(ℝ, ℂ)) :
    ccmArchimedeanGeometricTestedComposite g =
      evenToMultiplicativeHaarUnitary.toLinearIsometry.toContinuousLinearMap ∘L
        (ccmIntegratedScaling (ccmSchwartzLogKernel g) ∘L
          ccmArchimedeanGeometricScatteringLogDifferential) ∘L
            evenToMultiplicativeHaarUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  change evenToMultiplicativeHaarUnitary
      (ccmIntegratedScaling (ccmSchwartzLogKernel g)
        (evenToMultiplicativeHaarUnitary.symm
          (ccmArchimedeanGeometricComposite f))) =
    evenToMultiplicativeHaarUnitary
      (ccmIntegratedScaling (ccmSchwartzLogKernel g)
        (ccmArchimedeanGeometricScatteringLogDifferential
          (evenToMultiplicativeHaarUnitary.symm f)))
  apply congrArg evenToMultiplicativeHaarUnitary
  apply congrArg (ccmIntegratedScaling (ccmSchwartzLogKernel g))
  apply evenToMultiplicativeHaarUnitary.injective
  rw [evenToMultiplicativeHaarUnitary.apply_symm_apply]
  have h := ccmArchimedeanGeometricComposite_evenTransport
    (evenToMultiplicativeHaarUnitary.symm f)
  rw [evenToMultiplicativeHaarUnitary.apply_symm_apply] at h
  exact h

/-- **Proposition `lemsch7(iv)`, literal operator-ideal endpoint.**  The actual geometric
`ρ(g) u* [P,u]` is trace class for every Schwartz logarithmic test; no kernel or trace premise is
assumed. -/
theorem ccmArchimedeanGeometricTestedComposite_isTraceClass (g : 𝓢(ℝ, ℂ)) :
    (ccmArchimedeanGeometricTestedComposite g).IsTraceClass := by
  rw [ccmArchimedeanGeometricTestedComposite_eq_evenTransport]
  exact ccmIsTraceClass_unitaryConjugate evenToMultiplicativeHaarUnitary.symm _
    (ccmIntegratedScaling_mul_geometricScatteringLogDifferential_isTraceClass g)

end RHTower
