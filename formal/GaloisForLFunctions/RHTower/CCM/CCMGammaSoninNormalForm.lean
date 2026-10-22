import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanGeometricSpectralBridge
import GaloisForLFunctions.RHTower.SoninLogShellCocycle
import GaloisForLFunctions.RHTower.SoninBurnolConductorConcrete
import GaloisForLFunctions.RHTower.SoninApertureRestrictionDefect

/-!
# Exact physical normal form of the Gamma scattering differential

The literal Mellin-transported Gamma differential is `A₁ + R₁ - 1`.
This identifies its action on the actual Sonin carrier, without a scalar trace
replacement or an assumption on zeros of zeta.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

private theorem logHalflineCutoff_zero_apply (f : SoninL2) :
    logHalflineCutoff 0 f = f - ccmPositiveHalfLineProjection f := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Iic (0 : ℝ)) measurableSet_Iic f,
    indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f,
    Lp.coeFn_sub f (ccmPositiveHalfLineProjection f),
    volume.ae_ne (0 : ℝ)] with x hleft hright hsub hx
  change (indicatorCutoff (Iic (0 : ℝ)) measurableSet_Iic f) x = _
  rw [hleft, hsub]
  change (Iic (0 : ℝ)).indicator (fun x => f x) x =
    f x - (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) x
  rw [hright]
  rcases lt_or_gt_of_ne hx with hx | hx <;>
    simp [Set.mem_Iic, Set.mem_Ici, hx.le, not_le.mpr hx]

private theorem reflection_positiveHalfLine (f : SoninL2) :
    l2Reflection (ccmPositiveHalfLineProjection f) =
      l2Reflection f - ccmPositiveHalfLineProjection (l2Reflection f) := by
  apply Lp.ext
  have hcut := (indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (ccmPositiveHalfLineProjection f), hcut,
    l2Reflection_ae f,
    indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici (l2Reflection f),
    Lp.coeFn_sub (l2Reflection f) (ccmPositiveHalfLineProjection (l2Reflection f)),
    volume.ae_ne (0 : ℝ)] with x href hcut hf hright hsub hx
  rw [href, hsub]
  change (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici f) (-x) =
    (l2Reflection f) x - (indicatorCutoff (Ici (0 : ℝ)) measurableSet_Ici
      (l2Reflection f)) x
  have hcut' := hcut
  simp only [Function.comp_apply] at hcut'
  rw [hcut', hright]
  rcases lt_or_gt_of_ne hx with hx | hx <;>
    simp [Set.mem_Ici, hx.le, not_le.mpr hx, hf]

/-- Reflection interchanges the actual Hardy projection and its complement. -/
theorem l2Reflection_ccmHardyProjection (f : SoninL2) :
    l2Reflection (ccmHardyProjection f) =
      l2Reflection f - ccmHardyProjection (l2Reflection f) := by
  have hinv : fourierUnitary.symm (l2Reflection f) =
      l2Reflection (fourierUnitary.symm f) := by
    apply fourierUnitary.injective
    rw [fourierUnitary.apply_symm_apply, fourierUnitary_l2Reflection,
      fourierUnitary.apply_symm_apply]
  rw [ccmHardyProjection_apply, ← fourierUnitary_l2Reflection,
    reflection_positiveHalfLine, map_sub, fourierUnitary_l2Reflection,
    fourierUnitary.apply_symm_apply, ccmHardyProjection_apply, hinv]

private theorem archimedeanMellinUnitary_eq_logCore (f : evenSubspace) :
    archimedeanMellinUnitary f =
      dilation MellinL2.spectralNormalization MellinL2.spectralNormalization_pos
        (fourierUnitary (logEvenUnitary f)) := by
  change dilation MellinL2.spectralNormalization MellinL2.spectralNormalization_pos
      (fourierUnitary (MellinL2.expPullbackUnitary
        (MellinL2.expPullbackUnitary.symm (logEvenUnitary f)))) = _
  rw [MellinL2.expPullbackUnitary.apply_symm_apply]

/-- The unit physical cutoff is the complementary Hardy projection in Mellin coordinates. -/
theorem archimedeanMellinUnitary_evenIndicatorCutoff_one (f : evenSubspace) :
    archimedeanMellinUnitary (evenIndicatorCutoff 1 f) =
      archimedeanMellinUnitary f - ccmHardyProjection (archimedeanMellinUnitary f) := by
  rw [archimedeanMellinUnitary_eq_logCore,
    logEvenUnitary_evenIndicatorCutoff 1 zero_lt_one, Real.log_one,
    logHalflineCutoff_zero_apply, map_sub, map_sub,
    archimedeanMellinUnitary_eq_logCore, ccmHardyProjection_mellinCore]

/-- Fourier cutoff becomes the Gamma-conjugated Hardy projection. -/
theorem archimedeanMellinUnitary_evenFourierCutoff_one (f : evenSubspace) :
    archimedeanMellinUnitary (evenFourierCutoff 1 f) =
      ccmArchimedeanScatteringConjL2Multiplier
        (ccmHardyProjection (ccmArchimedeanScatteringL2Multiplier
          (archimedeanMellinUnitary f))) := by
  have hU (v : evenSubspace) :
      ccmArchimedeanScatteringL2Multiplier (archimedeanMellinUnitary v) =
        l2Reflection (archimedeanMellinUnitary (evenFourierTransform v)) := by
    rw [archimedeanMellinUnitary_evenFourierTransform, l2Reflection_involutive]
  apply ccmArchimedeanScatteringL2Unitary.injective
  change ccmArchimedeanScatteringL2Multiplier
      (archimedeanMellinUnitary (evenFourierCutoff 1 f)) =
    ccmArchimedeanScatteringL2Unitary
      (ccmArchimedeanScatteringL2Unitary.symm
        (ccmHardyProjection (ccmArchimedeanScatteringL2Multiplier
          (archimedeanMellinUnitary f))))
  rw [ccmArchimedeanScatteringL2Unitary.apply_symm_apply, hU]
  rw [evenFourierCutoff_eq_reflectedCutoff]
  change l2Reflection (archimedeanMellinUnitary (evenFourierTransform
      (evenFourierTransform (evenIndicatorCutoff 1 (evenFourierTransform f))))) = _
  rw [evenFourierTransform_involutive, archimedeanMellinUnitary_evenIndicatorCutoff_one,
    map_sub, l2Reflection_ccmHardyProjection, sub_sub_cancel,
    ← hU]

/-- Exact operator identity for the existing literal Gamma logarithmic differential. -/
theorem ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs :
    ccmArchimedeanGeometricScatteringLogDifferential =
      evenIndicatorCutoff 1 + evenFourierCutoff 1 - 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply archimedeanMellinUnitary.injective
  change archimedeanMellinUnitary
      (archimedeanMellinUnitary.symm (ccmArchimedeanScatteringLogDifferential
        (archimedeanMellinUnitary f))) = _
  rw [archimedeanMellinUnitary.apply_symm_apply,
    ccmArchimedeanScatteringLogDifferential_apply_eq_projectionCommutator, map_sub]
  have hcancel (x : SoninL2) : ccmArchimedeanScatteringConjL2Multiplier
      (ccmArchimedeanScatteringL2Multiplier x) = x :=
    ccmArchimedeanScatteringL2Unitary.symm_apply_apply x
  rw [hcancel]
  simp only [_root_.sub_apply, _root_.add_apply, one_apply_eq_self,
    map_sub, map_add, archimedeanMellinUnitary_evenIndicatorCutoff_one,
    archimedeanMellinUnitary_evenFourierCutoff_one]
  abel

/-- The Gamma differential acts as minus identity on every Sonin carrier beyond the unit wall. -/
theorem ccmGammaLogDifferential_mul_soninProjection {b : ℝ} (hb : 1 ≤ b) :
    ccmArchimedeanGeometricScatteringLogDifferential * evenCentralSoninProjection b =
      -evenCentralSoninProjection b := by
  have hA : evenIndicatorCutoff 1 * evenCentralSoninProjection b = 0 := by
    rw [← (evenCentralSoninProjection_mul_of_le hb).2, ← mul_assoc,
      evenIndicatorCutoff_mul_evenCentralSoninProjection, zero_mul]
  have hR : evenFourierCutoff 1 * evenCentralSoninProjection b = 0 := by
    rw [← (evenCentralSoninProjection_mul_of_le hb).2, ← mul_assoc,
      evenFourierCutoff_mul_evenCentralSoninProjection, zero_mul]
  rw [ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs,
    sub_mul, add_mul, hA, hR, zero_add, one_mul, zero_sub]

/-- The same reduction holds on the left; the carrier reduces the literal Gamma operator. -/
theorem soninProjection_mul_ccmGammaLogDifferential {b : ℝ} (hb : 1 ≤ b) :
    evenCentralSoninProjection b * ccmArchimedeanGeometricScatteringLogDifferential =
      -evenCentralSoninProjection b := by
  have hA : evenCentralSoninProjection b * evenIndicatorCutoff 1 = 0 := by
    rw [← (evenCentralSoninProjection_mul_of_le hb).1, mul_assoc,
      evenCentralSoninProjection_mul_evenIndicatorCutoff, mul_zero]
  have hR : evenCentralSoninProjection b * evenFourierCutoff 1 = 0 := by
    rw [← (evenCentralSoninProjection_mul_of_le hb).1, mul_assoc,
      evenCentralSoninProjection_mul_evenFourierCutoff, mul_zero]
  rw [ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs,
    mul_sub, mul_add, hA, hR, zero_add, mul_one, zero_sub]

/-- No bare Gamma leakage into a lost aperture layer. -/
theorem soninApertureLayer_mul_ccmGammaLogDifferential_mul_projection
    {a b : ℝ} (hab : a ≤ b) (hb : 1 ≤ b) :
    evenSoninApertureLayer a b * ccmArchimedeanGeometricScatteringLogDifferential *
      evenCentralSoninProjection b = 0 := by
  have hzero : evenSoninApertureLayer a b * evenCentralSoninProjection b = 0 := by
    rw [evenSoninApertureLayer, sub_mul,
    (evenCentralSoninProjection_mul_of_le hab).2,
      (evenCentralSoninProjection_mul_of_le (le_refl b)).1, sub_self]
  rw [mul_assoc, ccmGammaLogDifferential_mul_soninProjection hb]
  apply ContinuousLinearMap.ext
  intro f
  change evenSoninApertureLayer a b (-(evenCentralSoninProjection b f)) = 0
  rw [map_neg]
  have hf := DFunLike.congr_fun hzero f
  change evenSoninApertureLayer a b (evenCentralSoninProjection b f) = 0 at hf
  rw [hf, neg_zero]

/-- Adding a bare Gamma counterterm leaves every source transition unchanged. -/
theorem soninApertureTransition_add_ccmGammaLogDifferential
    (H : evenSubspace →L[ℂ] evenSubspace) (z : ℂ)
    {a b : ℝ} (hab : a ≤ b) (hb : 1 ≤ b) :
    evenSoninApertureLayer a b *
        (H + z • ccmArchimedeanGeometricScatteringLogDifferential) *
        evenCentralSoninProjection b =
      evenSoninApertureLayer a b * H * evenCentralSoninProjection b := by
  apply ContinuousLinearMap.ext
  intro f
  change evenSoninApertureLayer a b
      (H (evenCentralSoninProjection b f) + z •
        ccmArchimedeanGeometricScatteringLogDifferential (evenCentralSoninProjection b f)) = _
  rw [map_add, map_smul]
  have h := DFunLike.congr_fun
    (soninApertureLayer_mul_ccmGammaLogDifferential_mul_projection hab hb) f
  change evenSoninApertureLayer a b
    (ccmArchimedeanGeometricScatteringLogDifferential (evenCentralSoninProjection b f)) = 0 at h
  rw [h, smul_zero, add_zero]
  rfl

/-- The actual tested Gamma term reduces to a continuum dilation source on the Sonin carrier. -/
theorem ccmTestedGammaLogDifferential_mul_soninProjection
    (g : 𝓢(ℝ, ℂ)) {b : ℝ} (hb : 1 ≤ b) :
    (ccmIntegratedScaling (ccmSchwartzLogKernel g) *
        ccmArchimedeanGeometricScatteringLogDifferential) * evenCentralSoninProjection b =
      -(ccmIntegratedScaling (ccmSchwartzLogKernel g) * evenCentralSoninProjection b) := by
  rw [mul_assoc, ccmGammaLogDifferential_mul_soninProjection hb]
  apply ContinuousLinearMap.ext
  intro f
  exact map_neg (ccmIntegratedScaling (ccmSchwartzLogKernel g))
    (evenCentralSoninProjection b f)

/-- Unconditional trace-class regularity of the literal Schwartz continuum source on Sonin. -/
theorem ccmIntegratedScaling_mul_soninProjection_isTraceClass
    (g : 𝓢(ℝ, ℂ)) {b : ℝ} (hb : 1 ≤ b) :
    (ccmIntegratedScaling (ccmSchwartzLogKernel g) *
      evenCentralSoninProjection b).IsTraceClass := by
  rcases ccmIntegratedScaling_mul_geometricScatteringLogDifferential_isTraceClass g with
    ⟨S, V, hS, hV, hfactor⟩
  refine ⟨-S, V ∘L evenCentralSoninProjection b, hS.neg,
    hV.comp_right (evenCentralSoninProjection b), ?_⟩
  have h := ccmTestedGammaLogDifferential_mul_soninProjection g hb
  change (ccmIntegratedScaling (ccmSchwartzLogKernel g) ∘L
      ccmArchimedeanGeometricScatteringLogDifferential) ∘L evenCentralSoninProjection b =
    -(ccmIntegratedScaling (ccmSchwartzLogKernel g) * evenCentralSoninProjection b) at h
  rw [hfactor] at h
  rw [← neg_neg (ccmIntegratedScaling (ccmSchwartzLogKernel g) *
    evenCentralSoninProjection b), ← h]
  rfl

end RHTower
