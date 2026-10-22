import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFourierCrossBlock

/-!
# Trace class of the literal CCM quantized differential

This file transports the explicit positive Hankel factorization through reflection, Hilbert
adjoint, and Fourier conjugation.  It proves both literal Hardy crossblocks Schatten one and hence
the trace-class part of Connes--Consani's `quantsmooth` lemma for `[H,M_f]`, unconditionally for
every Schwartz symbol.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

theorem memSchattenClass_adjoint_iff (p : ℝ) (T : SoninL2 →L[ℂ] SoninL2) :
    MemSchattenClass p (ContinuousLinearMap.adjoint T) ↔ MemSchattenClass p T := by
  rw [← memRectSchattenClass_iff_memSchattenClass,
    ← memRectSchattenClass_iff_memSchattenClass]
  exact memRectSchattenClass_adjoint_iff p T

@[simp] theorem conjSLM_involutive (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (SchwartzMap.conjSLM f) = f := by
  ext x
  simp

theorem inner_ccmSchwartzMultiplier_conj (f : 𝓢(ℝ, ℂ)) (x y : SoninL2) :
    inner ℂ (ccmSchwartzMultiplier (SchwartzMap.conjSLM f) x) y =
      inner ℂ x (ccmSchwartzMultiplier f y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmSchwartzMultiplier_coeFn (SchwartzMap.conjSLM f) x,
    ccmSchwartzMultiplier_coeFn f y] with t hx hy
  rw [hx, hy, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  simp only [SchwartzMap.conjSLM_apply, starRingEnd_self_apply]
  ring

theorem adjoint_ccmSchwartzMultiplier (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.adjoint (ccmSchwartzMultiplier f) =
      ccmSchwartzMultiplier (SchwartzMap.conjSLM f) := by
  symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    (inner_ccmSchwartzMultiplier_conj f)

theorem adjoint_ccmTimeFourierMultiplier (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.adjoint (ccmTimeFourierMultiplier f) =
      ccmTimeFourierMultiplier (SchwartzMap.conjSLM f) := by
  have hU := fourierUnitary.adjoint_eq_symm
  change ContinuousLinearMap.adjoint
      fourierUnitary.toLinearIsometry.toContinuousLinearMap =
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap at hU
  have hUinv := fourierUnitary.symm.adjoint_eq_symm
  change ContinuousLinearMap.adjoint
      fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap =
    fourierUnitary.toLinearIsometry.toContinuousLinearMap at hUinv
  rw [ccmTimeFourierMultiplier, ccmTimeFourierMultiplier]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_ccmSchwartzMultiplier, hU, hUinv]
  rfl

theorem ccm_l2Reflection_ae (v : SoninL2) :
    l2Reflection v =ᵐ[volume] fun x : ℝ => v (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving v
    (Measure.measurePreserving_neg (volume : Measure ℝ))

@[simp] theorem ccm_l2Reflection_involutive (v : SoninL2) :
    l2Reflection (l2Reflection v) = v := by
  apply Lp.ext
  have hinner := (ccm_l2Reflection_ae v).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccm_l2Reflection_ae (l2Reflection v), hinner] with x hout hin
  rw [hout]
  simpa [Function.comp_apply] using hin

/-- Unreflected positive-to-negative time-side crossblock. -/
def ccmTimeUpperCrossBlock (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmPositiveHalfLineProjection ∘L ccmTimeFourierMultiplier f ∘L
    (1 - ccmPositiveHalfLineProjection)

/-- Unreflected negative-to-positive time-side crossblock. -/
def ccmTimeLowerCrossBlock (f : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  (1 - ccmPositiveHalfLineProjection) ∘L ccmTimeFourierMultiplier f ∘L
    ccmPositiveHalfLineProjection

theorem ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection
    (f : 𝓢(ℝ, ℂ)) :
    ccmTimeUpperCrossBlock f = ccmPositiveFourierHankelBlock f ∘L l2Reflection := by
  apply ContinuousLinearMap.ext
  intro v
  simp [ccmTimeUpperCrossBlock, ccmPositiveFourierHankelBlock]

theorem ccmTimeUpperCrossBlock_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1 (ccmTimeUpperCrossBlock f) := by
  rw [ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection,
    ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel]
  exact memSchattenClass_one_comp_right
    (ccmPositiveHankel_memSchattenClass_one (FourierTransform.fourierInv f))
    l2Reflection

theorem adjoint_ccmPositiveHalfLineProjection :
    ContinuousLinearMap.adjoint ccmPositiveHalfLineProjection =
      ccmPositiveHalfLineProjection := by
  exact ccmPositiveHalfLineProjection_isStarProjection.isSelfAdjoint.star_eq

theorem adjoint_one_sub_ccmPositiveHalfLineProjection :
    ContinuousLinearMap.adjoint (1 - ccmPositiveHalfLineProjection) =
      1 - ccmPositiveHalfLineProjection := by
  rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
    adjoint_ccmPositiveHalfLineProjection]

theorem adjoint_ccmTimeUpperCrossBlock_conj (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.adjoint
        (ccmTimeUpperCrossBlock (SchwartzMap.conjSLM f)) =
      ccmTimeLowerCrossBlock f := by
  rw [ccmTimeUpperCrossBlock, ccmTimeLowerCrossBlock]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_ccmPositiveHalfLineProjection,
    adjoint_one_sub_ccmPositiveHalfLineProjection,
    adjoint_ccmTimeFourierMultiplier, conjSLM_involutive]
  rfl

theorem ccmTimeLowerCrossBlock_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1 (ccmTimeLowerCrossBlock f) := by
  have hu := ccmTimeUpperCrossBlock_memSchattenClass_one
    (SchwartzMap.conjSLM f)
  have hadj := (memSchattenClass_adjoint_iff 1
    (ccmTimeUpperCrossBlock (SchwartzMap.conjSLM f))).2 hu
  rw [adjoint_ccmTimeUpperCrossBlock_conj] at hadj
  exact hadj

/-- Fourier conjugation transports the time upper-right block to the literal Hardy upper-right
block in the Connes--Consani quantized differential. -/
theorem ccmHardyUpperCrossBlock_eq_fourierConjugate (f : 𝓢(ℝ, ℂ)) :
    ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection) =
      fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
        ccmTimeUpperCrossBlock f ∘L
          fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  let z : SoninL2 := fourierUnitary.symm v
  have hv : v = fourierUnitary z := by
    exact (fourierUnitary.apply_symm_apply v).symm
  rw [hv]
  simp [ccmHardyProjection_apply, ccmTimeUpperCrossBlock,
    ccmTimeFourierMultiplier_apply, map_sub]

/-- Fourier conjugation transports the time lower-left block to the literal Hardy lower-left
block. -/
theorem ccmHardyLowerCrossBlock_eq_fourierConjugate (f : 𝓢(ℝ, ℂ)) :
    (1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection =
      fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
        ccmTimeLowerCrossBlock f ∘L
          fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  let z : SoninL2 := fourierUnitary.symm v
  have hv : v = fourierUnitary z := by
    exact (fourierUnitary.apply_symm_apply v).symm
  rw [hv]
  simp [ccmHardyProjection_apply, ccmTimeLowerCrossBlock,
    ccmTimeFourierMultiplier_apply]

theorem ccmHardyUpperCrossBlock_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1
      (ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection)) := by
  rw [ccmHardyUpperCrossBlock_eq_fourierConjugate]
  exact memSchattenClass_one_comp_right
    (memSchattenClass_one_comp_left
      (ccmTimeUpperCrossBlock_memSchattenClass_one f)
      fourierUnitary.toLinearIsometry.toContinuousLinearMap)
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmHardyLowerCrossBlock_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1
      ((1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection) := by
  rw [ccmHardyLowerCrossBlock_eq_fourierConjugate]
  exact memSchattenClass_one_comp_right
    (memSchattenClass_one_comp_left
      (ccmTimeLowerCrossBlock_memSchattenClass_one f)
      fourierUnitary.toLinearIsometry.toContinuousLinearMap)
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap

theorem ccmHardyCrossBlockDifference_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1
      (ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection) -
        (1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection) := by
  let U : SoninL2 →L[ℂ] SoninL2 :=
    ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection)
  let L : SoninL2 →L[ℂ] SoninL2 :=
    (1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection
  have hU : MemSchattenClass 1 U := ccmHardyUpperCrossBlock_memSchattenClass_one f
  have hL : MemSchattenClass 1 L := ccmHardyLowerCrossBlock_memSchattenClass_one f
  have hneg : MemSchattenClass 1 (-L) := by
    simpa using memSchattenClass_one_smul hL (-1 : ℂ)
  have hadd := memSchattenClass_one_add (hU.isCompactOperator one_pos)
    (hneg.isCompactOperator one_pos) hU hneg
  simpa [U, L, sub_eq_add_neg] using hadd

/-- **Connes--Consani `quantsmooth`, trace-class part.** For every Schwartz symbol, the literal
quantized differential `[H,M_f]` is Schatten one, with no analytic premise exposed. -/
theorem ccmQuantizedDifferential_memSchattenClass_one (f : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1 (ccmQuantizedDifferential f) := by
  rw [ccmQuantizedDifferential_eq_two_smul_crossBlocks]
  exact memSchattenClass_one_smul
    (ccmHardyCrossBlockDifference_memSchattenClass_one f) 2

end RHTower
