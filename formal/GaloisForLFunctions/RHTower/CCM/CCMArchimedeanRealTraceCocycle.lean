import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanHankelProductTrace
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedTrace
import GaloisForLFunctions.HTGeometry.SchwartzPolynomialDifferentialFrame
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen

/-!
# Real-line trace cocycle for the CCM quantized differential

This file derives the tested real-line Hardy commutator trace from actual trace-class Hankel
products.  It contains no diagonal-kernel trace postulate.  The two time-side crossblock products
are reduced to literal positive Hankel products, whose traces were proved by Hilbert--Schmidt
cyclicity and a measure-preserving quadrant shear.

This is classical Helton--Howe/Connes--Consani infrastructure and carries no novelty claim.
-/

noncomputable section

open Complex ContinuousLinearMap FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower


/-- Kernel of the reflected lower time-side Hankel block. -/
def ccmLowerHankelKernel (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.conjSLM
    (FourierTransform.fourierInv (SchwartzMap.conjSLM f))

/-- The lower Hankel kernel is the spatial reflection of the inverse Fourier transform. -/
theorem ccmLowerHankelKernel_eq_reflect_fourierInv (f : 𝓢(ℝ, ℂ)) :
    ccmLowerHankelKernel f =
      ccmReflectSchwartz (FourierTransform.fourierInv f) := by
  apply SchwartzMap.ext
  intro x
  rw [ccmLowerHankelKernel, SchwartzMap.conjSLM_apply,
    ccmReflectSchwartz_apply]
  rw [SchwartzMap.fourierInv_apply_eq]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply]
  have hinv : FourierTransform.fourierInv f (-x) =
      FourierTransform.fourier f x := by
    have h := congrArg (fun u : 𝓢(ℝ, ℂ) => u (-x))
      (SchwartzMap.fourierInv_apply_eq f)
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] at h
    change FourierTransform.fourierInv f (-x) =
      FourierTransform.fourier f (-(-x)) at h
    simpa only [neg_neg] using h
  rw [hinv]
  change (starRingEnd ℂ)
      (FourierTransform.fourier (SchwartzMap.conjSLM f) (-x)) =
    FourierTransform.fourier f x
  have h := SchwartzMap.fourier_conjugateReflectionSchwartz
    (ccmReflectSchwartz f) (-x)
  have hcr : SchwartzMap.conjugateReflectionSchwartz
      (ccmReflectSchwartz f) = SchwartzMap.conjSLM f := by
    apply SchwartzMap.ext
    intro y
    simp [SchwartzMap.conjugateReflectionSchwartz]
  rw [hcr] at h
  rw [h]
  change star (star (FourierTransform.fourier (ccmReflectSchwartz f) (-x))) = _
  rw [star_star]
  rw [SchwartzMap.fourier_coe]
  change FourierTransform.fourier
      ((f : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)) (-x) = _
  rw [Real.fourier_comp_linearIsometry]
  simp
  rfl

/-- Antisymmetrizing the two positive-half-line first moments recovers one full-line signed
moment.  This is the exact change-of-variables step hidden in the formal kernel computation. -/
theorem ccmPositive_firstMoment_antisymmetrization (A B : 𝓢(ℝ, ℂ)) :
    ((∫ t, (t : ℂ) * B t * A (-t) ∂ccmPositiveMeasure) -
      ∫ t, (t : ℂ) * B (-t) * A t ∂ccmPositiveMeasure) =
    -∫ t : ℝ, (t : ℂ) * A t * B (-t) := by
  let C : 𝓢(ℝ, ℂ) := SchwartzMap.pointwiseMul
    (GaloisForLFunctions.mulXCLM A) (ccmReflectSchwartz B)
  have hCfun : (fun t : ℝ => (t : ℂ) * A t * B (-t)) =
      (C : ℝ → ℂ) := by
    funext t
    simp [C, GaloisForLFunctions.mulXCLM_apply]
  have hCint : Integrable (fun t : ℝ => (t : ℂ) * A t * B (-t)) := by
    rw [hCfun]
    exact C.integrable
  have hsplit :
      (∫ t : ℝ, (t : ℂ) * A t * B (-t)) =
        (∫ t : ℝ in Iic 0, (t : ℂ) * A t * B (-t)) +
          ∫ t : ℝ in Ioi 0, (t : ℂ) * A t * B (-t) := by
    have h := integral_union_ae
      (Set.Iic_disjoint_Ioi (a := (0 : ℝ)) (b := 0) le_rfl).aedisjoint
      measurableSet_Ioi.nullMeasurableSet
      hCint.integrableOn hCint.integrableOn
    simpa only [Set.Iic_union_Ioi, Measure.restrict_univ] using h
  have hfirst :
      (∫ t, (t : ℂ) * B t * A (-t) ∂ccmPositiveMeasure) =
        -∫ t : ℝ in Iic 0, (t : ℂ) * A t * B (-t) := by
    rw [← setIntegral_Ici_eq_ccmPositive, integral_Ici_eq_integral_Ioi]
    have hneg := integral_comp_neg_Iic (0 : ℝ)
      (fun t : ℝ => (t : ℂ) * B t * A (-t))
    have hfun :
        (fun t : ℝ => ((-t : ℝ) : ℂ) * B (-t) * A (-(-t))) =
          fun t : ℝ => -((t : ℂ) * A t * B (-t)) := by
      funext t
      push_cast
      ring
    rw [hfun, integral_neg] at hneg
    simpa only [neg_zero] using hneg.symm
  have hsecond :
      (∫ t, (t : ℂ) * B (-t) * A t ∂ccmPositiveMeasure) =
        ∫ t : ℝ in Ioi 0, (t : ℂ) * A t * B (-t) := by
    rw [← setIntegral_Ici_eq_ccmPositive, integral_Ici_eq_integral_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    ring
  rw [hfirst, hsecond, hsplit]
  abel

/-- Differential Schwartz function whose Fourier transform is coordinate multiplication. -/
def ccmCocycleDerivative (b : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (-I) • SchwartzMap.normalizedDerivativeCLM b

@[simp] theorem ccmCocycleDerivative_apply (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ccmCocycleDerivative b x =
      (2 * (Real.pi : ℂ) * I)⁻¹ * deriv (b : ℝ → ℂ) x := by
  simp only [ccmCocycleDerivative, SchwartzMap.normalizedDerivativeCLM,
    _root_.smul_apply, smul_eq_mul, SchwartzMap.derivCLM_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  rw [I_sq]
  push_cast
  ring

theorem fourier_ccmCocycleDerivative_apply (b : 𝓢(ℝ, ℂ)) (t : ℝ) :
    FourierTransform.fourier (ccmCocycleDerivative b) t =
      (t : ℂ) * FourierTransform.fourier b t := by
  rw [ccmCocycleDerivative, FourierTransform.fourier_smul,
    _root_.smul_apply, SchwartzMap.fourier_normalizedDerivativeCLM_apply]
  simp only [smul_eq_mul]
  calc
    -I * ((t : ℂ) * I * FourierTransform.fourier b t) =
        ((-I) * I) * ((t : ℂ) * FourierTransform.fourier b t) := by ring
    _ = (t : ℂ) * FourierTransform.fourier b t := by simp

/-- Bilinear Parseval identity converting CCM signed Hankel moment into local derivative pairing. -/
theorem ccmFourier_signedMoment_eq_derivativePairing (a b : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, (t : ℂ) * FourierTransform.fourierInv a t *
        FourierTransform.fourierInv b (-t)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∫ x : ℝ, a x * deriv (b : ℝ → ℂ) x := by
  let g : 𝓢(ℝ, ℂ) := ccmCocycleDerivative b
  have hinv (t : ℝ) : FourierTransform.fourierInv b (-t) =
      FourierTransform.fourier b t := by
    have h := congrArg (fun u : 𝓢(ℝ, ℂ) => u (-t))
      (SchwartzMap.fourierInv_apply_eq b)
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] at h
    change FourierTransform.fourierInv b (-t) =
      FourierTransform.fourier b (-(-t)) at h
    simpa only [neg_neg] using h
  have hmoment :
      (∫ t : ℝ, (t : ℂ) * FourierTransform.fourierInv a t *
          FourierTransform.fourierInv b (-t)) =
        ∫ t : ℝ, FourierTransform.fourierInv a t *
          FourierTransform.fourier g t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [hinv, fourier_ccmCocycleDerivative_apply]
    ring
  have hparseval := SchwartzMap.integral_fourierInv_mul_eq a
    (FourierTransform.fourier g)
  rw [FourierTransform.fourierInv_fourier_eq] at hparseval
  rw [hmoment, hparseval]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [show g x = ccmCocycleDerivative b x by rfl,
    ccmCocycleDerivative_apply]
  ring

/-- The literal lower time crossblock is reflection followed by a positive Hankel block. -/
theorem ccmTimeLowerCrossBlock_eq_reflection_comp_positiveHankel
    (f : 𝓢(ℝ, ℂ)) :
    ccmTimeLowerCrossBlock f =
      l2Reflection ∘L ccmPositiveHankel (ccmLowerHankelKernel f) := by
  rw [← adjoint_ccmTimeUpperCrossBlock_conj f,
    ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection,
    ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel,
    ContinuousLinearMap.adjoint_comp,
    adjoint_ccmL2Reflection,
    adjoint_ccmPositiveHankel]
  rfl

theorem ccmTimeUpperCrossBlock_eq_positiveHankel_comp_reflection
    (f : 𝓢(ℝ, ℂ)) :
    ccmTimeUpperCrossBlock f =
      ccmPositiveHankel (FourierTransform.fourierInv f) ∘L l2Reflection := by
  rw [ccmTimeUpperCrossBlock_eq_positiveBlock_comp_reflection,
    ccmPositiveFourierHankelBlock_eq_ccmPositiveHankel]

private theorem ccmL2Reflection_comp_self :
    l2Reflection ∘L l2Reflection = (1 : SoninL2 →L[ℂ] SoninL2) := by
  apply ContinuousLinearMap.ext
  intro v
  exact ccm_l2Reflection_involutive v

theorem opTrace_ccmTimeUpper_comp_lower (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmTimeUpperCrossBlock b ∘L ccmTimeLowerCrossBlock a) =
      ∫ t, (t : ℂ) * FourierTransform.fourierInv b t *
        ccmLowerHankelKernel a t ∂ccmPositiveMeasure := by
  rw [ccmTimeUpperCrossBlock_eq_positiveHankel_comp_reflection,
    ccmTimeLowerCrossBlock_eq_reflection_comp_positiveHankel]
  have hop :
      (ccmPositiveHankel (FourierTransform.fourierInv b) ∘L l2Reflection) ∘L
          (l2Reflection ∘L ccmPositiveHankel (ccmLowerHankelKernel a)) =
        ccmPositiveHankel (FourierTransform.fourierInv b) ∘L
          ccmPositiveHankel (ccmLowerHankelKernel a) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply]
    rw [ccm_l2Reflection_involutive]
  rw [hop, opTrace_ccmPositiveHankel_comp]

theorem opTrace_ccmTimeLower_comp_upper (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmTimeLowerCrossBlock b ∘L ccmTimeUpperCrossBlock a) =
      ∫ t, (t : ℂ) * ccmLowerHankelKernel b t *
        FourierTransform.fourierInv a t ∂ccmPositiveMeasure := by
  rw [ccmTimeLowerCrossBlock_eq_reflection_comp_positiveHankel,
    ccmTimeUpperCrossBlock_eq_positiveHankel_comp_reflection]
  have hleft :
      (l2Reflection ∘L ccmPositiveHankel (ccmLowerHankelKernel b)).IsHilbertSchmidt :=
    (ccmPositiveHankel_isHilbertSchmidt (ccmLowerHankelKernel b)).comp_left
      l2Reflection
  have hright :
      (ccmPositiveHankel (FourierTransform.fourierInv a) ∘L
        l2Reflection).IsHilbertSchmidt :=
    (ccmPositiveHankel_isHilbertSchmidt
      (FourierTransform.fourierInv a)).comp_right l2Reflection
  calc
    opTrace
        ((l2Reflection ∘L ccmPositiveHankel (ccmLowerHankelKernel b)) ∘L
          (ccmPositiveHankel (FourierTransform.fourierInv a) ∘L l2Reflection)) =
      opTrace
        ((ccmPositiveHankel (FourierTransform.fourierInv a) ∘L l2Reflection) ∘L
          (l2Reflection ∘L ccmPositiveHankel (ccmLowerHankelKernel b))) :=
      ContinuousLinearMap.opTrace_comp_comm hleft hright
    _ = opTrace
        (ccmPositiveHankel (FourierTransform.fourierInv a) ∘L
          ccmPositiveHankel (ccmLowerHankelKernel b)) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply]
      rw [ccm_l2Reflection_involutive]
    _ = ∫ t, (t : ℂ) * FourierTransform.fourierInv a t *
        ccmLowerHankelKernel b t ∂ccmPositiveMeasure :=
      opTrace_ccmPositiveHankel_comp _ _
    _ = ∫ t, (t : ℂ) * ccmLowerHankelKernel b t *
        FourierTransform.fourierInv a t ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with t
      ring

theorem opTrace_fourierConjugate_of_memSchattenClass_one
    (T : SoninL2 →L[ℂ] SoninL2) (hT : MemSchattenClass 1 T) :
    opTrace
        (fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
          fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap) =
      opTrace T := by
  let U := fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let V := fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  have hTV : MemSchattenClass 1 (T ∘L V) :=
    memSchattenClass_one_comp_right hT V
  have hcyc := hTV.one_opTrace_comp_comm U
  calc
    opTrace (U ∘L T ∘L V) = opTrace ((T ∘L V) ∘L U) := hcyc
    _ = opTrace T := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.comp_apply, U, V]
      change T (fourierUnitary.symm (fourierUnitary x)) = T x
      rw [fourierUnitary.symm_apply_apply]

private theorem opTrace_ccmHardyMultiplier_upper_eq_upper_lower
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a *
        (ccmHardyProjection * ccmSchwartzMultiplier b * (1 - ccmHardyProjection))) =
      opTrace ((ccmHardyProjection * ccmSchwartzMultiplier b *
          (1 - ccmHardyProjection)) *
        ((1 - ccmHardyProjection) * ccmSchwartzMultiplier a *
          ccmHardyProjection)) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := ccmHardyProjection
  let A : SoninL2 →L[ℂ] SoninL2 := ccmSchwartzMultiplier a
  let B : SoninL2 →L[ℂ] SoninL2 := ccmSchwartzMultiplier b
  let U : SoninL2 →L[ℂ] SoninL2 := Q * B * (1 - Q)
  let L : SoninL2 →L[ℂ] SoninL2 := (1 - Q) * A * Q
  have hQ : Q * Q = Q := by
    change ccmHardyProjection * ccmHardyProjection = ccmHardyProjection
    exact ccmHardyProjection_idempotent
  have hU : MemSchattenClass 1 U := by
    simpa only [Q, B, U] using
      ccmHardyUpperCrossBlock_memSchattenClass_one b
  have hQU : Q * U = U := by
    dsimp only [U]
    rw [← mul_assoc Q (Q * B) (1 - Q), ← mul_assoc Q Q B, hQ]
  have hUQ : U * Q = 0 := by
    dsimp only [U]
    rw [mul_assoc, show (1 - Q) * Q = 0 by noncomm_ring [hQ], mul_zero]
  have hUA : MemSchattenClass 1 (U * A) :=
    memSchattenClass_one_comp_right hU A
  have hdiag : opTrace (Q * (U * A)) = opTrace ((U * A) * Q) := by
    simpa only [ContinuousLinearMap.mul_def] using hUA.one_opTrace_comp_comm Q
  calc
    opTrace (A * U) = opTrace (U * A) := by
      simpa only [ContinuousLinearMap.mul_def] using hU.one_opTrace_comp_comm A
    _ = opTrace (Q * (U * A)) := by rw [← mul_assoc, hQU]
    _ = opTrace ((U * A) * Q) := hdiag
    _ = opTrace (U * L) := by
      congr 1
      dsimp only [L]
      have hUP : U * (1 - Q) = U := by
        rw [mul_sub, mul_one, hUQ, sub_zero]
      calc
        U * A * Q = (U * (1 - Q)) * A * Q := by rw [hUP]
        _ = U * ((1 - Q) * A * Q) := by simp only [mul_assoc]

private theorem opTrace_ccmHardyMultiplier_lower_eq_lower_upper
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a *
        ((1 - ccmHardyProjection) * ccmSchwartzMultiplier b * ccmHardyProjection)) =
      opTrace (((1 - ccmHardyProjection) * ccmSchwartzMultiplier b *
          ccmHardyProjection) *
        (ccmHardyProjection * ccmSchwartzMultiplier a *
          (1 - ccmHardyProjection))) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := ccmHardyProjection
  let A : SoninL2 →L[ℂ] SoninL2 := ccmSchwartzMultiplier a
  let B : SoninL2 →L[ℂ] SoninL2 := ccmSchwartzMultiplier b
  let L : SoninL2 →L[ℂ] SoninL2 := (1 - Q) * B * Q
  let U : SoninL2 →L[ℂ] SoninL2 := Q * A * (1 - Q)
  have hQ : Q * Q = Q := by
    change ccmHardyProjection * ccmHardyProjection = ccmHardyProjection
    exact ccmHardyProjection_idempotent
  have hL : MemSchattenClass 1 L := by
    simpa only [Q, B, L] using
      ccmHardyLowerCrossBlock_memSchattenClass_one b
  have hPL : (1 - Q) * L = L := by
    dsimp only [L]
    have hP : (1 - Q) * (1 - Q) = 1 - Q := by noncomm_ring [hQ]
    rw [← mul_assoc (1 - Q) ((1 - Q) * B) Q,
      ← mul_assoc (1 - Q) (1 - Q) B, hP]
  have hLQ : L * Q = L := by
    dsimp only [L]
    rw [mul_assoc, hQ]
  have hLA : MemSchattenClass 1 (L * A) :=
    memSchattenClass_one_comp_right hL A
  have hdiag : opTrace ((1 - Q) * (L * A)) =
      opTrace ((L * A) * (1 - Q)) := by
    simpa only [ContinuousLinearMap.mul_def] using
      hLA.one_opTrace_comp_comm (1 - Q)
  calc
    opTrace (A * L) = opTrace (L * A) := by
      simpa only [ContinuousLinearMap.mul_def] using hL.one_opTrace_comp_comm A
    _ = opTrace ((1 - Q) * (L * A)) := by rw [← mul_assoc, hPL]
    _ = opTrace ((L * A) * (1 - Q)) := hdiag
    _ = opTrace (L * U) := by
      congr 1
      dsimp only [U]
      calc
        L * A * (1 - Q) = (L * Q) * A * (1 - Q) := by rw [hLQ]
        _ = L * (Q * A * (1 - Q)) := by simp only [mul_assoc]

/-- Tested Hardy commutator trace reduces exactly to two crossblock-product traces. -/
theorem opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_crossBlocks
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a * ccmQuantizedDifferential b) =
      (2 : ℂ) *
        (opTrace
            ((ccmHardyProjection * ccmSchwartzMultiplier b *
                (1 - ccmHardyProjection)) *
              ((1 - ccmHardyProjection) * ccmSchwartzMultiplier a *
                ccmHardyProjection)) -
          opTrace
            (((1 - ccmHardyProjection) * ccmSchwartzMultiplier b *
                ccmHardyProjection) *
              (ccmHardyProjection * ccmSchwartzMultiplier a *
                (1 - ccmHardyProjection)))) := by
  let U : SoninL2 →L[ℂ] SoninL2 :=
    ccmHardyProjection * ccmSchwartzMultiplier b * (1 - ccmHardyProjection)
  let L : SoninL2 →L[ℂ] SoninL2 :=
    (1 - ccmHardyProjection) * ccmSchwartzMultiplier b * ccmHardyProjection
  have hAU : MemSchattenClass 1 (ccmSchwartzMultiplier a * U) :=
    memSchattenClass_one_comp_left
      (by simpa only [U] using
        ccmHardyUpperCrossBlock_memSchattenClass_one b)
      (ccmSchwartzMultiplier a)
  have hAL : MemSchattenClass 1 (ccmSchwartzMultiplier a * L) :=
    memSchattenClass_one_comp_left
      (by simpa only [L] using
        ccmHardyLowerCrossBlock_memSchattenClass_one b)
      (ccmSchwartzMultiplier a)
  rw [ccmQuantizedDifferential_eq_two_smul_crossBlocks,
    mul_smul_comm, mul_sub,
    opTrace_smul, opTrace_sub_of_memSchattenClass_one hAU hAL,
    opTrace_ccmHardyMultiplier_upper_eq_upper_lower,
    opTrace_ccmHardyMultiplier_lower_eq_lower_upper]

theorem opTrace_ccmHardyUpper_comp_lower_eq_time
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace
        ((ccmHardyProjection * ccmSchwartzMultiplier b *
            (1 - ccmHardyProjection)) *
          ((1 - ccmHardyProjection) * ccmSchwartzMultiplier a *
            ccmHardyProjection)) =
      opTrace (ccmTimeUpperCrossBlock b ∘L ccmTimeLowerCrossBlock a) := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    ccmTimeUpperCrossBlock b ∘L ccmTimeLowerCrossBlock a
  have hT : MemSchattenClass 1 T :=
    memSchattenClass_one_comp_right
      (ccmTimeUpperCrossBlock_memSchattenClass_one b)
      (ccmTimeLowerCrossBlock a)
  have hop :
      (ccmHardyProjection * ccmSchwartzMultiplier b *
          (1 - ccmHardyProjection)) *
        ((1 - ccmHardyProjection) * ccmSchwartzMultiplier a *
          ccmHardyProjection) =
      fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
    rw [ccmHardyUpperCrossBlock_eq_fourierConjugate,
      ccmHardyLowerCrossBlock_eq_fourierConjugate]
    apply ContinuousLinearMap.ext
    intro x
    change fourierUnitary
        (ccmTimeUpperCrossBlock b
          (fourierUnitary.symm
            (fourierUnitary
              (ccmTimeLowerCrossBlock a (fourierUnitary.symm x))))) =
      fourierUnitary
        (ccmTimeUpperCrossBlock b
          (ccmTimeLowerCrossBlock a (fourierUnitary.symm x)))
    rw [fourierUnitary.symm_apply_apply]
  rw [hop]
  exact opTrace_fourierConjugate_of_memSchattenClass_one T hT

theorem opTrace_ccmHardyLower_comp_upper_eq_time
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace
        (((1 - ccmHardyProjection) * ccmSchwartzMultiplier b *
            ccmHardyProjection) *
          (ccmHardyProjection * ccmSchwartzMultiplier a *
            (1 - ccmHardyProjection))) =
      opTrace (ccmTimeLowerCrossBlock b ∘L ccmTimeUpperCrossBlock a) := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    ccmTimeLowerCrossBlock b ∘L ccmTimeUpperCrossBlock a
  have hT : MemSchattenClass 1 T :=
    memSchattenClass_one_comp_right
      (ccmTimeLowerCrossBlock_memSchattenClass_one b)
      (ccmTimeUpperCrossBlock a)
  have hop :
      ((1 - ccmHardyProjection) * ccmSchwartzMultiplier b *
          ccmHardyProjection) *
        (ccmHardyProjection * ccmSchwartzMultiplier a *
          (1 - ccmHardyProjection)) =
      fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L T ∘L
        fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap := by
    rw [ccmHardyLowerCrossBlock_eq_fourierConjugate,
      ccmHardyUpperCrossBlock_eq_fourierConjugate]
    apply ContinuousLinearMap.ext
    intro x
    change fourierUnitary
        (ccmTimeLowerCrossBlock b
          (fourierUnitary.symm
            (fourierUnitary
              (ccmTimeUpperCrossBlock a (fourierUnitary.symm x))))) =
      fourierUnitary
        (ccmTimeLowerCrossBlock b
          (ccmTimeUpperCrossBlock a (fourierUnitary.symm x)))
    rw [fourierUnitary.symm_apply_apply]
  rw [hop]
  exact opTrace_fourierConjugate_of_memSchattenClass_one T hT

/-- **Real-line Hardy trace cocycle in exact Hankel first-moment form.** -/
theorem opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_firstMoments
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a * ccmQuantizedDifferential b) =
      (2 : ℂ) *
        ((∫ t, (t : ℂ) * FourierTransform.fourierInv b t *
            ccmLowerHankelKernel a t ∂ccmPositiveMeasure) -
          ∫ t, (t : ℂ) * ccmLowerHankelKernel b t *
            FourierTransform.fourierInv a t ∂ccmPositiveMeasure) := by
  rw [opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_crossBlocks,
    opTrace_ccmHardyUpper_comp_lower_eq_time,
    opTrace_ccmHardyLower_comp_upper_eq_time,
    opTrace_ccmTimeUpper_comp_lower,
    opTrace_ccmTimeLower_comp_upper]

/-- Real-line Hardy trace cocycle as one full-line Fourier first moment. -/
theorem opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_signedMoment
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a * ccmQuantizedDifferential b) =
      -(2 : ℂ) *
        ∫ t : ℝ, (t : ℂ) * FourierTransform.fourierInv a t *
          FourierTransform.fourierInv b (-t) := by
  rw [opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_firstMoments,
    ccmLowerHankelKernel_eq_reflect_fourierInv,
    ccmLowerHankelKernel_eq_reflect_fourierInv]
  simp only [ccmReflectSchwartz_apply]
  rw [ccmPositive_firstMoment_antisymmetrization]
  ring

/-- **Exact local CCM/Helton--Howe trace cocycle.**  The proof passes through actual trace-class
Hankel products and bilinear Parseval; it uses no diagonal-kernel trace formula. -/
theorem opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_local
    (a b : 𝓢(ℝ, ℂ)) :
    opTrace (ccmSchwartzMultiplier a * ccmQuantizedDifferential b) =
      (I / (Real.pi : ℂ)) *
        ∫ x : ℝ, a x * deriv (b : ℝ → ℂ) x := by
  rw [opTrace_ccmSchwartzMultiplier_comp_quantizedDifferential_signedMoment,
    ccmFourier_signedMoment_eq_derivativePairing]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : -(2 : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ =
      I / (Real.pi : ℂ) := by
    field_simp [hpi]
    exact I_sq.symm
  rw [← mul_assoc, hc]

end RHTower
