import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseOperatorProduct
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedTrace

/-!
# Exact trace reduction for the CCM archimedean phase

This file removes the traceless Leibniz term from the literal tested phase differential.  It uses
only the already-proved Schatten-one estimates, bounded trace cyclicity, and the exact inverse law
for the unit-modulus Gamma scattering multiplier.  Thus the remaining trace problem is a single
weighted quantized differential, rather than a formal diagonal-kernel assertion.
-/

noncomputable section

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

/-- Multiplication by the conjugate Gamma phase is the left inverse of multiplication by the
Gamma phase. -/
theorem ccmArchimedeanScatteringConj_mul_scattering_eq_one :
    ccmArchimedeanScatteringConjL2Multiplier *
        ccmArchimedeanScatteringL2Multiplier = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmArchimedeanScatteringL2Unitary.symm
      (ccmArchimedeanScatteringL2Unitary x) = x
  exact ccmArchimedeanScatteringL2Unitary.symm_apply_apply x

/-- Multiplication by the conjugate Gamma phase is also the right inverse. -/
theorem ccmArchimedeanScattering_mul_scatteringConj_eq_one :
    ccmArchimedeanScatteringL2Multiplier *
        ccmArchimedeanScatteringConjL2Multiplier = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmArchimedeanScatteringL2Unitary
      (ccmArchimedeanScatteringL2Unitary.symm x) = x
  exact ccmArchimedeanScatteringL2Unitary.apply_symm_apply x

/-- The conjugated Leibniz remainder has zero ordinary operator trace. -/
theorem opTrace_scatteringConj_mul_quantizedDifferential_mul_scattering_eq_zero
    (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmArchimedeanScatteringConjL2Multiplier *
          (ccmQuantizedDifferential g *
            ccmArchimedeanScatteringL2Multiplier)) = 0 := by
  let D : SoninL2 →L[ℂ] SoninL2 := ccmQuantizedDifferential g
  let U : SoninL2 →L[ℂ] SoninL2 := ccmArchimedeanScatteringL2Multiplier
  let C : SoninL2 →L[ℂ] SoninL2 := ccmArchimedeanScatteringConjL2Multiplier
  have hD : MemSchattenClass 1 D := ccmQuantizedDifferential_memSchattenClass_one g
  have hDU : MemSchattenClass 1 (D * U) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hD U
  have hcyc := hDU.one_opTrace_comp_comm C
  have hcycle : ContinuousLinearMap.opTrace (C * (D * U)) =
      ContinuousLinearMap.opTrace ((D * U) * C) := by
    simpa only [ContinuousLinearMap.mul_def] using hcyc
  have hUC : U * C = 1 := by
    simpa only [U, C] using ccmArchimedeanScattering_mul_scatteringConj_eq_one
  rw [mul_assoc, hUC, mul_one, opTrace_ccmQuantizedDifferential_eq_zero] at hcycle
  simpa only [C, D, U] using hcycle

/-- **Exact non-formal reduction of Connes--Consani Proposition 7(iv).**  The ordinary trace of
the literal tested logarithmic phase differential is half the trace of one weighted quantized
differential.  The second Leibniz term vanishes by cyclicity; no diagonal-kernel trace rule is
assumed. -/
theorem opTrace_ccmSchwartzMultiplier_mul_scatteringLogDifferential_eq_reduced
    (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmSchwartzMultiplier g * ccmArchimedeanScatteringLogDifferential) =
      (1 / 2 : ℂ) * ContinuousLinearMap.opTrace
        (ccmArchimedeanScatteringConjL2Multiplier *
          ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)) := by
  let A : SoninL2 →L[ℂ] SoninL2 :=
    ccmArchimedeanScatteringConjL2Multiplier *
      ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g)
  let B : SoninL2 →L[ℂ] SoninL2 :=
    ccmArchimedeanScatteringConjL2Multiplier *
      (ccmQuantizedDifferential g * ccmArchimedeanScatteringL2Multiplier)
  have hA : MemSchattenClass 1 A := by
    simpa only [ContinuousLinearMap.mul_def, A] using
      memSchattenClass_one_comp_left
        (ccmQuantizedDifferential_memSchattenClass_one
          (ccmArchimedeanScatteringPhaseMul g))
        ccmArchimedeanScatteringConjL2Multiplier
  have hDgU : MemSchattenClass 1
      (ccmQuantizedDifferential g * ccmArchimedeanScatteringL2Multiplier) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right
        (ccmQuantizedDifferential_memSchattenClass_one g)
        ccmArchimedeanScatteringL2Multiplier
  have hB : MemSchattenClass 1 B := by
    simpa only [ContinuousLinearMap.mul_def, B] using
      memSchattenClass_one_comp_left hDgU
        ccmArchimedeanScatteringConjL2Multiplier
  rw [ccmSchwartzMultiplier_mul_scatteringLogDifferential,
    ccmSchwartzMultiplier_mul_scatteringQuantizedDifferential,
    mul_sub, opTrace_smul,
    opTrace_sub_of_memSchattenClass_one hA hB,
    opTrace_scatteringConj_mul_quantizedDifferential_mul_scattering_eq_zero,
    sub_zero]

end RHTower
