import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedTraceClass
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Trace of the Connes--Consani quantized differential

The two Hardy crossblocks in the quantized differential are Schatten one.  Projection
idempotence and bounded cyclicity force the ordinary operator trace of each off-diagonal block to
vanish.  Consequently the trace of the literal Connes--Consani quantized differential `[H, M_f]`
is zero for every Schwartz symbol, with no analytic premise exposed.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

/-- The positive-to-negative Hardy crossblock has zero ordinary operator trace. -/
theorem opTrace_ccmHardyUpperCrossBlock_eq_zero (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        (ccmHardyProjection * ccmSchwartzMultiplier f *
          (1 - ccmHardyProjection)) = 0 := by
  let Q : SoninL2 →L[ℂ] SoninL2 := ccmHardyProjection
  let U : SoninL2 →L[ℂ] SoninL2 :=
    Q * ccmSchwartzMultiplier f * (1 - Q)
  have hQ : Q * Q = Q := by
    exact ccmHardyProjection_idempotent
  have hU : MemSchattenClass 1 U := by
    simpa only [Q, U] using ccmHardyUpperCrossBlock_memSchattenClass_one f
  have hleft : Q * U = U := by
    dsimp only [U]
    simp only [← mul_assoc, hQ]
  have hright : U * Q = 0 := by
    dsimp only [U]
    noncomm_ring [hQ]
  have hcyc := hU.one_opTrace_comp_comm Q
  have hcycle : ContinuousLinearMap.opTrace (Q * U) =
      ContinuousLinearMap.opTrace (U * Q) := by
    simpa only [ContinuousLinearMap.mul_def] using hcyc
  rw [hleft, hright, opTrace_zero] at hcycle
  simpa only [Q, U] using hcycle

/-- The negative-to-positive Hardy crossblock has zero ordinary operator trace. -/
theorem opTrace_ccmHardyLowerCrossBlock_eq_zero (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace
        ((1 - ccmHardyProjection) * ccmSchwartzMultiplier f *
          ccmHardyProjection) = 0 := by
  let Q : SoninL2 →L[ℂ] SoninL2 := ccmHardyProjection
  let L : SoninL2 →L[ℂ] SoninL2 :=
    (1 - Q) * ccmSchwartzMultiplier f * Q
  have hQ : Q * Q = Q := by
    exact ccmHardyProjection_idempotent
  have hL : MemSchattenClass 1 L := by
    simpa only [Q, L] using ccmHardyLowerCrossBlock_memSchattenClass_one f
  have hleft : Q * L = 0 := by
    dsimp only [L]
    simp only [← mul_assoc, mul_sub, mul_one, hQ, sub_self, zero_mul]
  have hright : L * Q = L := by
    dsimp only [L]
    noncomm_ring [hQ]
  have hcyc := hL.one_opTrace_comp_comm Q
  have hcycle : ContinuousLinearMap.opTrace (Q * L) =
      ContinuousLinearMap.opTrace (L * Q) := by
    simpa only [ContinuousLinearMap.mul_def] using hcyc
  rw [hleft, hright, opTrace_zero] at hcycle
  simpa only [Q, L] using hcycle.symm

/-- The literal Connes--Consani quantized differential has zero ordinary operator trace. -/
theorem opTrace_ccmQuantizedDifferential_eq_zero (f : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.opTrace (ccmQuantizedDifferential f) = 0 := by
  let U : SoninL2 →L[ℂ] SoninL2 :=
    ccmHardyProjection * ccmSchwartzMultiplier f * (1 - ccmHardyProjection)
  let L : SoninL2 →L[ℂ] SoninL2 :=
    (1 - ccmHardyProjection) * ccmSchwartzMultiplier f * ccmHardyProjection
  have hU : MemSchattenClass 1 U := ccmHardyUpperCrossBlock_memSchattenClass_one f
  have hL : MemSchattenClass 1 L := ccmHardyLowerCrossBlock_memSchattenClass_one f
  rw [ccmQuantizedDifferential_eq_two_smul_crossBlocks,
    opTrace_smul,
    opTrace_sub_of_memSchattenClass_one hU hL,
    opTrace_ccmHardyUpperCrossBlock_eq_zero,
    opTrace_ccmHardyLowerCrossBlock_eq_zero]
  ring

end RHTower
