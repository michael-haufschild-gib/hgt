import GaloisForLFunctions.RHTower.RestrictedProjectionCubicTrace
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Cubic trace cocycle for Hilbert--Schmidt projection differences

For three orthogonal projections `R`, `Q`, and `P`, put `A = R - Q` and `B = Q - P`.
The mixed part of `(A + B)^(3 : ℕ)` has zero trace.  The key projection identity is

`A^(2 : ℕ) B + A B^(2 : ℕ) = (A B) Q - Q (A B)`,

whose right side is a trace-class commutator.  Cyclicity moves the remaining mixed monomials
onto this same zero-trace pair.  Consequently the cubic projection trace is an additive cocycle.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem memSchattenClass_one_mul_of_hilbertSchmidt
    {S T : H →L[ℂ] H} (hS : S.IsHilbertSchmidt) (hT : T.IsHilbertSchmidt) :
    MemSchattenClass 1 (S * T) := by
  have hrect :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hT hS
  exact (memRectSchattenClass_iff_memSchattenClass 1 (S ∘L T)).mp hrect

private theorem memSchattenClass_one_add'
    {S T : H →L[ℂ] H} (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (S + T) :=
  memSchattenClass_one_add (hS.isCompactOperator one_pos)
    (hT.isCompactOperator one_pos) hS hT

private theorem opTrace_projection_mixed_pair_eq_zero
    (R Q P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hRQ : (R - Q).IsHilbertSchmidt) (hQP : (Q - P).IsHilbertSchmidt) :
    opTrace (((R - Q) * (R - Q)) * (Q - P) +
        (R - Q) * ((Q - P) * (Q - P))) = 0 := by
  let A := R - Q
  let B := Q - P
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hRQ hQP
  have hABQ : MemSchattenClass 1 ((A * B) * Q) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hAB Q
  have hQAB : MemSchattenClass 1 (Q * (A * B)) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_left hAB Q
  have hcross : (A * A) * B + A * (B * B) = (A * B) * Q - Q * (A * B) := by
    have hRR : R * R = R := hR
    have hQQ : Q * Q = Q := hQ
    have hPP : P * P = P := hP
    have hQQP : Q * (Q * P) = Q * P := by rw [← mul_assoc, hQQ]
    dsimp only [A, B]
    noncomm_ring [hRR, hQQ, hPP, hQQP]
  change opTrace ((A * A) * B + A * (B * B)) = 0
  rw [hcross, opTrace_sub_of_memSchattenClass_one hABQ hQAB]
  have hcyc := hAB.one_opTrace_comp_comm Q
  change opTrace ((A * B) * Q) - opTrace (Q * (A * B)) = 0
  rw [show opTrace (Q * (A * B)) = opTrace ((A * B) * Q) by
    simpa only [ContinuousLinearMap.mul_def] using hcyc]
  exact sub_self _

/-- **Cubic projection trace cocycle.**  Whenever both adjacent projection differences are
Hilbert--Schmidt, the long difference is Hilbert--Schmidt and its cubic trace is the sum of the
two adjacent cubic traces. -/
theorem opTrace_restrictedProjectionCubicDefect_cocycle
    (R Q P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    opTrace (restrictedProjectionCubicDefect R P) =
      opTrace (restrictedProjectionCubicDefect R Q) +
        opTrace (restrictedProjectionCubicDefect Q P) := by
  let A := restrictedProjectionDisplacement R Q
  let B := restrictedProjectionDisplacement Q P
  let T₀ := (A * A) * B + A * (B * B)
  let T₁ := (A * B) * A + (B * A) * B
  let T₂ := (B * A) * A + (B * B) * A

  have hA : A.IsHilbertSchmidt := hRQ
  have hB : B.IsHilbertSchmidt := hQP
  have hAA : MemSchattenClass 1 (A * A) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hA hA
  have hAB : MemSchattenClass 1 (A * B) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hA hB
  have hBA : MemSchattenClass 1 (B * A) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hB hA
  have hBB : MemSchattenClass 1 (B * B) :=
    memSchattenClass_one_mul_of_hilbertSchmidt hB hB
  have hAAA : MemSchattenClass 1 ((A * A) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hAA A
  have hBBB : MemSchattenClass 1 ((B * B) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hBB B
  have hAAB : MemSchattenClass 1 ((A * A) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hAA B
  have hABA : MemSchattenClass 1 ((A * B) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hAB A
  have hBAA : MemSchattenClass 1 ((B * A) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hBA A
  have hABB : MemSchattenClass 1 (A * (B * B)) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_left hBB A
  have hBAB : MemSchattenClass 1 ((B * A) * B) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hBA B
  have hBBA : MemSchattenClass 1 ((B * B) * A) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hBB A

  have hT₀ : MemSchattenClass 1 T₀ := memSchattenClass_one_add' hAAB hABB
  have hT₁ : MemSchattenClass 1 T₁ := memSchattenClass_one_add' hABA hBAB
  have hT₂ : MemSchattenClass 1 T₂ := memSchattenClass_one_add' hBAA hBBA

  have htraceT₀ : opTrace T₀ = 0 := by
    simpa only [T₀, A, B, restrictedProjectionDisplacement] using
      opTrace_projection_mixed_pair_eq_zero R Q P hR hQ hP hRQ hQP

  have htraceAAB_ABA : opTrace ((A * A) * B) = opTrace ((A * B) * A) := by
    have hcyc := hAB.one_opTrace_comp_comm A
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hcyc
  have htraceAAB_BAA : opTrace ((A * A) * B) = opTrace ((B * A) * A) := by
    have hcyc := hAA.one_opTrace_comp_comm B
    calc
      opTrace ((A * A) * B) = opTrace (B * (A * A)) := by
        simpa only [ContinuousLinearMap.mul_def] using hcyc.symm
      _ = opTrace ((B * A) * A) := by rw [mul_assoc]
  have htraceABB_BAB : opTrace (A * (B * B)) = opTrace ((B * A) * B) := by
    have hcyc := hAB.one_opTrace_comp_comm B
    calc
      opTrace (A * (B * B)) = opTrace ((A * B) * B) := by rw [mul_assoc]
      _ = opTrace (B * (A * B)) := by
        simpa only [ContinuousLinearMap.mul_def] using hcyc.symm
      _ = opTrace ((B * A) * B) := by rw [mul_assoc]
  have htraceABB_BBA : opTrace (A * (B * B)) = opTrace ((B * B) * A) := by
    have hcyc := hBB.one_opTrace_comp_comm A
    simpa only [ContinuousLinearMap.mul_def] using hcyc

  have htraceT₁ : opTrace T₁ = 0 := by
    rw [show opTrace T₁ = opTrace ((A * B) * A) + opTrace ((B * A) * B) by
      exact opTrace_add_of_memSchattenClass_one hABA hBAB]
    rw [← htraceAAB_ABA, ← htraceABB_BAB]
    rw [← opTrace_add_of_memSchattenClass_one hAAB hABB]
    exact htraceT₀
  have htraceT₂ : opTrace T₂ = 0 := by
    rw [show opTrace T₂ = opTrace ((B * A) * A) + opTrace ((B * B) * A) by
      exact opTrace_add_of_memSchattenClass_one hBAA hBBA]
    rw [← htraceAAB_BAA, ← htraceABB_BBA]
    rw [← opTrace_add_of_memSchattenClass_one hAAB hABB]
    exact htraceT₀

  have hlong : restrictedProjectionDisplacement R P = A + B := by
    simp only [A, B, restrictedProjectionDisplacement]
    abel
  have hcube : restrictedProjectionCubicDefect R P =
      ((A * A) * A + (B * B) * B) + T₀ + T₁ + T₂ := by
    rw [restrictedProjectionCubicDefect, hlong]
    simp only [pow_succ]
    dsimp only [T₀, T₁, T₂]
    noncomm_ring

  have hbase : MemSchattenClass 1 ((A * A) * A + (B * B) * B) :=
    memSchattenClass_one_add' hAAA hBBB
  have hbaseT₀ : MemSchattenClass 1 (((A * A) * A + (B * B) * B) + T₀) :=
    memSchattenClass_one_add' hbase hT₀
  have hbaseT₀T₁ : MemSchattenClass 1
      ((((A * A) * A + (B * B) * B) + T₀) + T₁) :=
    memSchattenClass_one_add' hbaseT₀ hT₁

  rw [hcube]
  rw [opTrace_add_of_memSchattenClass_one hbaseT₀T₁ hT₂, htraceT₂, add_zero]
  rw [opTrace_add_of_memSchattenClass_one hbaseT₀ hT₁, htraceT₁, add_zero]
  rw [opTrace_add_of_memSchattenClass_one hbase hT₀, htraceT₀, add_zero]
  rw [opTrace_add_of_memSchattenClass_one hAAA hBBB]
  simp only [A, B, restrictedProjectionCubicDefect, restrictedProjectionDisplacement,
    pow_succ, pow_zero, one_mul, ContinuousLinearMap.mul_def]

/-- Real-valued form of the cubic trace cocycle. -/
theorem re_opTrace_restrictedProjectionCubicDefect_cocycle
    (R Q P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    (opTrace (restrictedProjectionCubicDefect R P)).re =
      (opTrace (restrictedProjectionCubicDefect R Q)).re +
        (opTrace (restrictedProjectionCubicDefect Q P)).re := by
  exact congrArg Complex.re
    (opTrace_restrictedProjectionCubicDefect_cocycle R Q P hR hQ hP hRQ hQP)

end RHTower
