import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Trace and sign of compression curvature

If `P` is an idempotent and `P T P - T` is Schatten-1, bounded trace cyclicity removes every
off-diagonal block.  The whole relative trace is the negative trace of the complementary
compression.  When `P` is orthogonal and `T = Y†Y`, that complementary block is a positive Gram
operator, so compression curvature has nonpositive real trace.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Compression-curvature trace law.** A trace-class difference between an operator and its
idempotent compression has trace equal to minus the complementary diagonal-block trace. -/
theorem opTrace_compression_sub_self_eq_neg_complement
    (P T : H →L[ℂ] H) (hP : P * P = P)
    (hK : MemSchattenClass 1 (P * T * P - T)) :
    opTrace (P * T * P - T) = -opTrace ((1 - P) * T * (1 - P)) := by
  let R : H →L[ℂ] H := 1 - P
  let K : H →L[ℂ] H := P * T * P - T
  have hPR : P * R = 0 := by
    dsimp only [R]
    rw [mul_sub, mul_one, hP, sub_self]
  have hRP : R * P = 0 := by
    dsimp only [R]
    rw [sub_mul, one_mul, hP, sub_self]
  have hPKP : P * K * P = 0 := by
    dsimp only [K]
    calc
      P * (P * T * P - T) * P =
          (P * P) * T * (P * P) - P * T * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hRKR : R * K * R = -(R * T * R) := by
    dsimp only [K]
    calc
      R * (P * T * P - T) * R =
          (R * P) * T * (P * R) - R * T * R := by noncomm_ring
      _ = -(R * T * R) := by rw [hRP]; simp
  have hPK : MemSchattenClass 1 (P * K) := by
    simpa only [ContinuousLinearMap.mul_def, K] using
      memSchattenClass_one_comp_left hK P
  have hRK : MemSchattenClass 1 (R * K) := by
    simpa only [ContinuousLinearMap.mul_def, K] using
      memSchattenClass_one_comp_left hK R
  have hKP : MemSchattenClass 1 (K * P) := by
    simpa only [ContinuousLinearMap.mul_def, K] using
      memSchattenClass_one_comp_right hK P
  have hKR : MemSchattenClass 1 (K * R) := by
    simpa only [ContinuousLinearMap.mul_def, K] using
      memSchattenClass_one_comp_right hK R
  have hPKP_tc : MemSchattenClass 1 (P * K * P) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hPK P
  have hPKR_tc : MemSchattenClass 1 (P * K * R) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hPK R
  have hRKP_tc : MemSchattenClass 1 (R * K * P) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hRK P
  have hRKR_tc : MemSchattenClass 1 (R * K * R) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hRK R
  have hPKR_trace : opTrace (P * K * R) = 0 := by
    have hcyc := hKR.one_opTrace_comp_comm P
    have hcycle : opTrace (P * (K * R)) = opTrace ((K * R) * P) := by
      simpa only [ContinuousLinearMap.mul_def] using hcyc
    rw [← mul_assoc] at hcycle
    rw [hcycle, mul_assoc, hRP, mul_zero, opTrace_zero]
  have hRKP_trace : opTrace (R * K * P) = 0 := by
    have hcyc := hKP.one_opTrace_comp_comm R
    have hcycle : opTrace (R * (K * P)) = opTrace ((K * P) * R) := by
      simpa only [ContinuousLinearMap.mul_def] using hcyc
    rw [← mul_assoc] at hcycle
    rw [hcycle, mul_assoc, hPR, mul_zero, opTrace_zero]
  have hdecomp : K = P * K * P + P * K * R + R * K * P + R * K * R := by
    dsimp only [R]
    noncomm_ring
  have hsum1 : MemSchattenClass 1 (P * K * P + P * K * R) :=
    memSchattenClass_one_add (hPKP_tc.isCompactOperator one_pos)
      (hPKR_tc.isCompactOperator one_pos) hPKP_tc hPKR_tc
  have hsum2 : MemSchattenClass 1
      (P * K * P + P * K * R + R * K * P) :=
    memSchattenClass_one_add (hsum1.isCompactOperator one_pos)
      (hRKP_tc.isCompactOperator one_pos) hsum1 hRKP_tc
  have hB : MemSchattenClass 1 (R * T * R) := by
    rw [hRKR] at hRKR_tc
    simpa using memSchattenClass_one_smul hRKR_tc (-1)
  change opTrace K = -opTrace (R * T * R)
  rw [hdecomp]
  rw [opTrace_add_of_memSchattenClass_one hsum2 hRKR_tc,
    opTrace_add_of_memSchattenClass_one hsum1 hRKP_tc,
    opTrace_add_of_memSchattenClass_one hPKP_tc hPKR_tc,
    hPKP, opTrace_zero, hPKR_trace, hRKP_trace, zero_add, add_zero,
    hRKR, opTrace_neg]
  simp

/-- Trace-class compression curvature forces the complementary diagonal block itself to be
Schatten-1. -/
theorem complement_compression_memSchattenClass_one
    (P T : H →L[ℂ] H) (hP : P * P = P)
    (hK : MemSchattenClass 1 (P * T * P - T)) :
    MemSchattenClass 1 ((1 - P) * T * (1 - P)) := by
  let R : H →L[ℂ] H := 1 - P
  let K : H →L[ℂ] H := P * T * P - T
  have hRP : R * P = 0 := by
    dsimp only [R]
    rw [sub_mul, one_mul, hP, sub_self]
  have hRKR : R * K * R = -(R * T * R) := by
    dsimp only [K]
    calc
      R * (P * T * P - T) * R =
          (R * P) * T * (P * R) - R * T * R := by noncomm_ring
      _ = -(R * T * R) := by rw [hRP]; simp
  have hRK : MemSchattenClass 1 (R * K) := by
    simpa only [ContinuousLinearMap.mul_def, K] using
      memSchattenClass_one_comp_left hK R
  have hRKR_tc : MemSchattenClass 1 (R * K * R) := by
    simpa only [ContinuousLinearMap.mul_def] using
      memSchattenClass_one_comp_right hRK R
  rw [hRKR] at hRKR_tc
  change MemSchattenClass 1 (R * T * R)
  simpa using memSchattenClass_one_smul hRKR_tc (-1)

/-- A positive Gram operator can be Schatten-1 only when its generating map is
Hilbert--Schmidt.  This is the converse to the usual Hilbert--Schmidt square construction. -/
theorem isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one
    (Z : H →L[ℂ] H)
    (hZ : MemSchattenClass 1 (ContinuousLinearMap.adjoint Z * Z)) :
    Z.IsHilbertSchmidt := by
  have hdiag := hZ.one_summable_inner_diag
  refine isHilbertSchmidt_of_summable (hsBasis ℂ H) ?_
  rw [← RCLike.summable_ofReal (𝕜 := ℂ)]
  refine hdiag.congr fun i => ?_
  simp only [mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- **Exact compression-energy law.**  Positive trace-class compression curvature is not merely
nonpositive: its real trace is exactly minus the squared Hilbert--Schmidt norm of the transition
lost through the complementary projection. -/
theorem re_opTrace_compression_sub_self_eq_neg_hsNormSq
    (P T Y : H →L[ℂ] H) (hP : P * P = P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hT : T = ContinuousLinearMap.adjoint Y * Y)
    (hK : MemSchattenClass 1 (P * T * P - T)) :
    (opTrace (P * T * P - T)).re =
      -hsNormSq (Y * (1 - P)) := by
  let R : H →L[ℂ] H := 1 - P
  let Z : H →L[ℂ] H := Y * R
  have hRadj : ContinuousLinearMap.adjoint R = R := by
    dsimp only [R]
    rw [ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_one, hPadj]
  have hB : MemSchattenClass 1 (R * T * R) := by
    simpa only [R] using complement_compression_memSchattenClass_one P T hP hK
  have hBgram : R * T * R = ContinuousLinearMap.adjoint Z * Z := by
    dsimp only [Z]
    rw [hT]
    change R * (ContinuousLinearMap.adjoint Y * Y) * R =
      ContinuousLinearMap.adjoint (Y ∘L R) ∘L (Y ∘L R)
    rw [ContinuousLinearMap.adjoint_comp]
    change R * (ContinuousLinearMap.adjoint Y * Y) * R =
      ContinuousLinearMap.adjoint R * ContinuousLinearMap.adjoint Y * (Y * R)
    rw [hRadj]
    noncomm_ring
  have hZtc : MemSchattenClass 1 (ContinuousLinearMap.adjoint Z * Z) := by
    rw [← hBgram]
    exact hB
  have hZhs : Z.IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one Z hZtc
  rw [opTrace_compression_sub_self_eq_neg_complement P T hP hK, hBgram]
  simpa only [Complex.neg_re, Z, R] using
    congrArg Neg.neg (ContinuousLinearMap.re_opTrace_adjoint_comp_self hZhs)

/-- **Faithfulness of positive compression curvature.**  Once the compression defect is
trace-class, it vanishes exactly when the corresponding boundary transition vanishes. -/
theorem compression_sub_self_eq_zero_iff_boundary_zero
    (P T Y : H →L[ℂ] H) (hP : P * P = P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hT : T = ContinuousLinearMap.adjoint Y * Y)
    (hK : MemSchattenClass 1 (P * T * P - T)) :
    P * T * P - T = 0 ↔ Y * (1 - P) = 0 := by
  let R : H →L[ℂ] H := 1 - P
  let Z : H →L[ℂ] H := Y * R
  have henergy := re_opTrace_compression_sub_self_eq_neg_hsNormSq
    P T Y hP hPadj hT hK
  have hB : MemSchattenClass 1 (R * T * R) := by
    simpa only [R] using complement_compression_memSchattenClass_one P T hP hK
  have hRadj : ContinuousLinearMap.adjoint R = R := by
    dsimp only [R]
    rw [ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_one, hPadj]
  have hBgram : R * T * R = ContinuousLinearMap.adjoint Z * Z := by
    dsimp only [Z]
    rw [hT]
    change R * (ContinuousLinearMap.adjoint Y * Y) * R =
      ContinuousLinearMap.adjoint (Y ∘L R) ∘L (Y ∘L R)
    rw [ContinuousLinearMap.adjoint_comp]
    change R * (ContinuousLinearMap.adjoint Y * Y) * R =
      ContinuousLinearMap.adjoint R * ContinuousLinearMap.adjoint Y * (Y * R)
    rw [hRadj]
    noncomm_ring
  have hZtc : MemSchattenClass 1 (ContinuousLinearMap.adjoint Z * Z) := by
    rw [← hBgram]
    exact hB
  have hZhs : Z.IsHilbertSchmidt :=
    isHilbertSchmidt_of_adjoint_mul_self_memSchattenClass_one Z hZtc
  constructor
  · intro hzero
    have hnorm' : hsNormSq (Y * (1 - P)) = 0 := by
      rw [hzero, opTrace_zero] at henergy
      simpa using henergy
    have hnorm : hsNormSq Z = 0 := by
      simpa only [Z, R] using hnorm'
    simpa only [Z, R] using (hsNormSq_eq_zero_iff hZhs).mp hnorm
  · intro hZzero
    have hYP : Y * P = Y := by
      have hsplit : Y = Y * P + Y * (1 - P) := by noncomm_ring
      rw [hZzero, add_zero] at hsplit
      exact hsplit.symm
    have hPYadj : P * ContinuousLinearMap.adjoint Y =
        ContinuousLinearMap.adjoint Y := by
      have hadj := congrArg ContinuousLinearMap.adjoint hYP
      change ContinuousLinearMap.adjoint (Y ∘L P) =
        ContinuousLinearMap.adjoint Y at hadj
      rw [ContinuousLinearMap.adjoint_comp, hPadj] at hadj
      exact hadj
    rw [hT]
    calc
      P * (ContinuousLinearMap.adjoint Y * Y) * P -
          ContinuousLinearMap.adjoint Y * Y =
          (P * ContinuousLinearMap.adjoint Y) * (Y * P) -
            ContinuousLinearMap.adjoint Y * Y := by noncomm_ring
      _ = 0 := by rw [hPYadj, hYP, sub_self]

/-- **Universal sign law.** A trace-class compression curvature of a positive Gram operator has
nonpositive real trace; it is the negative complementary Gram energy. -/
theorem re_opTrace_compression_sub_self_nonpos_of_adjoint_mul_self
    (P T Y : H →L[ℂ] H) (hP : P * P = P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hT : T = ContinuousLinearMap.adjoint Y * Y)
    (hK : MemSchattenClass 1 (P * T * P - T)) :
    (opTrace (P * T * P - T)).re ≤ 0 := by
  rw [re_opTrace_compression_sub_self_eq_neg_hsNormSq P T Y hP hPadj hT hK]
  exact neg_nonpos.mpr (hsNormSq_nonneg _)

end RHTower
