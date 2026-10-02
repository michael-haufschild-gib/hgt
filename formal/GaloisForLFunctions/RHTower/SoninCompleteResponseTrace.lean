import GaloisForLFunctions.RHTower.SoninTimeBandSchatten
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace

noncomputable section
namespace RHTower
open ContinuousLinearMap
local notation "Op" => (SoninL2 →L[ℂ] SoninL2)

private theorem correction_mul_projection_zero (a : ℝ) :
    centralSoninProjectionCorrection a * centralSoninProjection a = 0 := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : Op := A.starProjection
  let R : Op := B.starProjection
  let Q : Op := centralSoninProjection a
  have hQQ : Q * Q = Q := (centralSoninCarrier a).isIdempotentElem_starProjection
  have hPQ : P * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change A.starProjection ((A.orthogonal ⊓ B.orthogonal).starProjection f) = 0
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem f).1
  have hRQ : R * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change B.starProjection ((A.orthogonal ⊓ B.orthogonal).starProjection f) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((A.orthogonal ⊓ B.orthogonal).starProjection_apply_mem f).2
  have hJ : centralSoninProjectionCorrection a = Q - (1 - P - R) := by
    simp only [centralSoninProjectionCorrection, Q, P, R, A, B,
      centralPhysicalForbidden, centralFourierForbidden, centralInterval,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection]
  rw [hJ]
  change (Q - (1 - P - R)) * Q = 0
  noncomm_ring [hQQ, hPQ, hRQ]

private theorem projection_mul_correction_zero (a : ℝ) :
    centralSoninProjection a * centralSoninProjectionCorrection a = 0 := by
  have hQ : adjoint (centralSoninProjection a) = centralSoninProjection a :=
    (isSelfAdjoint_starProjection (centralSoninCarrier a)).star_eq
  have h := congrArg (adjoint : Op ≃ₗᵢ⋆[ℂ] Op) (correction_mul_projection_zero a)
  simpa only [adjoint_mul_soninL2, hQ, adjoint_centralSoninProjectionCorrection,
    map_zero] using h

private theorem correction_minus_formal_mul_eq (a : ℝ) :
    centralSoninProjectionCorrection a -
        centralSoninFormalComplement a * centralSoninProjectionCorrection a =
      (centralPhysicalForbidden a).starProjection * (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection := by
  let Q := centralSoninProjection a
  let Q0 := centralSoninFormalComplement a
  let J := centralSoninProjectionCorrection a
  have hQJ : Q * J = 0 := projection_mul_correction_zero a
  have hQ0 : Q0 = Q - J := by
    change centralSoninFormalComplement a = centralSoninProjection a -
      (centralSoninProjection a - centralSoninFormalComplement a)
    abel
  calc
    J - Q0 * J = J * J + J := by rw [hQ0]; noncomm_ring [hQJ]
    _ = _ := centralSoninProjectionCorrection_sq_add_self_eq_anticommutator a

private theorem response_commutator_algebra {M : Type*} [Ring M]
    (Q Q0 J D L : M) (hJQ : J * Q = 0) (hL : J - Q0 * J = L) :
    (1 - Q) * D * J - J * D * Q0 =
      D * L + (D * Q0 * J - J * (D * Q0)) - (Q * (D * J) - D * J * Q) := by
  rw [← hL]
  noncomm_ring [hJQ]

/-- The complete original correction response retains the actual time-band
current plus two explicit commutators with trace-class factors. -/
theorem centralSoninCornerCorrectionResponse_eq_timeBand_commutators
    (a : ℝ) (D : Op) :
    centralSoninCornerCorrectionResponse a D =
      D * ((centralPhysicalForbidden a).starProjection *
          (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) +
      (D * centralSoninFormalComplement a * centralSoninProjectionCorrection a -
        centralSoninProjectionCorrection a * (D * centralSoninFormalComplement a)) -
      (centralSoninProjection a * (D * centralSoninProjectionCorrection a) -
        D * centralSoninProjectionCorrection a * centralSoninProjection a) := by
  rw [centralSoninCornerCorrectionResponse_eq_correction_factorization]
  exact response_commutator_algebra _ _ _ _ _
    (correction_mul_projection_zero a) (correction_minus_formal_mul_eq a)

private theorem trace_commutator_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) (D : H →L[ℂ] H) :
    opTrace (D * T - T * D) = 0 := by
  have hDT : MemSchattenClass 1 (D * T) := memSchattenClass_one_comp_left hT D
  have hTD : MemSchattenClass 1 (T * D) := memSchattenClass_one_comp_right hT D
  rw [opTrace_sub_of_memSchattenClass_one hDT hTD]
  exact sub_eq_zero.mpr (hT.one_opTrace_comp_comm D)

/-- The trace of the full two-leg response is exactly the actual time-band
anticommutator pairing; no source positivity or commutation premise is used. -/
theorem opTrace_centralSoninCornerCorrectionResponse_eq_timeBand
    (a : ℝ) (ha : 0 < a) (D : Op) :
    opTrace (centralSoninCornerCorrectionResponse a D) =
      opTrace (D * ((centralPhysicalForbidden a).starProjection *
          (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection)) := by
  let Q := centralSoninProjection a
  let Q0 := centralSoninFormalComplement a
  let J := centralSoninProjectionCorrection a
  let L := (centralPhysicalForbidden a).starProjection *
      (centralFourierForbidden a).starProjection +
    (centralFourierForbidden a).starProjection * (centralPhysicalForbidden a).starProjection
  have hJ : MemSchattenClass 1 J := centralSoninProjectionCorrection_memSchattenClass_one a ha
  have hDJ : MemSchattenClass 1 (D * J) := memSchattenClass_one_comp_left hJ D
  have hL : MemSchattenClass 1 L := by
    dsimp only [L]
    rw [← correction_minus_formal_mul_eq a]
    exact hJ.one_sub (memSchattenClass_one_comp_left hJ Q0)
  have hDL : MemSchattenClass 1 (D * L) := memSchattenClass_one_comp_left hL D
  have hC1 : MemSchattenClass 1 (D * Q0 * J - J * (D * Q0)) :=
    (memSchattenClass_one_comp_left hJ (D * Q0)).one_sub
      (memSchattenClass_one_comp_right hJ (D * Q0))
  have hC2 : MemSchattenClass 1 (Q * (D * J) - D * J * Q) :=
    (memSchattenClass_one_comp_left hDJ Q).one_sub
      (memSchattenClass_one_comp_right hDJ Q)
  rw [centralSoninCornerCorrectionResponse_eq_timeBand_commutators]
  change opTrace (D * L + (D * Q0 * J - J * (D * Q0)) -
    (Q * (D * J) - D * J * Q)) = opTrace (D * L)
  rw [opTrace_sub_of_memSchattenClass_one (hDL.one_add hC1) hC2,
    opTrace_add_of_memSchattenClass_one hDL hC1]
  have htr1 : opTrace (D * Q0 * J - J * (D * Q0)) = 0 := trace_commutator_zero hJ (D * Q0)
  have htr2 : opTrace (Q * (D * J) - D * J * Q) = 0 := trace_commutator_zero hDJ Q
  rw [htr1, htr2, add_zero, sub_zero]

end RHTower
