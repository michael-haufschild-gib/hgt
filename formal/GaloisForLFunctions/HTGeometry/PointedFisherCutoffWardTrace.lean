import GaloisForLFunctions.HTGeometry.RankTwoFisherCutoffWard

/-!
# Signed finite-rank cutoff Ward trace

A bounded cutoff edge need not be Hilbert--Schmidt.  Pairing it with the finite-rank pointed
Fisher connection nevertheless gives a canonical trace.  This module identifies that signed
pairing with a double-commutator value and proves its two reflection laws: cutoff complementation
and conjugation by a self-adjoint involution.
-/

open Complex
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical diagonal of a rank-one operator is summable. -/
theorem summable_inner_diag_rankOne (x y : H) :
    Summable (fun i => inner ℂ (hsBasis ℂ H i)
      (rankOne ℂ x y (hsBasis ℂ H i))) := by
  simpa only [rankOne_apply, inner_smul_right] using
    (hsBasis ℂ H).summable_inner_mul_inner y x

/-- The project's operator trace agrees with the usual rank-one trace. -/
theorem opTrace_rankOne (x y : H) :
    opTrace (rankOne ℂ x y) = inner ℂ y x := by
  rw [opTrace]
  simpa only [rankOne_apply, inner_smul_right] using
    (hsBasis ℂ H).tsum_inner_mul_inner y x

/-- Operator trace is additive whenever both canonical diagonals are summable. -/
theorem opTrace_add_of_summable_diag (S T : H →L[ℂ] H)
    (hS : Summable (fun i => inner ℂ (hsBasis ℂ H i) (S (hsBasis ℂ H i))))
    (hT : Summable (fun i => inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i)))) :
    opTrace (S + T) = opTrace S + opTrace T := by
  unfold opTrace
  simp_rw [add_apply, inner_add_right]
  exact hS.tsum_add hT

/-- Operator trace respects subtraction whenever both canonical diagonals are summable. -/
theorem opTrace_sub_of_summable_diag (S T : H →L[ℂ] H)
    (hS : Summable (fun i => inner ℂ (hsBasis ℂ H i) (S (hsBasis ℂ H i))))
    (hT : Summable (fun i => inner ℂ (hsBasis ℂ H i) (T (hsBasis ℂ H i)))) :
    opTrace (S - T) = opTrace S - opTrace T := by
  unfold opTrace
  simp_rw [sub_apply, inner_sub_right]
  exact hS.tsum_sub hT

/-- Scalar multiplication passes through the canonical operator trace. -/
theorem opTrace_smul (c : ℂ) (S : H →L[ℂ] H) :
    opTrace (c • S) = c * opTrace S := by
  unfold opTrace
  simp_rw [smul_apply, inner_smul_right]
  exact tsum_mul_left

/-- A bounded sandwich of the pointed Fisher connection remains an explicit sum of two
rank-one operators. -/
theorem mul_pointedFisherConnection_mul
    (A B : H →L[ℂ] H) (psi chi : H) :
    A * pointedFisherConnection psi chi * B =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        (rankOne ℂ (A chi) (adjoint B psi) +
          rankOne ℂ (A psi) (adjoint B chi)) := by
  ext z
  simp [pointedFisherConnection, mul_apply_eq_comp,
    adjoint_inner_left]

/-- Every bounded sandwich of the pointed Fisher connection has summable canonical diagonal. -/
theorem summable_inner_diag_mul_pointedFisherConnection_mul
    (A B : H →L[ℂ] H) (psi chi : H) :
    Summable (fun i => inner ℂ (hsBasis ℂ H i)
      ((A * pointedFisherConnection psi chi * B) (hsBasis ℂ H i))) := by
  rw [mul_pointedFisherConnection_mul]
  simp_rw [smul_apply, add_apply, inner_smul_right, inner_add_right]
  exact ((summable_inner_diag_rankOne (A chi) (adjoint B psi)).add
    (summable_inner_diag_rankOne (A psi) (adjoint B chi))).mul_left _

/-- **Finite-rank value law.**  A bounded operator may be evaluated against the pointed Fisher
connection without any Hilbert--Schmidt premise on the bounded factors. -/
theorem opTrace_mul_pointedFisherConnection_mul
    (A B : H →L[ℂ] H) (psi chi : H) :
    opTrace (A * pointedFisherConnection psi chi * B) =
      ((Real.sqrt 2)⁻¹ : ℂ) *
        (inner ℂ psi (B (A chi)) + inner ℂ chi (B (A psi))) := by
  rw [mul_pointedFisherConnection_mul, opTrace_smul,
    opTrace_add_of_summable_diag]
  · rw [opTrace_rankOne, opTrace_rankOne, adjoint_inner_left,
      adjoint_inner_left]
  · exact summable_inner_diag_rankOne _ _
  · exact summable_inner_diag_rankOne _ _

/-- **Finite-rank cyclicity.**  A bounded factor can pass cyclically across the pointed Fisher
connection even when neither surrounding bounded operator is Hilbert--Schmidt. -/
theorem opTrace_mul_pointedFisherConnection_mul_cyclic
    (A B : H →L[ℂ] H) (psi chi : H) :
    opTrace (A * pointedFisherConnection psi chi * B) =
      opTrace (pointedFisherConnection psi chi * B * A) := by
  rw [opTrace_mul_pointedFisherConnection_mul,
    show pointedFisherConnection psi chi * B * A =
        1 * pointedFisherConnection psi chi * (B * A) by noncomm_ring,
    opTrace_mul_pointedFisherConnection_mul]
  simp [mul_apply_eq_comp]

/-- Double cutoff commutator, the curvature seen by the signed Ward trace. -/
noncomputable def cutoffWardCurvature (e T : H →L[ℂ] H) : H →L[ℂ] H :=
  cutoffCommutator e (cutoffCommutator e T)

/-- Adjoint cutoff curvature.  This is the unconditional curvature paired by the signed Ward
trace; it reduces to `cutoffWardCurvature` when the cutoff is self-adjoint. -/
noncomputable def cutoffWardAdjointCurvature (e T : H →L[ℂ] H) : H →L[ℂ] H :=
  cutoffCommutator (adjoint e) (cutoffCommutator e T)

/-- Signed finite-rank pairing of a pointed Fisher source with a bounded cutoff edge. -/
noncomputable def pointedCutoffWardTrace
    (e T : H →L[ℂ] H) (psi chi : H) : ℂ :=
  opTrace (adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
    cutoffCommutator e T)

omit [CompleteSpace H] in
/-- Reversing the tangent reverses the pointed Fisher connection. -/
theorem pointedFisherConnection_neg_tangent (psi chi : H) :
    pointedFisherConnection psi (-chi) = -pointedFisherConnection psi chi := by
  have hleft : rankOne ℂ (-chi) psi = -rankOne ℂ chi psi := by
    ext z
    simp only [rankOne_apply, smul_neg, neg_apply]
  have hright : rankOne ℂ psi (-chi) = -rankOne ℂ psi chi := by
    ext z
    simp only [rankOne_apply, inner_neg_left, neg_smul, neg_apply]
  rw [pointedFisherConnection, pointedFisherConnection, hleft, hright]
  module

/-- **Orientation law.**  The signed Ward trace is odd in the source tangent, in contrast to the
quadratic Hilbert--Schmidt energy.  Hence this scalarization retains rather than squares away the
orientation carried by an arithmetic tangent. -/
theorem pointedCutoffWardTrace_neg_tangent
    (e T : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace e T psi (-chi) =
      -pointedCutoffWardTrace e T psi chi := by
  unfold pointedCutoffWardTrace
  rw [pointedFisherConnection_neg_tangent]
  have hcomm :
      cutoffCommutator e (-pointedFisherConnection psi chi) =
        -cutoffCommutator e (pointedFisherConnection psi chi) := by
    change (-pointedFisherConnection psi chi) * e -
        e * (-pointedFisherConnection psi chi) =
      -(pointedFisherConnection psi chi * e -
        e * pointedFisherConnection psi chi)
    noncomm_ring
  rw [hcomm, map_neg]
  have hop :
      (-adjoint (cutoffCommutator e (pointedFisherConnection psi chi))) *
          cutoffCommutator e T =
        -(adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
          cutoffCommutator e T) := by
    noncomm_ring
  rw [hop]
  simpa only [neg_smul, one_smul, neg_one_mul] using
    opTrace_smul (-1 : ℂ)
      (adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
        cutoffCommutator e T)

/-- The commutator of two self-adjoint operators is anti-self-adjoint. -/
theorem adjoint_cutoffCommutator_of_selfAdjoint
    (e T : H →L[ℂ] H) (he : adjoint e = e) (hT : adjoint T = T) :
    adjoint (cutoffCommutator e T) = -cutoffCommutator e T := by
  rw [cutoffCommutator, map_sub, adjoint_comp, adjoint_comp, he, hT]
  ext z
  simp

/-- **Unconditional signed cutoff Ward transgression.**  The polarized boundary pairing is the
trace of the pointed Fisher connection against the adjoint cutoff curvature `[[T,e],e†]`. -/
theorem pointedCutoffWardTrace_eq_opTrace_adjointCurvature
    (e T : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace e T psi chi =
      opTrace (pointedFisherConnection psi chi *
        cutoffWardAdjointCurvature e T) := by
  let F := pointedFisherConnection psi chi
  let K := cutoffCommutator e T
  have hF : adjoint F = F := pointedFisherConnection_selfAdjoint psi chi
  have hAdj : adjoint (cutoffCommutator e F) =
      adjoint e * F - F * adjoint e := by
    rw [cutoffCommutator, map_sub, adjoint_comp, adjoint_comp, hF]
    rfl
  have hleft : (adjoint e * F - F * adjoint e) * K =
      adjoint e * F * K - F * adjoint e * K := by
    noncomm_ring
  have hright : F * cutoffWardAdjointCurvature e T =
      F * K * adjoint e - F * adjoint e * K := by
    change F * (K * adjoint e - adjoint e * K) =
      F * K * adjoint e - F * adjoint e * K
    noncomm_ring
  have heFK := summable_inner_diag_mul_pointedFisherConnection_mul
    (adjoint e) K psi chi
  have hFeK := summable_inner_diag_mul_pointedFisherConnection_mul
    1 (adjoint e * K) psi chi
  have hFKe := summable_inner_diag_mul_pointedFisherConnection_mul
    1 (K * adjoint e) psi chi
  dsimp only [pointedCutoffWardTrace]
  rw [hAdj, hleft, opTrace_sub_of_summable_diag]
  · rw [opTrace_mul_pointedFisherConnection_mul_cyclic (adjoint e) K, hright,
      opTrace_sub_of_summable_diag]
    · simpa only [one_mul, mul_assoc] using hFKe
    · simpa only [one_mul, mul_assoc] using hFeK
  · exact heFK
  · simpa only [one_mul, mul_assoc] using hFeK

/-- **Self-adjoint cutoff transgression.**  For an orthogonal cutoff, adjoint curvature is the
ordinary double cutoff commutator. -/
theorem pointedCutoffWardTrace_eq_opTrace_curvature
    (e T : H →L[ℂ] H) (psi chi : H)
    (he : adjoint e = e) :
    pointedCutoffWardTrace e T psi chi =
      opTrace (pointedFisherConnection psi chi * cutoffWardCurvature e T) := by
  rw [pointedCutoffWardTrace_eq_opTrace_adjointCurvature]
  congr 2
  rw [cutoffWardAdjointCurvature, he]
  rfl

/-- **Unconditional adjoint-curvature value relation.**  The signed trace is always the sum of
two pointed matrix elements of `[[T,e],e†]`. -/
theorem pointedCutoffWardTrace_eq_adjointCurvature_values
    (e T : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace e T psi chi =
      ((Real.sqrt 2)⁻¹ : ℂ) *
        (inner ℂ psi (cutoffWardAdjointCurvature e T chi) +
          inner ℂ chi (cutoffWardAdjointCurvature e T psi)) := by
  rw [pointedCutoffWardTrace_eq_opTrace_adjointCurvature]
  simpa only [one_mul] using
    opTrace_mul_pointedFisherConnection_mul
      (1 : H →L[ℂ] H) (cutoffWardAdjointCurvature e T) psi chi

/-- **Double-commutator value relation.**  The noncompact bounded edge enters only through two
matrix elements of its cutoff curvature; the Fisher probe supplies all trace-class regularity. -/
theorem pointedCutoffWardTrace_eq_values
    (e T : H →L[ℂ] H) (psi chi : H)
    (he : adjoint e = e) :
    pointedCutoffWardTrace e T psi chi =
      ((Real.sqrt 2)⁻¹ : ℂ) *
        (inner ℂ psi (cutoffWardCurvature e T chi) +
          inner ℂ chi (cutoffWardCurvature e T psi)) := by
  rw [pointedCutoffWardTrace_eq_adjointCurvature_values]
  rw [cutoffWardAdjointCurvature, he]
  rfl

omit [CompleteSpace H] in
/-- Double cutoff curvature is additive in the bounded channel. -/
theorem cutoffWardCurvature_add
    (e S T : H →L[ℂ] H) :
    cutoffWardCurvature e (S + T) =
      cutoffWardCurvature e S + cutoffWardCurvature e T := by
  change (((S + T) * e - e * (S + T)) * e -
      e * ((S + T) * e - e * (S + T))) =
    ((S * e - e * S) * e - e * (S * e - e * S)) +
      ((T * e - e * T) * e - e * (T * e - e * T))
  noncomm_ring

/-- The trace diagonal in the pointed Ward pairing is summable for every bounded channel. -/
theorem summable_inner_diag_pointedCutoffWardProduct
    (e T : H →L[ℂ] H) (psi chi : H) :
    Summable (fun i => inner ℂ (hsBasis ℂ H i)
      ((adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
        cutoffCommutator e T) (hsBasis ℂ H i))) := by
  let F := pointedFisherConnection psi chi
  let K := cutoffCommutator e T
  have hF : adjoint F = F := pointedFisherConnection_selfAdjoint psi chi
  have hAdj : adjoint (cutoffCommutator e F) =
      adjoint e * F - F * adjoint e := by
    rw [cutoffCommutator, map_sub, adjoint_comp, adjoint_comp, hF]
    rfl
  have hEq : adjoint (cutoffCommutator e F) * K =
      adjoint e * F * K - F * adjoint e * K := by
    rw [hAdj]
    noncomm_ring
  have hleft := summable_inner_diag_mul_pointedFisherConnection_mul
    (adjoint e) K psi chi
  have hright := summable_inner_diag_mul_pointedFisherConnection_mul
    1 (adjoint e * K) psi chi
  change Summable (fun i => inner ℂ (hsBasis ℂ H i)
    ((adjoint (cutoffCommutator e F) * K) (hsBasis ℂ H i)))
  rw [hEq]
  simp_rw [sub_apply, inner_sub_right]
  exact hleft.sub (by simpa only [one_mul, mul_assoc] using hright)

/-- **Source linearity.**  The signed pointed Ward trace is unconditionally additive in the
bounded channel.  This makes the value suitable for exact source/residual decompositions. -/
theorem pointedCutoffWardTrace_add
    (e S T : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace e (S + T) psi chi =
      pointedCutoffWardTrace e S psi chi +
        pointedCutoffWardTrace e T psi chi := by
  have hcomm : cutoffCommutator e (S + T) =
      cutoffCommutator e S + cutoffCommutator e T := by
    change (S + T) * e - e * (S + T) =
      (S * e - e * S) + (T * e - e * T)
    noncomm_ring
  unfold pointedCutoffWardTrace
  rw [hcomm]
  have hprod :
      adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
          (cutoffCommutator e S + cutoffCommutator e T) =
        adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
            cutoffCommutator e S +
          adjoint (cutoffCommutator e (pointedFisherConnection psi chi)) *
            cutoffCommutator e T := by
    noncomm_ring
  rw [hprod, opTrace_add_of_summable_diag]
  · exact summable_inner_diag_pointedCutoffWardProduct e S psi chi
  · exact summable_inner_diag_pointedCutoffWardProduct e T psi chi

/-- **Complement reflection.**  The signed Ward trace is unchanged when the observed cutoff is
exchanged with its complement: both boundary orientations reverse simultaneously. -/
theorem pointedCutoffWardTrace_one_sub
    (e T : H →L[ℂ] H) (psi chi : H) :
    pointedCutoffWardTrace (1 - e) T psi chi =
      pointedCutoffWardTrace e T psi chi := by
  unfold pointedCutoffWardTrace
  rw [cutoffCommutator_one_sub, cutoffCommutator_one_sub]
  apply congrArg opTrace
  rw [map_neg]
  noncomm_ring

omit [CompleteSpace H] in
/-- Cutoff commutators are covariant under conjugation by an involution. -/
theorem cutoffCommutator_conjugate_involution
    (J e T : H →L[ℂ] H) (hJ : J * J = 1) :
    cutoffCommutator (J * e * J) (J * T * J) =
      J * cutoffCommutator e T * J := by
  change (J * T * J) * (J * e * J) - (J * e * J) * (J * T * J) =
    J * (T * e - e * T) * J
  calc
    (J * T * J) * (J * e * J) - (J * e * J) * (J * T * J) =
        J * T * (J * J) * e * J - J * e * (J * J) * T * J := by
      noncomm_ring
    _ = J * T * e * J - J * e * T * J := by rw [hJ]; simp
    _ = J * (T * e - e * T) * J := by noncomm_ring

omit [CompleteSpace H] in
/-- Double cutoff curvature is covariant under conjugation by an involution. -/
theorem cutoffWardCurvature_conjugate_involution
    (J e T : H →L[ℂ] H) (hJ : J * J = 1) :
    cutoffWardCurvature (J * e * J) (J * T * J) =
      J * cutoffWardCurvature e T * J := by
  rw [cutoffWardCurvature, cutoffCommutator_conjugate_involution J e T hJ,
    cutoffCommutator_conjugate_involution J e (cutoffCommutator e T) hJ]
  rfl

/-- Adjoint commutes with conjugation by a self-adjoint outer operator. -/
theorem adjoint_conjugate_selfAdjoint_outer
    (J T : H →L[ℂ] H) (hJAdj : adjoint J = J) :
    adjoint (J * T * J) = J * adjoint T * J := by
  simp only [ContinuousLinearMap.mul_def, adjoint_comp, hJAdj]
  rfl

/-- Adjoint cutoff curvature is covariant under a self-adjoint involution, without any
self-adjointness premise on the cutoff. -/
theorem cutoffWardAdjointCurvature_conjugate_involution
    (J e T : H →L[ℂ] H) (hJ : J * J = 1)
    (hJAdj : adjoint J = J) :
    cutoffWardAdjointCurvature (J * e * J) (J * T * J) =
      J * cutoffWardAdjointCurvature e T * J := by
  rw [cutoffWardAdjointCurvature,
    cutoffCommutator_conjugate_involution J e T hJ,
    adjoint_conjugate_selfAdjoint_outer J e hJAdj]
  exact cutoffCommutator_conjugate_involution J (adjoint e)
    (cutoffCommutator e T) hJ

/-- Conjugation by a self-adjoint operator preserves self-adjointness. -/
theorem adjoint_conjugate_of_selfAdjoint
    (J T : H →L[ℂ] H) (hJAdj : adjoint J = J) (hT : adjoint T = T) :
    adjoint (J * T * J) = J * T * J := by
  rw [adjoint_conjugate_selfAdjoint_outer J T hJAdj, hT]

/-- Matrix elements are invariant under simultaneous conjugation by a self-adjoint involution. -/
theorem inner_conjugate_apply_involution
    (J D : H →L[ℂ] H) (hJ : J * J = 1) (hJAdj : adjoint J = J)
    (x y : H) :
    inner ℂ (J x) ((J * D * J) (J y)) = inner ℂ x (D y) := by
  have hJJ (z : H) : J (J z) = z := by
    have hz := DFunLike.congr_fun hJ z
    simpa [mul_apply_eq_comp] using hz
  simp only [mul_apply_eq_comp, hJJ]
  calc
    inner ℂ (J x) (J (D y)) = inner ℂ x (adjoint J (J (D y))) :=
      (adjoint_inner_right J x (J (D y))).symm
    _ = inner ℂ x (D y) := by rw [hJAdj, hJJ]

/-- **Unitary-reflection value law.**  Simultaneously reflecting the cutoff, bounded channel,
source state, and tangent preserves the signed pointed Ward trace exactly. -/
theorem pointedCutoffWardTrace_conjugate_involution
    (J e T : H →L[ℂ] H) (psi chi : H)
    (hJ : J * J = 1) (hJAdj : adjoint J = J) :
    pointedCutoffWardTrace (J * e * J) (J * T * J) (J psi) (J chi) =
      pointedCutoffWardTrace e T psi chi := by
  rw [pointedCutoffWardTrace_eq_adjointCurvature_values,
    pointedCutoffWardTrace_eq_adjointCurvature_values,
    cutoffWardAdjointCurvature_conjugate_involution J e T hJ hJAdj]
  rw [inner_conjugate_apply_involution J (cutoffWardAdjointCurvature e T) hJ hJAdj,
    inner_conjugate_apply_involution J (cutoffWardAdjointCurvature e T) hJ hJAdj]

end

end GaloisForLFunctions.HTGeometry
