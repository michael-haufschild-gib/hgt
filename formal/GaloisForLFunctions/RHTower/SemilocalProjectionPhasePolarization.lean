import GaloisForLFunctions.RHTower.SemilocalProjectionConstraintOrientation

/-!
# Phase-polarized projection curvature

The symmetric mixed-curvature identity for a projection family does not lose the orientation
sector.  The canonical quarter-turn

`J_P(D) = i ((1 - P) D P - P D (1 - P))`

is self-adjoint whenever `P` and `D` are self-adjoint, is automatically tangent to the
idempotent constraint, and rotates its normal corner by exactly `i`.  Substituting this rotated
direction into the existing symmetric mixed-curvature theorem recovers the antisymmetric normal
Gram, hence the connection curvature, exactly.

The compactness endpoint only asks that the base-compressed mixed derivative `P D_st P` be
compact.  It does not require the full mixed derivative, or the whole projection family relative
to its base, to be compact.  For the semilocal Sonin route this turns the remaining orientation
problem into a source-side phase-polarized mixed-curvature construction.
-/

open Filter Topology

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Canonical quarter-turn of an off-diagonal projection tangent. -/
def projectionPhaseRotation (P D : H →L[ℂ] H) : H →L[ℂ] H :=
  Complex.I • ((1 - P) * D * P - P * D * (1 - P))

omit [CompleteSpace H] in
/-- The canonical quarter-turn rotates the normal corner by exactly `i`. -/
theorem projectionNormalCorner_phaseRotation
    (P D : H →L[ℂ] H) (hP2 : P * P = P) :
    projectionNormalCorner P (projectionPhaseRotation P D) =
      Complex.I • projectionNormalCorner P D := by
  unfold projectionPhaseRotation projectionNormalCorner
  let Q : H →L[ℂ] H := 1 - P
  let X : H →L[ℂ] H := Q * D * P
  let Y : H →L[ℂ] H := P * D * Q
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + P := by rw [hP2]
      _ = 1 - P := by abel
  have hQP : Q * P = 0 := by
    dsimp only [Q]
    rw [sub_mul, one_mul, hP2, sub_self]
  have hQX : Q * X = X := by
    dsimp only [X]
    calc
      Q * (Q * D * P) = (Q * Q) * D * P := by simp only [mul_assoc]
      _ = Q * D * P := by rw [hQ2]
  have hQY : Q * Y = 0 := by
    dsimp only [Y]
    calc
      Q * (P * D * Q) = (Q * P) * D * Q := by simp only [mul_assoc]
      _ = 0 := by simp [hQP]
  have hXP : X * P = X := by
    dsimp only [X]
    calc
      Q * D * P * P = Q * D * (P * P) := by simp only [mul_assoc]
      _ = Q * D * P := by rw [hP2]
  have hYP : Y * P = 0 := by
    dsimp only [Y]
    calc
      P * D * Q * P = P * D * (Q * P) := by simp only [mul_assoc]
      _ = 0 := by rw [hQP, mul_zero]
  change Q * (Complex.I • (X - Y)) * P = Complex.I • X
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_sub, hQX, hQY, hXP, sub_zero]

/-- The canonical quarter-turn preserves self-adjointness. -/
theorem adjoint_projectionPhaseRotation
    (P D : H →L[ℂ] H)
    (hPadj : adjoint P = P) (hDadj : adjoint D = D) :
    adjoint (projectionPhaseRotation P D) = projectionPhaseRotation P D := by
  unfold projectionPhaseRotation
  change star (Complex.I • ((1 - P) * D * P - P * D * (1 - P))) = _
  rw [star_smul, star_sub]
  rw [show star (Complex.I : ℂ) = -Complex.I by exact Complex.conj_I]
  change -Complex.I •
      (adjoint (((1 - P) * D) ∘L P) - adjoint ((P * D) ∘L (1 - P))) = _
  rw [adjoint_comp, adjoint_comp]
  change -Complex.I •
      (adjoint P ∘L adjoint ((1 - P) ∘L D) -
        adjoint (1 - P) ∘L adjoint (P ∘L D)) = _
  rw [adjoint_comp, adjoint_comp, adjoint_one_sub hPadj, hPadj, hDadj]
  simp only [mul_assoc]
  module

/-- Phase polarization turns the symmetric normal Gram into `i` times the antisymmetric normal
Gram exactly. -/
theorem phasePolarized_normalGram_eq_smul_normalSkewGram
    (A B : H →L[ℂ] H) :
    adjoint A * (Complex.I • B) + adjoint (Complex.I • B) * A =
      Complex.I • (adjoint A * B - adjoint B * A) := by
  change adjoint A * (Complex.I • B) + star (Complex.I • B) * A = _
  rw [star_smul, mul_smul_comm, smul_mul_assoc]
  rw [show star (Complex.I : ℂ) = -Complex.I by exact Complex.conj_I]
  module

/-- A compact symmetric Gram with one normal direction rotated by `i` forces the original
antisymmetric Gram to be compact. -/
theorem phasePolarized_normalSkewGram_isCompact
    (A B : H →L[ℂ] H)
    (h : IsCompactOperator
      (adjoint A * (Complex.I • B) + adjoint (Complex.I • B) * A)) :
    IsCompactOperator (adjoint A * B - adjoint B * A) := by
  rw [phasePolarized_normalGram_eq_smul_normalSkewGram] at h
  let T : H →L[ℂ] H := adjoint A * B - adjoint B * A
  change IsCompactOperator (Complex.I • T) at h
  have hs : IsCompactOperator ((-Complex.I) • (Complex.I • T)) := by
    exact h.smul (-Complex.I)
  have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  have heq : (-Complex.I) • (Complex.I • T) = T := by
    rw [smul_smul, hI, one_smul]
  change IsCompactOperator T
  rw [← heq]
  exact hs

omit [CompleteSpace H] in
/-- The canonical quarter-turn is tangent to the idempotent constraint, without requiring the
input operator itself to satisfy the tangent equation. -/
theorem projectionPhaseRotation_tangent
    (P D : H →L[ℂ] H) (hP2 : P * P = P) :
    projectionPhaseRotation P D * P + P * projectionPhaseRotation P D =
      projectionPhaseRotation P D := by
  unfold projectionPhaseRotation
  let Q : H →L[ℂ] H := 1 - P
  let X : H →L[ℂ] H := Q * D * P
  let Y : H →L[ℂ] H := P * D * Q
  have hQP : Q * P = 0 := by
    dsimp only [Q]
    rw [sub_mul, one_mul, hP2, sub_self]
  have hPQ : P * Q = 0 := by
    dsimp only [Q]
    rw [mul_sub, mul_one, hP2, sub_self]
  have hXP : X * P = X := by
    dsimp only [X]
    calc
      Q * D * P * P = Q * D * (P * P) := by simp only [mul_assoc]
      _ = Q * D * P := by rw [hP2]
  have hYP : Y * P = 0 := by
    dsimp only [Y]
    calc
      P * D * Q * P = P * D * (Q * P) := by simp only [mul_assoc]
      _ = 0 := by rw [hQP, mul_zero]
  have hPX : P * X = 0 := by
    dsimp only [X]
    calc
      P * (Q * D * P) = (P * Q) * D * P := by simp only [mul_assoc]
      _ = 0 := by simp [hPQ]
  have hPY : P * Y = Y := by
    dsimp only [Y]
    calc
      P * (P * D * Q) = (P * P) * D * Q := by simp only [mul_assoc]
      _ = P * D * Q := by rw [hP2]
  change (Complex.I • (X - Y)) * P + P * (Complex.I • (X - Y)) =
    Complex.I • (X - Y)
  rw [smul_mul_assoc, mul_smul_comm]
  simp only [sub_mul, mul_sub, hXP, hYP, hPX, hPY, zero_sub, sub_zero]
  module

/-- The base-compressed mixed derivative in a phase-rotated projection family is exactly minus
`i` times the antisymmetric normal Gram of the unrotated directions. -/
theorem selfAdjointIdempotentFamily_phaseRotated_mixed_identity
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (D Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t ↦ F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s ↦ F s 0)
      (projectionPhaseRotation (F 0 0) D) 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDadj : adjoint D = D)
    (hDtadj : adjoint (Dt 0) = Dt 0) :
    F 0 0 * Dst * F 0 0 =
      -(Complex.I •
        (adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
            projectionNormalCorner (F 0 0) D -
          adjoint (projectionNormalCorner (F 0 0) D) *
            projectionNormalCorner (F 0 0) (Dt 0))) := by
  have hP2 : F 0 0 * F 0 0 = F 0 0 := (hidem 0).eq_of_nhds
  have hphaseAdj :
      adjoint (projectionPhaseRotation (F 0 0) D) =
        projectionPhaseRotation (F 0 0) D :=
    adjoint_projectionPhaseRotation (F 0 0) D hPadj hDadj
  have hmixed := selfAdjointIdempotentFamily_mixed_normalGram_identity
    F Dt (projectionPhaseRotation (F 0 0) D) Dst
      ht hidem hs hst hPadj hphaseAdj hDtadj
  rw [projectionNormalCorner_phaseRotation (F 0 0) D hP2] at hmixed
  change F 0 0 * Dst * F 0 0 =
    -(adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          (Complex.I • projectionNormalCorner (F 0 0) D) +
        adjoint (Complex.I • projectionNormalCorner (F 0 0) D) *
          projectionNormalCorner (F 0 0) (Dt 0)) at hmixed
  rw [phasePolarized_normalGram_eq_smul_normalSkewGram] at hmixed
  exact hmixed

/-- After the canonical phase rotation, symmetric mixed curvature is exactly `i` times the
connection-orientation curvature of the unrotated directions. -/
theorem selfAdjointIdempotentFamily_phaseRotated_mixed_eq_connectionCurvature
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (D Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t ↦ F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s ↦ F s 0)
      (projectionPhaseRotation (F 0 0) D) 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDadj : adjoint D = D)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hDtan : D * F 0 0 + F 0 0 * D = D) :
    F 0 0 * Dst * F 0 0 =
      -(Complex.I • projectionConnectionCurvature (F 0 0) D (Dt 0)) := by
  have hmixed := selfAdjointIdempotentFamily_phaseRotated_mixed_identity
    F Dt D Dst ht hidem hs hst hPadj hDadj hDtadj
  have hP2 : F 0 0 * F 0 0 = F 0 0 := (hidem 0).eq_of_nhds
  have hDttan : Dt 0 * F 0 0 + F 0 0 * Dt 0 = Dt 0 :=
    idempotentFamily_tangent_identity (F 0) (Dt 0) (ht 0) (hidem 0)
  have hconnection := projectionConnectionCurvature_eq_normalSkewGram
    (F 0 0) D (Dt 0) hP2 hPadj hDadj hDtadj hDtan hDttan
  rw [hconnection]
  exact hmixed

/-- Compactness of only the base-compressed phase-polarized mixed derivative forces compactness
of the oriented normal Gram. -/
theorem selfAdjointIdempotentFamily_phaseRotated_normalSkewGram_isCompact
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (D Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t ↦ F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s ↦ F s 0)
      (projectionPhaseRotation (F 0 0) D) 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDadj : adjoint D = D)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hcompressed : IsCompactOperator (F 0 0 * Dst * F 0 0)) :
    IsCompactOperator
      (adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          projectionNormalCorner (F 0 0) D -
        adjoint (projectionNormalCorner (F 0 0) D) *
          projectionNormalCorner (F 0 0) (Dt 0)) := by
  let O : H →L[ℂ] H :=
    adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
        projectionNormalCorner (F 0 0) D -
      adjoint (projectionNormalCorner (F 0 0) D) *
        projectionNormalCorner (F 0 0) (Dt 0)
  have hmixed := selfAdjointIdempotentFamily_phaseRotated_mixed_identity
    F Dt D Dst ht hidem hs hst hPadj hDadj hDtadj
  have hscaled := hcompressed.smul Complex.I
  have hEq : Complex.I • (F 0 0 * Dst * F 0 0) = O := by
    change Complex.I • (F 0 0 * Dst * F 0 0) = _
    rw [hmixed]
    dsimp only [O]
    simp only [smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
  change IsCompactOperator (O : H → H)
  rw [← hEq]
  simpa only [ContinuousLinearMap.coe_smul] using hscaled

/-- Full mixed compactness is a sufficient, but not necessary, source input. -/
theorem selfAdjointIdempotentFamily_phaseRotated_normalSkewGram_isCompact_of_mixed
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (D Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t ↦ F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s ↦ F s 0)
      (projectionPhaseRotation (F 0 0) D) 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDadj : adjoint D = D)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hDst : IsCompactOperator Dst) :
    IsCompactOperator
      (adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          projectionNormalCorner (F 0 0) D -
        adjoint (projectionNormalCorner (F 0 0) D) *
          projectionNormalCorner (F 0 0) (Dt 0)) := by
  apply selfAdjointIdempotentFamily_phaseRotated_normalSkewGram_isCompact
    F Dt D Dst ht hidem hs hst hPadj hDadj hDtadj
  simpa only [mul_assoc] using (hDst.comp_clm (F 0 0)).clm_comp (F 0 0)

end

end RHTower
