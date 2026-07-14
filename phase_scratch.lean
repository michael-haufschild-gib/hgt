import GaloisForLFunctions.RHTower.SemilocalProjectionConstraintOrientation

open Filter Topology

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

#check IsCompactOperator.smul
#check ContinuousLinearMap.adjoint_smul
#check ContinuousLinearMap.adjoint_add
#check ContinuousLinearMap.adjoint_sub
#check ContinuousLinearMap.adjoint_comp

/-- Canonical quarter-turn of an off-diagonal projection tangent. -/
def projectionPhaseRotation (P D : H →L[ℂ] H) : H →L[ℂ] H :=
  Complex.I • ((1 - P) * D * P - P * D * (1 - P))

theorem projectionNormalCorner_phaseRotation
    (P D : H →L[ℂ] H) (hP2 : P * P = P) :
    projectionNormalCorner P (projectionPhaseRotation P D) =
      Complex.I • projectionNormalCorner P D := by
  unfold projectionPhaseRotation projectionNormalCorner
  rw [mul_smul_comm, smul_mul_assoc]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P - P + P := by rw [hP2]
      _ = 1 - P := by abel
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP2, sub_self]
  simp only [mul_sub, mul_assoc, hQ2, hQP, zero_mul, sub_zero]

theorem adjoint_projectionPhaseRotation
    (P D : H →L[ℂ] H)
    (hPadj : adjoint P = P) (hDadj : adjoint D = D) :
    adjoint (projectionPhaseRotation P D) = projectionPhaseRotation P D := by
  unfold projectionPhaseRotation
  change star (Complex.I • ((1 - P) * D * P - P * D * (1 - P))) = _
  rw [star_smul, star_sub]
  simp only [starRingEnd_apply, map_neg, map_one, Complex.conj_I, neg_smul]
  change -Complex.I •
      (adjoint (((1 - P) * D) ∘L P) - adjoint ((P * D) ∘L (1 - P))) = _
  rw [adjoint_comp, adjoint_comp]
  change -Complex.I •
      (adjoint P ∘L adjoint ((1 - P) ∘L D) -
        adjoint (1 - P) ∘L adjoint (P ∘L D)) = _
  rw [adjoint_comp, adjoint_comp, adjoint_one_sub hPadj, hPadj, hDadj]
  module

theorem phasePolarized_normalSkewGram_isCompact
    (A B : H →L[ℂ] H)
    (h : IsCompactOperator
      (adjoint A * (Complex.I • B) + adjoint (Complex.I • B) * A)) :
    IsCompactOperator (adjoint A * B - adjoint B * A) := by
  have hs := h.smul (-Complex.I)
  have hEq :
      (-Complex.I) •
          (adjoint A * (Complex.I • B) + adjoint (Complex.I • B) * A) =
        adjoint A * B - adjoint B * A := by
    change (-Complex.I) •
        (adjoint A * (Complex.I • B) +
          star (Complex.I • B) * A) = _
    rw [star_smul]
    simp only [starRingEnd_apply, Complex.conj_I]
    module
  rw [hEq] at hs
  exact hs

end

end RHTower
