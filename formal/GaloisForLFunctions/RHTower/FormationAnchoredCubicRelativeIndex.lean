import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect
import GaloisForLFunctions.RHTower.RestrictedProjectionCubicRelativeIndex

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem opTrace_formationAnchoredCubicDefect_eq_relativeIndex
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRP : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    opTrace (formationAnchoredCubicDefect R P) =
      (restrictedProjectionRelativeIndex R P : ℂ) :=
  opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
    R P hR hP hRadj hPadj hRP

theorem restrictedProjectionRelativeIndex_cocycle
    (R Q P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hRadj : ContinuousLinearMap.adjoint R = R)
    (hQadj : ContinuousLinearMap.adjoint Q = Q)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    restrictedProjectionRelativeIndex R P =
      restrictedProjectionRelativeIndex R Q +
        restrictedProjectionRelativeIndex Q P := by
  have hRP := formationAnchoredLongDisplacement_isHilbertSchmidt R Q P hRQ hQP
  have hcocycle := opTrace_restrictedProjectionCubicDefect_cocycle
    R Q P hR hQ hP hRQ hQP
  rw [opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
      R P hR hP hRadj hPadj hRP,
    opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
      R Q hR hQ hRadj hQadj hRQ,
    opTrace_restrictedProjectionCubicDefect_eq_relativeIndex
      Q P hQ hP hQadj hPadj hQP,
    ← Int.cast_add] at hcocycle
  exact_mod_cast hcocycle

theorem formationAnchoredCubicRelativeIndex_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (R Q P : H →L[ℂ] H),
      IsIdempotentElem R → IsIdempotentElem Q → IsIdempotentElem P →
      ContinuousLinearMap.adjoint R = R →
      ContinuousLinearMap.adjoint Q = Q →
      ContinuousLinearMap.adjoint P = P →
      (restrictedProjectionDisplacement R Q).IsHilbertSchmidt →
      (restrictedProjectionDisplacement Q P).IsHilbertSchmidt →
      opTrace (formationAnchoredCubicDefect R P) =
          (restrictedProjectionRelativeIndex R P : ℂ) ∧
        restrictedProjectionRelativeIndex R P =
          restrictedProjectionRelativeIndex R Q +
            restrictedProjectionRelativeIndex Q P := by
  intro H _ _ _ R Q P hR hQ hP hRadj hQadj hPadj hRQ hQP
  have hRP := formationAnchoredLongDisplacement_isHilbertSchmidt R Q P hRQ hQP
  exact ⟨opTrace_formationAnchoredCubicDefect_eq_relativeIndex
      R P hR hP hRadj hPadj hRP,
    restrictedProjectionRelativeIndex_cocycle
      R Q P hR hQ hP hRadj hQadj hPadj hRQ hQP⟩

end RHTower
