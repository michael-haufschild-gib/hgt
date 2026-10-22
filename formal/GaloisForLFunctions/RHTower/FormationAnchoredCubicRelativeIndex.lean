import GaloisForLFunctions.RHTower.FormationAnchoredCubicHomotopyDefect
import GaloisForLFunctions.RHTower.RestrictedProjectionCubicRelativeIndex

/-!
# Trace of the cubic defect equals the relative index of two projections, with cocycle law

For orthogonal projections `R`, `P` on a complex Hilbert space whose difference `R - P` is
Hilbert–Schmidt, the cubic operator `(R - P)³` is trace class and its trace equals the relative
index `dim ker(R - P - 1) - dim ker(R - P + 1)`. This module restates that identity for the
formation-anchored cubic defect and derives the additive cocycle law
`ind(R, P) = ind(R, Q) + ind(Q, P)` for three projections with Hilbert–Schmidt successive
differences.

## Main results

- `opTrace_formationAnchoredCubicDefect_eq_relativeIndex`: `tr (R - P)³ = ind(R, P)`.
- `restrictedProjectionRelativeIndex_cocycle`: `ind(R, P) = ind(R, Q) + ind(Q, P)`.
- `formationAnchoredCubicRelativeIndex_closed`: both statements bundled, universally quantified
  over the Hilbert space.

## Hypotheses

Unconditional as operator theory. The theorems assume `R`, `P` (and `Q`) are orthogonal
projections (idempotent and self-adjoint) and that the relevant differences `R - P`, or
`R - Q` and `Q - P`, are Hilbert–Schmidt.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For orthogonal projections `R`, `P` with `R - P` Hilbert–Schmidt, the trace of the cubic
defect `(R - P)³` equals the integer relative index `ind(R, P)`. -/
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

/-- Cocycle law: for orthogonal projections `R`, `Q`, `P` with `R - Q` and `Q - P`
Hilbert–Schmidt, `ind(R, P) = ind(R, Q) + ind(Q, P)`. -/
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

/-- Bundled form over every complex Hilbert space: for orthogonal projections `R`, `Q`, `P` with
`R - Q`, `Q - P` Hilbert–Schmidt, `tr (R - P)³ = ind(R, P)` and `ind(R, P) = ind(R, Q) + ind(Q, P)`. -/
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
