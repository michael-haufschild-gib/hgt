import GaloisForLFunctions.RHTower.RestrictedProjectionCubicCocycle
import GaloisForLFunctions.RHTower.TraceNormLimit

/-!
# Formation-anchored cubic homotopy defect: operator core

This module formalizes the exact operator-valued part of FACHD.  For three admitted
polarizations, the long cubic defect differs from the two adjacent cubic defects by a genuine
Schatten-one associator.  Its trace vanishes exactly, while the defect itself retains the full
noncommutative operator data.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- FACHD's relative cubic operator `T(R,P) = (R-P)^3`. -/
abbrev formationAnchoredCubicDefect (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  restrictedProjectionCubicDefect R P

/-- Exact operator-valued associator from `(FACHD.8)`. -/
def formationAnchoredCubicAssociator
    (R Q P : H →L[ℂ] H) : H →L[ℂ] H :=
  formationAnchoredCubicDefect R P -
    formationAnchoredCubicDefect R Q -
      formationAnchoredCubicDefect Q P

/-- Adjacent Hilbert--Schmidt displacements make the long displacement Hilbert--Schmidt. -/
theorem formationAnchoredLongDisplacement_isHilbertSchmidt
    (R Q P : H →L[ℂ] H)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    (restrictedProjectionDisplacement R P).IsHilbertSchmidt := by
  have hsum := hRQ.add hQP
  have heq : restrictedProjectionDisplacement R P =
      restrictedProjectionDisplacement R Q +
        restrictedProjectionDisplacement Q P := by
    simp only [restrictedProjectionDisplacement]
    abel
  rw [heq]
  exact hsum

/-- FACHD's noncommutative associator is an actual nuclear operator. -/
theorem formationAnchoredCubicAssociator_memSchattenClass_one
    (R Q P : H →L[ℂ] H)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) := by
  have hRP := formationAnchoredLongDisplacement_isHilbertSchmidt R Q P hRQ hQP
  have hlong := restrictedProjectionCubicDefect_memSchattenClass_one R P hRP
  have hleft := restrictedProjectionCubicDefect_memSchattenClass_one R Q hRQ
  have hright := restrictedProjectionCubicDefect_memSchattenClass_one Q P hQP
  exact (hlong.one_sub hleft).one_sub hright

/-- Exact abelianization law: the FACHD associator has zero ordinary operator trace. -/
theorem opTrace_formationAnchoredCubicAssociator_eq_zero
    (R Q P : H →L[ℂ] H)
    (hR : IsIdempotentElem R) (hQ : IsIdempotentElem Q) (hP : IsIdempotentElem P)
    (hRQ : (restrictedProjectionDisplacement R Q).IsHilbertSchmidt)
    (hQP : (restrictedProjectionDisplacement Q P).IsHilbertSchmidt) :
    opTrace (formationAnchoredCubicAssociator R Q P) = 0 := by
  have hRP := formationAnchoredLongDisplacement_isHilbertSchmidt R Q P hRQ hQP
  have hlong := restrictedProjectionCubicDefect_memSchattenClass_one R P hRP
  have hleft := restrictedProjectionCubicDefect_memSchattenClass_one R Q hRQ
  have hright := restrictedProjectionCubicDefect_memSchattenClass_one Q P hQP
  change opTrace (restrictedProjectionCubicDefect R P -
    restrictedProjectionCubicDefect R Q -
      restrictedProjectionCubicDefect Q P) = 0
  rw [
    opTrace_sub_of_memSchattenClass_one (hlong.one_sub hleft) hright,
    opTrace_sub_of_memSchattenClass_one hlong hleft,
    opTrace_restrictedProjectionCubicDefect_cocycle R Q P hR hQ hP hRQ hQP]
  abel

/-- Closed, hypothesis-free certificate for all operator identities of Theorem FACHD-A and the
nuclear associator `(FACHD.8)`.  Admission conditions remain inside the universally quantified
statement; this declaration itself has no premises. -/
theorem formationAnchoredCubicHomotopyDefect_operator_closed :
    ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (R Q P : H →L[ℂ] H),
      IsIdempotentElem R → IsIdempotentElem Q → IsIdempotentElem P →
      ContinuousLinearMap.adjoint R = R →
      ContinuousLinearMap.adjoint Q = Q →
      ContinuousLinearMap.adjoint P = P →
      (restrictedProjectionDisplacement R Q).IsHilbertSchmidt →
      (restrictedProjectionDisplacement Q P).IsHilbertSchmidt →
      ContinuousLinearMap.adjoint (formationAnchoredCubicDefect R P) =
          formationAnchoredCubicDefect R P ∧
        MemSchattenClass 1 (formationAnchoredCubicDefect R P) ∧
        formationAnchoredCubicDefect R P =
          restrictedProjectionPositiveChannel R P -
            restrictedProjectionPositiveChannel P R ∧
        MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
        opTrace (formationAnchoredCubicAssociator R Q P) = 0 := by
  intro H _ _ _ R Q P hR hQ hP hRadj hQadj hPadj hRQ hQP
  have hRP := formationAnchoredLongDisplacement_isHilbertSchmidt R Q P hRQ hQP
  exact ⟨adjoint_restrictedProjectionCubicDefect R P hRadj hPadj,
    restrictedProjectionCubicDefect_memSchattenClass_one R P hRP,
    restrictedProjectionCubicDefect_eq_channels R P hR hP,
    formationAnchoredCubicAssociator_memSchattenClass_one R Q P hRQ hQP,
    opTrace_formationAnchoredCubicAssociator_eq_zero R Q P hR hQ hP hRQ hQP⟩

end RHTower
