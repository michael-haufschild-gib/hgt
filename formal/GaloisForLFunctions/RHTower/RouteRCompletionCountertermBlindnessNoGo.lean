import GaloisForLFunctions.RHTower.RouteRBurnolReflectionPartnerCurrent
import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletedHeadDissipation

/-!
# Route R reflection-even completion counterterm blindness

Every scalar counterterm built from reflection-even completion data cancels
from the reflection-odd current.  The actual prime-two completion can make the
dressed current negative while the bare current remains strictly positive at
every hypothetical right-half Xi divisor, so dressed negativity cannot imply
the missing physical dissipativity.
-/

namespace RHTower

noncomputable section

/-- Dressed current for an abstract reflection, even counterterm, and bare
oriented current. -/
def routeRCompletionDressedCurrent {X : Type*}
    (A J : X → ℝ) (x : X) : ℝ := A x + J x

theorem routeRCompletionDressedCurrent_sub_reflection
    {X : Type*} (dagger : X → X) (A J : X → ℝ)
    (hA : ∀ x, A (dagger x) = A x) (x : X) :
    routeRCompletionDressedCurrent A J x -
        routeRCompletionDressedCurrent A J (dagger x) =
      J x - J (dagger x) := by
  rw [routeRCompletionDressedCurrent, routeRCompletionDressedCurrent,
    hA x]
  ring

theorem routeRCompletionDressedCurrent_eq_reflection_iff
    {X : Type*} (dagger : X → X) (A J : X → ℝ)
    (hA : ∀ x, A (dagger x) = A x) (x : X) :
    routeRCompletionDressedCurrent A J x =
        routeRCompletionDressedCurrent A J (dagger x) ↔
      J x = J (dagger x) := by
  rw [← sub_eq_zero, routeRCompletionDressedCurrent_sub_reflection
    dagger A J hA x, sub_eq_zero]

/-- Actual prime-two completion specialization: dressed reflection equality
cuts out exactly the critical line. -/
theorem routeR_xiCompletionDressedReflection_eq_iff_criticalLine
    (rho : XiDivisorSupport) :
    burnolXiCompletionDressedHeadCurrent (rho : ℂ) =
        burnolXiCompletionDressedHeadCurrent
          (burnolXiReflectionPartner (rho : ℂ)) ↔
      (rho : ℂ).re = 1 / 2 :=
  xiDivisor_burnolXiCompletionDressedHeadCurrent_eq_reflectionPartner_iff rho

/-- Actual counterexample to the invalid inference from dressed negativity to
bare dissipativity: on every hypothetical right-half divisor the signs are
strictly opposite. -/
theorem routeR_xiCompletionDressedNegativity_does_not_imply_bareDissipativity
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolXiCompletionDressedHeadCurrent (rho : ℂ) < 0 ∧
      ¬ burnolCartierDividedShiftHeadFlux (rho : ℂ) ≤ 0 := by
  obtain ⟨hdressed, hbare⟩ :=
    xiDivisor_burnolCompletionDressed_and_bareHeadCurrents_opposed rho h
  exact ⟨hdressed, not_le.mpr hbare⟩

end

end RHTower
