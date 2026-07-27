import GaloisForLFunctions.HTGeometry.PrimeOrientationConstraintOpacity

/-!
# Recurrence of the anchored skeleton patterns

The anchored skeleton law consumes infinitude of the fibers of the pattern map over the all-positive
and single-negative patterns.  The exact constraint realization has those fibers infinite precisely
when the patterns are prescribed, but only through an `Iff`, so the premise instances were never
named.

* `constraintOrientation_allPositive_fiber_infinite`,
  `constraintOrientation_singleNegative_fiber_infinite`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {J : Type*} [Fintype J]

theorem constraintOrientation_allPositive_fiber_infinite (R : Set (J → Bool))
    (h : allPositiveOrientationPattern ∈ R) :
    {p : R × ℕ | primeOrientationPattern (constraintOrientation R) p =
      allPositiveOrientationPattern}.Infinite :=
  (constraintOrientation_pattern_fiber_infinite_iff R _).2 h

theorem constraintOrientation_singleNegative_fiber_infinite [DecidableEq J] (R : Set (J → Bool))
    (j : J) (h : singleNegativeOrientationPattern j ∈ R) :
    {p : R × ℕ | primeOrientationPattern (constraintOrientation R) p =
      singleNegativeOrientationPattern j}.Infinite :=
  (constraintOrientation_pattern_fiber_infinite_iff R _).2 h

end GaloisForLFunctions.HTGeometry
