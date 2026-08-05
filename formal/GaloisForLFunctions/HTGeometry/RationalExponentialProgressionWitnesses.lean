import GaloisForLFunctions.HTGeometry.RationalExponentialProgressionGrowth

/-!
# Rational-exponential progressions exist

The representation is a finite sum of rational functions of the index times exponentials.  The
empty sum represents the zero sequence, one term with unit rational part represents a pure
exponential, and one term with unit exponent represents an arbitrary rational function of the
index — so the growth law applies to a class containing both geometric and polynomial behaviour.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The zero sequence has a rational-exponential representation, with no terms. -/
theorem hasRationalExponentialProgressionRepresentation_zero :
    HasRationalExponentialProgressionRepresentation (fun _ => 0) := by
  refine ⟨0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun n => ?_⟩
  simp

/-- A pure exponential has a rational-exponential representation. -/
theorem hasRationalExponentialProgressionRepresentation_exp (lambda : ℂ) :
    HasRationalExponentialProgressionRepresentation
      (fun n => Complex.exp (lambda * (n : ℂ))) := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => lambda, fun _ => one_ne_zero, fun n => ?_⟩
  simp

/-- Every rational function of the index has a rational-exponential representation. -/
theorem hasRationalExponentialProgressionRepresentation_ratio
    (num den : Polynomial ℂ) (hden : den ≠ 0) :
    HasRationalExponentialProgressionRepresentation
      (fun n => num.eval (n : ℂ) / den.eval (n : ℂ)) := by
  refine ⟨1, fun _ => num, fun _ => den, fun _ => 0, fun _ => hden, fun n => ?_⟩
  simp

end GaloisForLFunctions.HTGeometry
