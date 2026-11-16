import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import Mathlib.Tactic.LinearCombination

/-!
# Local equation relative to a Hermitian tangent

Subtracting the tangent line gives an additive equation whose right side
records contact at the original point and its square-Frobenius image.
Unlike tangent translations, this identity needs no rationality of the point.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [CharP E p]
local notation "Q" => p ^ (s + 1)

/-- The difference between a point's second coordinate and the tangent line at another point. -/
def hermitianTangentDifference (P U : HermitianAffinePoint p s E) : E :=
  U.val.2 - (hermitianTangentPolynomial p s E P).eval U.val.1

/-- The tangent difference satisfies the exact additive local equation. -/
theorem hermitianTangentDifference_equation (P U : HermitianAffinePoint p s E) :
    hermitianTangentDifference p s E P U ^ Q + hermitianTangentDifference p s E P U =
      (U.val.1 - P.val.1) ^ Q * (U.val.1 - P.val.1 ^ (Q * Q)) := by
  have h := congrArg (fun f : E[X] => f.eval U.val.1)
    (hermitianTangent_intersection p s E P)
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at h
  rw [hermitianTangentDifference, sub_pow_char_pow]
  linear_combination U.property - h

/-- At a Frobenius-fixed first coordinate, both tangent contact factors coincide. -/
theorem hermitianTangentDifference_equation_of_fixed
    (P U : HermitianAffinePoint p s E) (hP : P.val.1 ^ (Q * Q) = P.val.1) :
    hermitianTangentDifference p s E P U ^ Q + hermitianTangentDifference p s E P U =
      (U.val.1 - P.val.1) ^ (Q + 1) := by
  rw [hermitianTangentDifference_equation, hP, pow_succ]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
