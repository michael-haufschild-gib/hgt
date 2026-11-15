import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants

/-!
# Full tangent contact at rational Hermitian points

Over the field with Q² elements, square Frobenius fixes every point.
The two tangent-intersection factors therefore merge into one power
of degree Q+1, and the tangent meets the affine equation at only that
first coordinate.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "K" => SquareConstantField p s

/-- Every rational Hermitian tangent has the single intersection factor of exponent Q+1. -/
theorem hermitianSquareTangent_intersection (P : HermitianAffinePoint p s K) :
    (hermitianTangentPolynomial p s K P) ^ Q +
        hermitianTangentPolynomial p s K P - X ^ (Q + 1) =
      -((X - C P.val.1) ^ (Q + 1)) := by
  have hfix : P.val.1 ^ (Q * Q) = P.val.1 :=
    (pow_mul P.val.1 Q Q).trans (squareConstantField_frobenius_sq p s P.val.1)
  rw [hermitianTangent_intersection, hfix]
  calc
    _ = -((X - C P.val.1) ^ Q * (X - C P.val.1)) := by ring
    _ = _ := congrArg (fun f : K[X] => -f) (pow_succ (X - C P.val.1) Q).symm

/-- A rational Hermitian tangent meets the affine curve only at its defining first coordinate. -/
theorem hermitianSquareTangent_intersection_root (P : HermitianAffinePoint p s K) (x : K) :
    ((hermitianTangentPolynomial p s K P) ^ Q +
        hermitianTangentPolynomial p s K P - X ^ (Q + 1)).eval x = 0 ↔ x = P.val.1 := by
  rw [hermitianSquareTangent_intersection]
  simp only [eval_neg, eval_pow, eval_sub, eval_X, eval_C, neg_eq_zero]
  constructor
  · intro h
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)
  · intro h
    rw [h, sub_self, zero_pow (Nat.succ_ne_zero Q)]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

