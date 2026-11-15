import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-!
# Tangent intersections on the Hermitian equation

Substitution of the tangent line at an affine point factors the
intersection polynomial into a power at that point and one factor at
its square-Frobenius image. This identity holds over every extension
of the constant field and in every positive characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [CharP E p]
local notation "Q" => p ^ (s + 1)

/-- Actual affine points of the Hermitian equation `b^Q+b=a^(Q+1)`. -/
def HermitianAffinePoint := {P : E × E // P.2 ^ Q + P.2 = P.1 ^ (Q + 1)}

/-- The tangent line, expressed as its second coordinate in terms of the first. -/
def hermitianTangentPolynomial (P : HermitianAffinePoint p s E) : E[X] :=
  C P.val.2 + C (P.val.1 ^ Q) * (X - C P.val.1)

/-- Tangent substitution has contact factor `(X-a)^Q` and remaining root `a^(Q²)`. -/
theorem hermitianTangent_intersection (P : HermitianAffinePoint p s E) :
    (hermitianTangentPolynomial p s E P) ^ Q +
        hermitianTangentPolynomial p s E P - X ^ (Q + 1) =
      (X - C P.val.1) ^ Q * (C (P.val.1 ^ (Q * Q)) - X) := by
  let a := P.val.1
  let b := P.val.2
  have hadd (U V : E[X]) : (U + V) ^ Q = U ^ Q + V ^ Q := by
    change iterateFrobenius E[X] p (s + 1) (U + V) =
      iterateFrobenius E[X] p (s + 1) U + iterateFrobenius E[X] p (s + 1) V
    exact map_add _ _ _
  have hsub (U V : E[X]) : (U - V) ^ Q = U ^ Q - V ^ Q := by
    change iterateFrobenius E[X] p (s + 1) (U - V) =
      iterateFrobenius E[X] p (s + 1) U - iterateFrobenius E[X] p (s + 1) V
    exact map_sub _ _ _
  have hpoint : (C b) ^ Q + C b = (C a) ^ (Q + 1) := by
    simpa only [map_add, map_pow] using congrArg (C : E → E[X]) P.property
  have hcoeff : C (a ^ Q) = (C a) ^ Q := map_pow C a Q
  have hdouble : ((C a) ^ Q) ^ Q = C (a ^ (Q * Q)) :=
    (pow_mul (C a) Q Q).symm.trans (map_pow C a (Q * Q)).symm
  change (C b + C (a ^ Q) * (X - C a)) ^ Q +
    (C b + C (a ^ Q) * (X - C a)) - X ^ (Q + 1) =
      (X - C a) ^ Q * (C (a ^ (Q * Q)) - X)
  simp only [hcoeff, hadd, mul_pow, hdouble]
  calc
    _ = ((C b) ^ Q + C b) + C (a ^ (Q * Q)) * (X - C a) ^ Q +
        (C a) ^ Q * (X - C a) - X ^ (Q + 1) := by ring
    _ = _ := by
      rw [hpoint]
      simp only [hsub, pow_succ (C a) Q, pow_succ (X : E[X]) Q]
      ring

/-- The tangent intersection has exactly the original and square-Frobenius first coordinates. -/
theorem hermitianTangent_intersection_roots (P : HermitianAffinePoint p s E) (x : E) :
    ((hermitianTangentPolynomial p s E P) ^ Q +
      hermitianTangentPolynomial p s E P - X ^ (Q + 1)).eval x = 0 ↔
        x = P.val.1 ∨ x = P.val.1 ^ (Q * Q) := by
  rw [hermitianTangent_intersection]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h))
    · exact Or.inr (sub_eq_zero.mp h).symm
  · rintro (h | h)
    · rw [h, sub_self, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), zero_mul]
    · rw [h, sub_self, mul_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

