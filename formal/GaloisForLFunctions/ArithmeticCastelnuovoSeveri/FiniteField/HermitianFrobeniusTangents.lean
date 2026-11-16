import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.HermitianTangentFactor
import Mathlib.Tactic.LinearCombination

/-!
# The Frobenius point on a Hermitian tangent

The tangent at a geometric Hermitian point meets the curve only at that
point and its square-Frobenius image. Both coordinates are determined:
the tangent value at the second first-coordinate root is exactly the
Frobenius transform of the original second coordinate.
The root multiset retains contact multiplicity `Q` at the original point
and one further copy at its Frobenius image.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (E : Type*) [Field E] [CharP E p]
local notation "Q" => p ^ (s + 1)

/-- Square-Frobenius on actual Hermitian points over any extension field. -/
def hermitianFrobeniusPoint (P : HermitianAffinePoint p s E) : HermitianAffinePoint p s E :=
  ⟨(P.val.1 ^ (Q * Q), P.val.2 ^ (Q * Q)), by
    let φ := (iterateFrobenius E p (s + 1)).comp (iterateFrobenius E p (s + 1))
    have hφ (a : E) : φ a = a ^ (Q * Q) := by
      change (a ^ Q) ^ Q = a ^ (Q * Q)
      exact (pow_mul a Q Q).symm
    have h := congrArg φ P.property
    rw [map_add, map_pow, map_pow] at h
    simpa only [hφ] using h⟩

omit [Fact p.Prime] [CharP E p] in
/-- The tangent passes through its defining point. -/
theorem hermitianTangent_eval_self (P : HermitianAffinePoint p s E) :
    (hermitianTangentPolynomial p s E P).eval P.val.1 = P.val.2 := by
  simp only [hermitianTangentPolynomial, eval_add, eval_C, eval_mul, eval_sub,
    eval_X, sub_self, mul_zero, add_zero]

/-- The second intersection coordinate is the actual Frobenius transform of the point. -/
theorem hermitianTangent_eval_frobenius (P : HermitianAffinePoint p s E) :
    (hermitianTangentPolynomial p s E P).eval (P.val.1 ^ (Q * Q)) =
      P.val.2 ^ (Q * Q) := by
  let a := P.val.1
  let b := P.val.2
  have hpoint : b ^ Q + b = a ^ (Q + 1) := P.property
  have hF := congrArg (iterateFrobenius E p (s + 1)) hpoint
  rw [map_add] at hF
  change (b ^ Q) ^ Q + b ^ Q = (a ^ (Q + 1)) ^ Q at hF
  simp only [pow_succ a Q, mul_pow, ← pow_mul] at hF
  rw [pow_succ a Q] at hpoint
  simp only [hermitianTangentPolynomial, eval_add, eval_C, eval_mul, eval_sub, eval_X]
  change b + a ^ Q * (a ^ (Q * Q) - a) = b ^ (Q * Q)
  linear_combination hpoint - hF

/-- A Hermitian point is Frobenius-fixed exactly when its first coordinate is fixed. -/
theorem hermitianFrobeniusPoint_eq_self_iff (P : HermitianAffinePoint p s E) :
    hermitianFrobeniusPoint p s E P = P ↔ P.val.1 ^ (Q * Q) = P.val.1 := by
  constructor
  · intro h
    exact congrArg (fun U : HermitianAffinePoint p s E => U.val.1) h
  · intro ha
    have hb := hermitianTangent_eval_frobenius p s E P
    rw [ha, hermitianTangent_eval_self] at hb
    apply Subtype.ext
    exact Prod.ext ha hb.symm

/-- The tangent intersection polynomial records contact `Q` and the one remaining Frobenius root. -/
theorem hermitianTangent_intersection_multiset (P : HermitianAffinePoint p s E) :
    ((hermitianTangentPolynomial p s E P) ^ Q +
        hermitianTangentPolynomial p s E P - X ^ (Q + 1)).roots =
      Q • ({P.val.1} : Multiset E) + {(hermitianFrobeniusPoint p s E P).val.1} := by
  rw [hermitianTangent_intersection]
  have hb : (C (P.val.1 ^ (Q * Q)) - X : E[X]) ≠ 0 := by
    rw [← neg_sub X (C (P.val.1 ^ (Q * Q)))]
    exact neg_ne_zero.mpr (monic_X_sub_C (P.val.1 ^ (Q * Q))).ne_zero
  rw [roots_mul (mul_ne_zero (pow_ne_zero Q (monic_X_sub_C P.val.1).ne_zero) hb),
    roots_pow, roots_X_sub_C, ← neg_sub X (C (P.val.1 ^ (Q * Q))), roots_neg,
    roots_X_sub_C]
  rfl

/-- The complete set of geometric curve points on a tangent consists of the point and its Frobenius image. -/
theorem hermitianTangent_incidence_iff (P U : HermitianAffinePoint p s E) :
    (hermitianTangentPolynomial p s E P).eval U.val.1 = U.val.2 ↔
      U = P ∨ U = hermitianFrobeniusPoint p s E P := by
  constructor
  · intro hline
    have hroot : ((hermitianTangentPolynomial p s E P) ^ Q +
        hermitianTangentPolynomial p s E P - X ^ (Q + 1)).eval U.val.1 = 0 := by
      rw [eval_sub, eval_add, eval_pow, eval_pow, eval_X, hline]
      exact sub_eq_zero.mpr U.property
    rcases (hermitianTangent_intersection_roots p s E P U.val.1).mp hroot with ha | ha
    · left
      apply Subtype.ext
      refine Prod.ext ha ?_
      rw [← hline, ha, hermitianTangent_eval_self]
    · right
      apply Subtype.ext
      refine Prod.ext ha ?_
      change U.val.2 = P.val.2 ^ (Q * Q)
      rw [← hline, ha, hermitianTangent_eval_frobenius]
  · rintro (h | h)
    · subst U
      exact hermitianTangent_eval_self p s E P
    · subst U
      exact hermitianTangent_eval_frobenius p s E P

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
