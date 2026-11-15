import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.Ring

/-!
# Iterating a negated Frobenius eigenvector

If one Frobenius block sends an element to its negative, repeated
blocks alternate its sign. The argument uses the Frobenius ring
homomorphism, so the same identities also hold in characteristic two.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] {A : Type*} [CommRing A] [CharP A p]

/-- Repeated Frobenius blocks alternate the sign of a negated eigenvector. -/
theorem frobenius_negated_power (h t : ℕ) (x : A) (hx : x ^ p ^ h = -x) :
    x ^ p ^ (h * t) = (-1 : A) ^ t * x := by
  have hminus : (-1 : A) ^ p ^ h = -1 := by
    change (iterateFrobenius A p h) (-1) = -1
    rw [map_neg, map_one]
  induction t with
  | zero => rw [Nat.mul_zero, pow_zero, pow_one, pow_zero, one_mul]
  | succ t ih =>
    have hsign : ((-1 : A) ^ t) ^ p ^ h = (-1 : A) ^ t := by
      rw [← pow_mul, Nat.mul_comm t (p ^ h), pow_mul, hminus]
    rw [Nat.mul_succ, pow_add, pow_mul, ih, mul_pow, hsign, hx, pow_succ]
    ring

/-- An even number of negated Frobenius blocks fixes the element. -/
theorem frobenius_negated_power_even (h t : ℕ) (x : A) (hx : x ^ p ^ h = -x)
    (ht : Even t) : x ^ p ^ (h * t) = x := by
  rw [frobenius_negated_power p h t x hx, ht.neg_one_pow, one_mul]

/-- An odd number of negated Frobenius blocks negates the element. -/
theorem frobenius_negated_power_odd (h t : ℕ) (x : A) (hx : x ^ p ^ h = -x)
    (ht : Odd t) : x ^ p ^ (h * t) = -x := by
  rw [frobenius_negated_power p h t x hx, ht.neg_one_pow, neg_one_mul]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
