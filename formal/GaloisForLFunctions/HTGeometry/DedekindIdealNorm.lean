import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ideal cardinality norms in every characteristic

The cardinality of an ideal quotient is multiplicative in an infinite Dedekind
domain. Chinese remainders handle coprime factors, and the successive prime-power
quotients give the prime-power formula. Infinitude, rather than characteristic
zero, is the condition needed to send the zero ideal to zero.
-/

namespace GaloisForLFunctions.HTGeometry

open Submodule

noncomputable section

variable (A : Type*) [CommRing A] [IsDedekindDomain A] [Infinite A]

theorem ideal_cardinality_mul (I J : Ideal A) :
    Nat.card (A ⧸ (I * J)) = Nat.card (A ⧸ I) * Nat.card (A ⧸ J) := by
  change cardQuot (I * J) = cardQuot I * cardQuot J
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot A A)
    (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
    (fun {I} i hI =>
      have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
      cardQuot_pow_of_prime hI.ne_zero)
    fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.isUnit_iff.mp
        (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

/-- The ideal norm defined by quotient cardinality, valid also in positive characteristic. -/
def idealCardinality : Ideal A →*₀ ℕ where
  toFun I := Nat.card (A ⧸ I)
  map_mul' := ideal_cardinality_mul A
  map_one' := by
    change cardQuot (1 : Ideal A) = 1
    rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    change cardQuot (0 : Ideal A) = 0
    rw [Ideal.zero_eq_bot, cardQuot_bot]

@[simp] theorem idealCardinality_apply (I : Ideal A) :
    idealCardinality A I = Nat.card (A ⧸ I) := rfl

end
end GaloisForLFunctions.HTGeometry
