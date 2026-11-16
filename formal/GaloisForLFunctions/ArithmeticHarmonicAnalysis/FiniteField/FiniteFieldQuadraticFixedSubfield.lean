import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusFixedCardinality

/-!
# Quadratic extension over a middle Frobenius fixed field

A finite field of prime-field degree `2k` has exactly `p^k` elements
fixed by the `p^k`-power Frobenius. Comparing field cardinalities proves
that the ambient field has degree two over this actual fixed subfield.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Finite E]
    [CharP E p] [Algebra (ZMod p) E]

local instance fixedSubfieldPrimeAlgebra (k : ℕ) :
    Algebra (ZMod p) (frobeniusFixedSubfield p E k) := ZMod.algebra _ p

/-- The middle Frobenius fixed field has exactly half the ambient prime-field degree. -/
theorem finiteField_middle_prime_finrank (k : ℕ)
    (hdegree : Module.finrank (ZMod p) E = 2 * k) :
    Module.finrank (ZMod p) (frobeniusFixedSubfield p E k) = k := by
  let F := frobeniusFixedSubfield p E k
  have hcF : Nat.card F = p ^ k := by
    rw [frobeniusFixedSubfield_card, hdegree, Nat.gcd_eq_right (dvd_mul_left k 2)]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := F)
  rw [Nat.card_zmod, hcF] at hc
  exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt hc).symm

/-- A finite field of degree `2k` is quadratic over its actual `p^k`-Frobenius fixed field. -/
theorem finiteField_frobeniusFixedSubfield_finrank_two (k : ℕ)
    (hdegree : Module.finrank (ZMod p) E = 2 * k) :
    Module.finrank (frobeniusFixedSubfield p E k) E = 2 := by
  let F := frobeniusFixedSubfield p E k
  have hk : 0 < k := by
    have hpos : 0 < Module.finrank (ZMod p) E := Module.finrank_pos
    omega
  have hcF : Nat.card F = p ^ k := by
    rw [frobeniusFixedSubfield_card, hdegree, Nat.gcd_eq_right (dvd_mul_left k 2)]
  have hcE : Nat.card E = p ^ (2 * k) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := E), Nat.card_zmod, hdegree]
  have hc := Module.natCard_eq_pow_finrank (K := F) (V := E)
  rw [hcE, hcF, ← pow_mul] at hc
  have he := Nat.pow_right_injective (Fact.out : p.Prime).one_lt hc
  have he' : k * 2 = k * Module.finrank F E := by
    simpa only [Nat.mul_comm 2 k] using he
  exact (Nat.eq_of_mul_eq_mul_left hk he').symm

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
