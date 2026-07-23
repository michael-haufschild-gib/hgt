import GaloisForLFunctions.HTGeometry.FamilyCrossResonance
import GaloisForLFunctions.RHTower.DiagonalCharacter

/-!
# Family prime-balance diagonal-scale universality

A finite signed prime-exponent family carries one aggregate balance vector.  This file identifies
three exact manifestations of its neutrality:

* positive and negative prime products agree;
* every prime coordinate balances and every complex diagonal Dirichlet monomial agrees;
* every shared scale disappears from every commutative-group twisted family product.

The result joins unique factorization, the prime-torus diagonal/Dirichlet identity, and the
family twisted-product split.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- Dirichlet monomial attached to a natural prime-exponent vector, written in its prime-torus
diagonal form. -/
def diagonalPrimeMonomial (a : Nat.Primes →₀ ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ a.support, (((p : ℕ) : ℂ) ^ z) ^ (a p)

/-- The diagonal prime monomial is the complex power of its encoded integer. -/
theorem diagonalPrimeMonomial_eq (a : Nat.Primes →₀ ℕ) (z : ℂ) :
    diagonalPrimeMonomial a z = (((primeProduct a : ℕ) : ℂ) ^ z) := by
  exact (diagonal_character_eq_dirichlet a z).symm

/-- Equality of prime products is faithfully detected by the complete complex diagonal family.
The reverse implication already follows from the single exponent `z = 1`. -/
theorem primeProduct_eq_iff_diagonalPrimeMonomial_eq
    (a b : Nat.Primes →₀ ℕ) :
    primeProduct a = primeProduct b ↔
      ∀ z : ℂ, diagonalPrimeMonomial a z = diagonalPrimeMonomial b z := by
  constructor
  · intro h z
    rw [diagonalPrimeMonomial_eq, diagonalPrimeMonomial_eq, h]
  · intro h
    have h1 := h 1
    rw [diagonalPrimeMonomial_eq, diagonalPrimeMonomial_eq] at h1
    simpa using h1

/-- **Family prime-balance diagonal-scale universality law.**  For an arbitrary finite family of
signed prime exponent vectors, equality of the aggregate positive and negative prime products is
equivalent to a simultaneous package:

* the aggregate vector vanishes;
* every prime-coordinate family sum vanishes;
* positive and negative diagonal Dirichlet monomials agree at every complex exponent;
* for every shared scale in every chosen commutative group, the twisted family product retains
  only its family-dependent twist factor.

Thus one integer unique-factorization equality removes a shared scale universally, not merely on
the complex prime diagonal. -/
theorem familyPrimeBalance_diagonalScaleUniversality
    {ι G : Type*} [Fintype ι] [CommGroup G]
    (m : ι → Nat.Primes →₀ ℤ) (twist : ι → Nat.Primes → G) :
    primeProduct (positivePart (familyPrimeBalance m)) =
        primeProduct (negativePart (familyPrimeBalance m)) ↔
      familyPrimeBalance m = 0 ∧
        (∀ p : Nat.Primes, ∑ i, m i p = 0) ∧
        (∀ z : ℂ,
          diagonalPrimeMonomial (positivePart (familyPrimeBalance m)) z =
            diagonalPrimeMonomial (negativePart (familyPrimeBalance m)) z) ∧
        (∀ scale : Nat.Primes → G,
          familyTwistedProduct twist scale m =
            ∏ i, bohrCharacter (m i) (twist i)) := by
  classical
  constructor
  · intro hprime
    have hbalance := familyPrimeBalance_eq_zero_of_primeProduct_eq m hprime
    refine ⟨hbalance, ?_, ?_, ?_⟩
    · intro p
      exact familyPrimeBalance_apply_eq_zero_of_primeProduct_eq m hprime p
    · exact
        (primeProduct_eq_iff_diagonalPrimeMonomial_eq
          (positivePart (familyPrimeBalance m))
          (negativePart (familyPrimeBalance m))).1 hprime
    · intro scale
      have hexponent : familyExponentSum m = 0 := by
        simpa [familyPrimeBalance] using hbalance
      rw [familyTwistedProduct_split, hexponent, bohrCharacter_zero, mul_one]
  · rintro ⟨hbalance, -, -, -⟩
    rw [hbalance]
    rfl

end

end GaloisForLFunctions
