/-
# Fundamental discriminants for the certified quadratic CRT families

This module defines the source-facing fundamental-discriminant forms attached
to the three two-adic quadratic CRT characters and proves the finite
square-free/odd arithmetic of their odd prime product.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticJacobiIdentity

noncomputable section

namespace RHTower
namespace OddPrimeFamily

/-- Standard arithmetic characterization of a fundamental discriminant. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (Squarefree D ∧ D % 4 = 1) ∨
    ∃ d : ℤ, Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) ∧ D = 4 * d

/-- The certified odd prime product is square-free. -/
theorem modulus_squarefree {I : Type*} [Fintype I] (P : OddPrimeFamily I) :
    Squarefree P.modulus := by
  rw [modulus]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp (P.pairwise_coprime hij)
  · intro i hi
    exact (Nat.prime_iff.mp (P.prime i).2.1).squarefree

/-- The certified odd prime product is odd. -/
theorem modulus_odd {I : Type*} [Fintype I] (P : OddPrimeFamily I) : Odd P.modulus := by
  rw [modulus]
  exact Finset.prod_induction (fun i : I => (P.prime i).1) (fun n : ℕ => Odd n)
    (fun a b ha hb => ha.mul hb)
    (by norm_num)
    (fun i hi => (P.prime i).2.1.odd_of_ne_two (P.prime i).2.2)

/-- Fundamental discriminant represented by the conductor-four CRT character. -/
def fourOddFundamentalDiscriminant {I : Type*} [Fintype I] (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then -4 * (P.modulus : ℤ) else 4 * (P.modulus : ℤ)

/-- Fundamental discriminant represented by the first conductor-eight CRT character. -/
def eightOddFundamentalDiscriminant {I : Type*} [Fintype I] (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then 8 * (P.modulus : ℤ) else -8 * (P.modulus : ℤ)

/-- Fundamental discriminant represented by the second conductor-eight CRT character. -/
def eightOddPrimeFundamentalDiscriminant {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then -8 * (P.modulus : ℤ) else 8 * (P.modulus : ℤ)

/-- The Kronecker symbol for an even discriminant, on positive integer denominators.
For a discriminant divisible by four, even denominators have value zero and
odd denominators use Mathlib's Jacobi symbol. -/
def evenKroneckerSymbol (D : ℤ) (n : ℕ) : ℤ :=
  if Even n then 0 else jacobiSym D n

end OddPrimeFamily
end RHTower
