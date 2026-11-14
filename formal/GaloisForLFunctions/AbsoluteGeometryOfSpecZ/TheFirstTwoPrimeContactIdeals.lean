import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes

/-!
# The first prime contacts and their multiplicities

The graph pairs `(1,2)` and `(1,3)` have ideals `(2)` and `(3)`.
Ramification raises the ideals of `(2,4)` and `(3,9)` to `(4)` and `(9)`.
The graphs of degrees two and three are disjoint.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The diagonal meets the first two prime Frobenius graphs with multiplicity one. -/
theorem graphIdeal_first_two_primes :
    graphIdeal 1 2 = Ideal.span ({2} : Set ℤ) ∧
    graphIdeal 1 3 = Ideal.span ({3} : Set ℤ) := by
  constructor
  · simpa using graphIdeal_one_prime_pow (p := 2) Nat.prime_two (k := 1) (by norm_num)
  · simpa using graphIdeal_one_prime_pow (p := 3) Nat.prime_three (k := 1) (by norm_num)

/-- The first ramified contacts retain their doubled local intersection order. -/
theorem graphIdeal_first_prime_squares :
    graphIdeal 2 4 = Ideal.span ({4} : Set ℤ) ∧
    graphIdeal 3 9 = Ideal.span ({9} : Set ℤ) := by
  constructor
  · have h := graphIdeal_mul_prime_pow 2 (p := 2) Nat.prime_two (j := 1) (by norm_num)
    norm_num [Nat.prime_two.factorization] at h ⊢
    exact h
  · have h := graphIdeal_mul_prime_pow 3 (p := 3) Nat.prime_three (j := 1) (by norm_num)
    norm_num [Nat.prime_three.factorization] at h ⊢
    exact h

/-- Different first prime graphs have no contact. -/
theorem graphIdeal_two_three : graphIdeal 2 3 = ⊤ := by
  apply graphIdeal_eq_top_of_two_primes (p := 2) (q := 3) Nat.prime_two Nat.prime_three
    (by norm_num)
  · norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  · norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]

#print axioms graphIdeal_first_two_primes
#print axioms graphIdeal_first_prime_squares
#print axioms graphIdeal_two_three

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
