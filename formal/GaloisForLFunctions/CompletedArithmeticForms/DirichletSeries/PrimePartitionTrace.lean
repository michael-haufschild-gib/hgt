import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction
import GaloisForLFunctions.CompletedArithmeticForms.EisensteinDivisorTrace

/-!
# Prime separation of the Eisenstein divisor trace

The two unitary phases and their Eisenstein convolution admit exact complementary prime
decompositions. The coefficient identity holds for every real spectral parameter and every
prime partition, including infinite partitions.
-/

namespace GaloisForLFunctions.CompletedArithmeticForms

open SelbergClass.DirichletSeries

/-- The unitary phase separates into complementary partial Euler streams. -/
theorem phaseFunction_prime_partition (S : Set ℕ) (b : ℝ) :
    primeRestrict S (phaseFunction b) * primeRestrict Sᶜ (phaseFunction b) = phaseFunction b :=
  primeRestrict_mul_compl S _ (phaseFunction_isMultiplicative b)

/-- Restricting the Eisenstein trace restricts each of its opposite unitary phases. -/
theorem eisenstein_primeRestriction (S : Set ℕ) (b : ℝ) :
    primeRestrict S (phaseFunction b * phaseFunction (-b)) =
      primeRestrict S (phaseFunction b) * primeRestrict S (phaseFunction (-b)) :=
  primeRestrict_mul S _ _

/-- The original real Eisenstein trace is recovered by convolution of complementary pieces. -/
theorem eisensteinTrace_prime_partition (S : Set ℕ) (b : ℝ) (n : ℕ) :
    (primeRestrict S (phaseFunction b * phaseFunction (-b)) *
      primeRestrict Sᶜ (phaseFunction b * phaseFunction (-b))) n =
        (eisensteinTrace b n : ℂ) := by
  rw [primeRestrict_mul_compl S _
    ((phaseFunction_isMultiplicative b).mul (phaseFunction_isMultiplicative (-b))),
    ← eisensteinTrace_complex]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.phaseFunction_prime_partition
#print axioms GaloisForLFunctions.CompletedArithmeticForms.eisenstein_primeRestriction
#print axioms GaloisForLFunctions.CompletedArithmeticForms.eisensteinTrace_prime_partition
