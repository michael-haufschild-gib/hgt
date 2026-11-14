import GaloisForLFunctions.CompletedArithmeticForms.EisensteinDivisorTrace
import GaloisForLFunctions.RHTower.EisensteinHeckeCoefficient
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.DoubleRootSpecialization

/-!
# The coincident-root boundary of two Eisenstein coefficient models

At zero spectral parameter, both the real divisor trace and the Whittaker
coefficient become the divisor-count function. Their prime-power values
are the repeated-root spectral Mertens row at `α=1`. Thus the linear bound
for the prime-power divisor trace is attained at every exponent.
-/

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower ArithmeticCorrespondencePositivity

noncomputable section

/-- The real Eisenstein divisor trace at the repeated root counts divisors. -/
theorem eisensteinTrace_collision (N : ℕ) :
    eisensteinTrace 0 N = (N.divisors.card : ℝ) := by
  simpa [eisensteinTrace] using
    (Nat.sum_divisorsAntidiagonal (n := N) (fun _ _ => (1 : ℝ)))

/-- The Whittaker arithmetic coefficient has the same divisor-count specialization. -/
theorem whittakerCoeff_collision (N : ℕ) :
    whittakerCoeff 0 N = (N.divisors.card : ℂ) := by
  simp [whittakerCoeff, divisorPowerSum]

/-- The real coefficient bound is sharp at all prime powers simultaneously. -/
theorem eisensteinTrace_collision_saturates (p : Nat.Primes) (k : ℕ) :
    |eisensteinTrace 0 ((p : ℕ) ^ k)| = (k : ℝ) + 1 := by
  rw [eisensteinTrace_prime_pow_eq_cosSum 0 p.property]
  simp [cosSum]

/-- The Whittaker and spectral Mertens models have literally the same collision sequence. -/
theorem whittakerCoeff_collision_eq_spectral (p : Nat.Primes) (k : ℕ) :
    whittakerCoeff 0 ((p : ℕ) ^ k) = spectralMertensRow ![1, 1] k := by
  rw [whittakerCoeff, spectralMertensRow_double]
  simp only [mul_zero, Complex.cpow_zero, one_mul, one_pow, mul_one]
  rw [divisorPowerSum_prime_pow _ p.property]
  simp [geomSumTo]

end

end GaloisForLFunctions.CompletedArithmeticForms
