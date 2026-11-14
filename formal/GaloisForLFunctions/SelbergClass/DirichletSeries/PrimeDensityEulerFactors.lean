import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeActivitySupport
import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeDensityCoefficientField

/-!
# Exact density classification of partial Euler coefficients

For zeta, Möbius, and Liouville coefficients, every allowed prime is detected already by its
first local coefficient. Their restrictions therefore belong to a density-zero coefficient
field exactly when the allowed prime set has density zero.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry
open scoped Classical

noncomputable section

private theorem primeSupport_restriction_of_nonzero_primes
    (S : Set ℕ) (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, f p.1 ≠ 0) :
    arithmeticPrimeSupport (primeRestrict S f) = {p : Nat.Primes | p.1 ∈ S} := by
  apply Set.Subset.antisymm (arithmeticPrimeSupport_primeRestrict_subset S f)
  intro p hp
  refine ⟨p.1, ?_, dvd_rfl⟩
  have hvalue : primeRestrict S f p.1 = f p.1 := by
    simpa only [pow_one, Nat.one_ne_zero, false_or, if_pos hp] using
      primeRestrict_prime_pow S f p.2 1
  rw [hvalue]
  exact hf p

/-- The prime support of partial zeta is exactly its allowed prime set. -/
theorem arithmeticPrimeSupport_restricted_zeta (S : Set ℕ) :
    arithmeticPrimeSupport (primeRestrict S (zeta : ArithmeticFunction ℂ)) =
      {p : Nat.Primes | p.1 ∈ S} := by
  apply primeSupport_restriction_of_nonzero_primes
  intro p
  simp [p.2.ne_zero]

/-- Partial Möbius inversion detects every allowed prime. -/
theorem arithmeticPrimeSupport_restricted_moebius (S : Set ℕ) :
    arithmeticPrimeSupport (primeRestrict S (moebius : ArithmeticFunction ℂ)) =
      {p : Nat.Primes | p.1 ∈ S} := by
  apply primeSupport_restriction_of_nonzero_primes
  intro p
  simp [p.2]

/-- Partial Liouville coefficients detect every allowed prime. -/
theorem arithmeticPrimeSupport_restricted_liouville (S : Set ℕ) :
    arithmeticPrimeSupport (primeRestrict S (liouville : ArithmeticFunction ℂ)) =
      {p : Nat.Primes | p.1 ∈ S} := by
  apply primeSupport_restriction_of_nonzero_primes
  intro p
  simp [p.2]

/-- Exact sparse-coefficient criterion for every partial zeta Euler product. -/
theorem restricted_zeta_mem_densityField_iff
    (W : ℕ → Finset Nat.Primes) (S : Set ℕ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeRestrict S (zeta : ArithmeticFunction ℂ)) ∈ primeDensityCoefficientField W ↔
      PrimeWindowDensityZero W {p : Nat.Primes | p.1 ∈ S} := by
  rw [mem_primeDensityCoefficientField_iff, finitePrimeActivity_eq_arithmeticPrimeSupport,
    arithmeticPrimeSupport_restricted_zeta]

/-- The reciprocal partial zeta product has exactly the same density criterion. -/
theorem restricted_moebius_mem_densityField_iff
    (W : ℕ → Finset Nat.Primes) (S : Set ℕ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeRestrict S (moebius : ArithmeticFunction ℂ)) ∈ primeDensityCoefficientField W ↔
      PrimeWindowDensityZero W {p : Nat.Primes | p.1 ∈ S} := by
  rw [mem_primeDensityCoefficientField_iff, finitePrimeActivity_eq_arithmeticPrimeSupport,
    arithmeticPrimeSupport_restricted_moebius]

/-- Liouville's partial Euler product has exactly the same density criterion. -/
theorem restricted_liouville_mem_densityField_iff
    (W : ℕ → Finset Nat.Primes) (S : Set ℕ) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeRestrict S (liouville : ArithmeticFunction ℂ)) ∈ primeDensityCoefficientField W ↔
      PrimeWindowDensityZero W {p : Nat.Primes | p.1 ∈ S} := by
  rw [mem_primeDensityCoefficientField_iff, finitePrimeActivity_eq_arithmeticPrimeSupport,
    arithmeticPrimeSupport_restricted_liouville]

#print axioms restricted_zeta_mem_densityField_iff
#print axioms restricted_moebius_mem_densityField_iff
#print axioms restricted_liouville_mem_densityField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
