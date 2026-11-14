import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorBasis
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationInteractionSuperselection

/-!
# Sparse-prime independence of anchored residue interactions

The complete anchored interaction table is a basis of functions on the finite residue product.
Its prime columns are therefore algebraically independent over an exceptional-prime coefficient
field exactly when every residue pattern survives. For density-zero exceptions this means that
none of the residue-pattern fibers has density zero.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Exact exceptional-prime criterion for the existing anchored residue-interaction family. -/
theorem algebraicIndependent_primeResidueInteractions_over_filterField_iff
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (F : Filter Nat.Primes) (y : Nat.Primes → ∀ i, A i) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (primeResidueInteractionCoefficient A y z))) ↔
      ∀ z, ∃ᶠ p in F, y p = z :=
  algebraicIndependent_finiteColorBasis_iff F y (anchoredProductBasis A)

/-- The residue-interaction family survives density-zero coefficient exceptions exactly when
every complete residue pattern has a non-negligible prime fiber. -/
theorem algebraicIndependent_primeResidueInteractions_over_densityField_iff
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (W : ℕ → Finset Nat.Primes) (y : Nat.Primes → ∀ i, A i) :
    AlgebraicIndependent (primeDensityCoefficientField W)
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (primeResidueInteractionCoefficient A y z))) ↔
      ∀ z, ¬ PrimeWindowDensityZero W {p | y p = z} :=
  algebraicIndependent_finiteColorBasis_over_densityField_iff W y (anchoredProductBasis A)

/-- Infinite prime fibers are the exact boundary for the cofinite exceptional-prime filter. -/
theorem algebraicIndependent_primeResidueInteractions_over_cofiniteField_iff
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    AlgebraicIndependent (primeFilterCoefficientField cofinite)
        (fun z => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticOfPrimeColumn (primeResidueInteractionCoefficient A y z))) ↔
      ∀ z, {p | y p = z}.Infinite := by
  rw [algebraicIndependent_primeResidueInteractions_over_filterField_iff]
  constructor
  · intro h z
    exact (mem_frequentPrimeColors_cofinite_iff y z).mp (h z)
  · intro h z
    exact (mem_frequentPrimeColors_cofinite_iff y z).mpr (h z)

#print axioms algebraicIndependent_primeResidueInteractions_over_filterField_iff
#print axioms algebraicIndependent_primeResidueInteractions_over_densityField_iff

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
