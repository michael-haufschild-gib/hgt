import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorInfiniteJetAlgebra
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

/-- The residue-interaction algebra has one polynomial generator for each surviving residue
pattern, even when its original interaction columns become dependent. -/
def primeResidueInteractionPolynomialEquiv
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (F : Filter Nat.Primes) (y : Nat.Primes → ∀ i, A i) :
    MvPolynomial (frequentPrimeColors F y) (primeFilterCoefficientField F)
      ≃ₐ[primeFilterCoefficientField F]
        Algebra.adjoin (primeFilterCoefficientField F)
          (Set.range fun z => primeColorValue y (anchoredProductBasis A z)) :=
  finiteColorBasisPolynomialEquiv F y (anchoredProductBasis A)

/-- Every natural shift and logarithmic order of every anchored interaction is jointly
independent precisely when no complete residue pattern has prime density zero. -/
theorem algebraicIndependent_primeResidueInteractionInfiniteJets_over_densityField_iff
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (primeColorNaturalShiftLogJet y (fun z x => anchoredProductBasis A z x)) ↔
      ∀ z, ¬ PrimeWindowDensityZero primeCountingWindow {p | y p = z} :=
  algebraicIndependent_primeColorBasisInfiniteJets_over_densityField_iff y (anchoredProductBasis A)

#print axioms primeResidueInteractionPolynomialEquiv
#print axioms algebraicIndependent_primeResidueInteractionInfiniteJets_over_densityField_iff

/-- The entire shifted residue-interaction algebra is polynomial on the surviving residue
patterns and the two natural indices, including when some interaction columns are dependent. -/
def primeResidueInteractionInfiniteJetPolynomialEquiv
    {ι : Type*} [Fintype ι]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, One (A i)]
    (y : Nat.Primes → ∀ i, A i) :
    MvPolynomial
        (frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) y × (ℕ × ℕ))
        (primeDensityCoefficientField primeCountingWindow)
      ≃ₐ[primeDensityCoefficientField primeCountingWindow]
        Algebra.adjoin (primeDensityCoefficientField primeCountingWindow)
          (Set.range (primeColorNaturalShiftLogJet y (fun z x => anchoredProductBasis A z x))) :=
  primeColorBasisInfiniteJetPolynomialEquiv y (anchoredProductBasis A)

#print axioms primeResidueInteractionInfiniteJetPolynomialEquiv

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
