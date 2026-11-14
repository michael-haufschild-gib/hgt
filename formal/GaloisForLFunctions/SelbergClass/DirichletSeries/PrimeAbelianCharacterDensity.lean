import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorInfiniteJetAlgebra
import GaloisForLFunctions.RHTower.Deninger.DeningerFiniteCharacterBasis

/-!
# Finite abelian character prime algebras with density-zero exceptions

The finite abelian character table is a full function basis. Its prime columns, together with all
natural shifts and logarithmic orders, therefore have the exact independence criterion given by
the surviving group-element fibers. Their entire algebra is polynomial on those fibers, even
when the original character family has relations over the density coefficient field.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter Module
open scoped Classical

noncomputable section

local instance {G : Type*} [CommGroup G] [Finite G] : Finite (G →* ℂˣ) :=
  RHTower.deningerCharacterGroup_finite

local instance {G : Type*} [CommGroup G] [Finite G] : Fintype (G →* ℂˣ) :=
  Fintype.ofFinite _

variable {G : Type*} [CommGroup G] [Fintype G]

/-- The complex characters of a finite abelian group form a function basis. -/
def primeAbelianCharacterBasis : Basis (G →* ℂˣ) ℂ (G → ℂ) :=
  Basis.mk RHTower.deningerCharacter_linearIndependent (by rw [RHTower.deningerCharacter_span])

@[simp] theorem primeAbelianCharacterBasis_apply (χ : G →* ℂˣ) :
    primeAbelianCharacterBasis χ = RHTower.deningerCharacterFn χ :=
  congrFun (Basis.coe_mk _ _) χ

/-- Character prime columns are independent exactly when every group-element fiber survives. -/
theorem algebraicIndependent_primeAbelianCharacters_over_filterField_iff
    (F : Filter Nat.Primes) (color : Nat.Primes → G) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun χ : G →* ℂˣ => primeColorValue color (RHTower.deningerCharacterFn χ)) ↔
      ∀ g, ∃ᶠ p in F, color p = g := by
  simpa only [primeAbelianCharacterBasis_apply, primeColorValue] using
    algebraicIndependent_finiteColorBasis_iff F color (primeAbelianCharacterBasis (G := G))

/-- The exact density-zero exception criterion for the complete finite abelian character table. -/
theorem algebraicIndependent_primeAbelianCharacters_over_densityField_iff
    (W : ℕ → Finset Nat.Primes) (color : Nat.Primes → G) :
    AlgebraicIndependent (primeDensityCoefficientField W)
        (fun χ : G →* ℂˣ => primeColorValue color (RHTower.deningerCharacterFn χ)) ↔
      ∀ g, ¬ PrimeWindowDensityZero W {p | color p = g} := by
  simpa only [primeAbelianCharacterBasis_apply, primeColorValue] using
    algebraicIndependent_finiteColorBasis_over_densityField_iff W color
      (primeAbelianCharacterBasis (G := G))

/-- The finite abelian character prime algebra is polynomial on the surviving group elements. -/
def primeAbelianCharacterPolynomialEquiv
    (F : Filter Nat.Primes) (color : Nat.Primes → G) :
    MvPolynomial (frequentPrimeColors F color) (primeFilterCoefficientField F)
      ≃ₐ[primeFilterCoefficientField F]
        Algebra.adjoin (primeFilterCoefficientField F)
          (Set.range fun χ : G →* ℂˣ => primeColorValue color (RHTower.deningerCharacterFn χ)) := by
  have heq : Algebra.adjoin (primeFilterCoefficientField F)
      (Set.range fun χ : G →* ℂˣ => primeColorValue color (primeAbelianCharacterBasis χ)) =
      Algebra.adjoin (primeFilterCoefficientField F)
        (Set.range fun χ : G →* ℂˣ => primeColorValue color (RHTower.deningerCharacterFn χ)) := by
    simp only [primeAbelianCharacterBasis_apply]
  exact (finiteColorBasisPolynomialEquiv F color (primeAbelianCharacterBasis (G := G))).trans
    (Subalgebra.equivOfEq _ _ heq)

/-- All characters, natural shifts, and logarithmic orders are jointly independent exactly when
every group-element prime fiber survives density-zero exceptions. -/
theorem algebraicIndependent_primeAbelianCharacterInfiniteJets_over_densityField_iff
    (color : Nat.Primes → G) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (primeColorNaturalShiftLogJet color (fun χ g => RHTower.deningerCharacterFn χ g)) ↔
      ∀ g, ¬ PrimeWindowDensityZero primeCountingWindow {p | color p = g} := by
  simpa only [primeAbelianCharacterBasis_apply] using
    algebraicIndependent_primeColorBasisInfiniteJets_over_densityField_iff color
      (primeAbelianCharacterBasis (G := G))

/-- The full shifted character algebra has an unconditional polynomial presentation, including
when some group elements occur only on density-zero prime sets. -/
def primeAbelianCharacterInfiniteJetPolynomialEquiv
    (color : Nat.Primes → G) :
    MvPolynomial
        (frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) color × (ℕ × ℕ))
        (primeDensityCoefficientField primeCountingWindow)
      ≃ₐ[primeDensityCoefficientField primeCountingWindow]
        Algebra.adjoin (primeDensityCoefficientField primeCountingWindow)
          (Set.range (primeColorNaturalShiftLogJet color
            (fun χ g => RHTower.deningerCharacterFn χ g))) := by
  have heq : Algebra.adjoin (primeDensityCoefficientField primeCountingWindow)
      (Set.range (primeColorNaturalShiftLogJet color (fun χ g => primeAbelianCharacterBasis χ g))) =
      Algebra.adjoin (primeDensityCoefficientField primeCountingWindow)
        (Set.range (primeColorNaturalShiftLogJet color
          (fun χ g => RHTower.deningerCharacterFn χ g))) := by
    simp only [primeAbelianCharacterBasis_apply]
  exact (primeColorBasisInfiniteJetPolynomialEquiv color
    (primeAbelianCharacterBasis (G := G))).trans (Subalgebra.equivOfEq _ _ heq)

#print axioms algebraicIndependent_primeAbelianCharacters_over_densityField_iff
#print axioms algebraicIndependent_primeAbelianCharacterInfiniteJets_over_densityField_iff
#print axioms primeAbelianCharacterPolynomialEquiv
#print axioms primeAbelianCharacterInfiniteJetPolynomialEquiv

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
