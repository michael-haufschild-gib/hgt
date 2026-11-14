import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorInfiniteJetAlgebra
import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint

/-!
# Walsh prime algebras with sparse exceptions

Fourier–Walsh inversion makes the complete Boolean character table a function basis. Its prime
series generate a polynomial algebra on the Boolean patterns that survive the prime filter.
The complete character family is algebraically independent exactly when every pattern survives.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter Module
open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I]

/-- Walsh inversion proves that the character table spans every function on the Boolean cube. -/
theorem span_orientationWalshCharacter :
    Submodule.span ℂ (Set.range (orientationWalshCharacter (I := I))) = ⊤ := by
  apply top_unique
  intro f _
  have hf : f = ∑ B : Finset I, inverseWalshCoefficient f B • orientationWalshCharacter B := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      (orientationWalsh_inversion f x).symm
  rw [hf]
  apply Submodule.sum_mem
  intro B _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, rfl⟩)

/-- The square Walsh character table is linearly independent, since inversion gives full span. -/
theorem linearIndependent_orientationWalshCharacter :
    LinearIndependent ℂ (orientationWalshCharacter (I := I)) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Finset I) =
    Module.finrank ℂ (Submodule.span ℂ (Set.range (orientationWalshCharacter (I := I))))
  rw [span_orientationWalshCharacter]
  simp only [finrank_top, Module.finrank_pi, Fintype.card_finset, Fintype.card_fun,
    Fintype.card_bool]

/-- The finite Walsh character basis of all complex-valued Boolean observations. -/
def primeOrientationWalshBasis : Basis (Finset I) ℂ ((I → Bool) → ℂ) :=
  Basis.mk linearIndependent_orientationWalshCharacter (by rw [span_orientationWalshCharacter])

@[simp] theorem primeOrientationWalshBasis_apply (B : Finset I) :
    primeOrientationWalshBasis B = orientationWalshCharacter B :=
  congrFun (Basis.coe_mk _ _) B

/-- Every Boolean pattern must survive, and this condition suffices for all Walsh prime columns. -/
theorem algebraicIndependent_primeWalsh_over_filterField_iff
    (F : Filter Nat.Primes) (color : Nat.Primes → I → Bool) :
    AlgebraicIndependent (primeFilterCoefficientField F)
        (fun B : Finset I => primeColorValue color (orientationWalshCharacter B)) ↔
      ∀ x, ∃ᶠ p in F, color p = x := by
  simpa only [primeOrientationWalshBasis_apply, primeColorValue] using
    algebraicIndependent_finiteColorBasis_iff F color (primeOrientationWalshBasis (I := I))

/-- Density-zero exceptions remove a Walsh degree of freedom exactly when a Boolean pattern
fiber has density zero. -/
theorem algebraicIndependent_primeWalsh_over_densityField_iff
    (W : ℕ → Finset Nat.Primes) (color : Nat.Primes → I → Bool) :
    AlgebraicIndependent (primeDensityCoefficientField W)
        (fun B : Finset I => primeColorValue color (orientationWalshCharacter B)) ↔
      ∀ x, ¬ PrimeWindowDensityZero W {p | color p = x} := by
  simpa only [primeOrientationWalshBasis_apply, primeColorValue] using
    algebraicIndependent_finiteColorBasis_over_densityField_iff W color
      (primeOrientationWalshBasis (I := I))

/-- Even when Walsh columns are dependent, their entire algebra is polynomial, with one variable
for each surviving Boolean pattern. -/
def primeWalshPolynomialEquiv
    (F : Filter Nat.Primes) (color : Nat.Primes → I → Bool) :
    MvPolynomial (frequentPrimeColors F color) (primeFilterCoefficientField F)
      ≃ₐ[primeFilterCoefficientField F]
        Algebra.adjoin (primeFilterCoefficientField F)
          (Set.range fun B : Finset I => primeColorValue color (orientationWalshCharacter B)) := by
  simpa only [primeOrientationWalshBasis_apply] using
    finiteColorBasisPolynomialEquiv F color (primeOrientationWalshBasis (I := I))

#print axioms algebraicIndependent_primeWalsh_over_densityField_iff
#print axioms primeWalshPolynomialEquiv

/-- The full Walsh palette, all natural shifts, and all logarithmic orders are jointly
independent exactly when every Boolean pattern survives density-zero prime exceptions. -/
theorem algebraicIndependent_primeWalshInfiniteJets_over_densityField_iff
    (color : Nat.Primes → I → Bool) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
        (primeColorNaturalShiftLogJet color (fun B x => orientationWalshCharacter B x)) ↔
      ∀ x, ¬ PrimeWindowDensityZero primeCountingWindow {p | color p = x} := by
  simpa only [primeOrientationWalshBasis_apply] using
    algebraicIndependent_primeColorBasisInfiniteJets_over_densityField_iff color
      (primeOrientationWalshBasis (I := I))

#print axioms algebraicIndependent_primeWalshInfiniteJets_over_densityField_iff

/-- All shifted Walsh observations form a polynomial algebra on surviving Boolean patterns,
natural shifts, and logarithmic orders, without requiring every Boolean pattern to survive. -/
def primeWalshInfiniteJetPolynomialEquiv
    (color : Nat.Primes → I → Bool) :
    MvPolynomial
        (frequentPrimeColors (primeWindowDensityFilter primeCountingWindow) color × (ℕ × ℕ))
        (primeDensityCoefficientField primeCountingWindow)
      ≃ₐ[primeDensityCoefficientField primeCountingWindow]
        Algebra.adjoin (primeDensityCoefficientField primeCountingWindow)
          (Set.range (primeColorNaturalShiftLogJet color (fun B x => orientationWalshCharacter B x))) := by
  simpa only [primeOrientationWalshBasis_apply] using
    primeColorBasisInfiniteJetPolynomialEquiv color (primeOrientationWalshBasis (I := I))

#print axioms primeWalshInfiniteJetPolynomialEquiv

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
