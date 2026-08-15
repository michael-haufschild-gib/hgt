import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialMonomial

/-!
# Additive--exponential auxiliary monomials for Baker's theorem

The full Baker auxiliary polynomial needs an additive coordinate in addition to the exponential
coordinates.  This module introduces the corresponding monomial basis and proves the exact action
of every solved component derivation.  Nonconstant directions stay diagonal; the distinguished
constant direction has one lowering term in the additive degree.  That lowering term is the source
of the polynomial weights in the terminal exponential polynomial and is essential for the
parameter separation in the long extrapolation argument.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- A bounded additive degree together with bounded exponential degrees. -/
abbrev SolvedRelation.AuxiliaryColumn (R : SolvedRelation) (U V : ℕ) :=
  Fin U × R.ExponentialColumn V

/-- A monomial in the additive coordinate and all exponential coordinates. -/
noncomputable def SolvedRelation.additiveExponentialMonomial
    (R : SolvedRelation) {U V : ℕ} (col : R.AuxiliaryColumn U V) :
    MvPolynomial R.Variable R.CoefficientField :=
  MvPolynomial.X none ^ (col.1 : ℕ) * R.exponentialMonomial col.2

/-- A nonconstant component acts diagonally on an additive--exponential monomial. -/
theorem SolvedRelation.componentDerivation_additiveExponentialMonomial_some
    (R : SolvedRelation) (c : ℤ) (j : R.NonPivot) {U V : ℕ}
    (col : R.AuxiliaryColumn U V) :
    R.componentDerivation c (some j) (R.additiveExponentialMonomial col) =
      MvPolynomial.C (R.componentEigenvalue c (some j) col.2) *
        R.additiveExponentialMonomial col := by
  unfold SolvedRelation.additiveExponentialMonomial
  rw [Derivation.leibniz, R.componentDerivation_exponentialMonomial]
  have hX : R.componentDerivation c (some j) (MvPolynomial.X none) = 0 := by
    rw [R.componentDerivation_X]
    simp [SolvedRelation.componentVector]
  rw [(R.componentDerivation c (some j)).leibniz_pow, hX]
  simp only [nsmul_eq_mul, smul_eq_mul, mul_zero]
  ring

/-- The constant component has an additive-degree lowering term and a diagonal eigen term. -/
theorem SolvedRelation.componentDerivation_additiveExponentialMonomial_none
    (R : SolvedRelation) (c : ℤ) {U V : ℕ}
    (col : R.AuxiliaryColumn U V) :
    R.componentDerivation c none (R.additiveExponentialMonomial col) =
      MvPolynomial.C ((col.1 : R.CoefficientField) * R.integerScalar c) *
          (MvPolynomial.X none ^ ((col.1 : ℕ) - 1) * R.exponentialMonomial col.2) +
        MvPolynomial.C (R.componentEigenvalue c none col.2) *
          R.additiveExponentialMonomial col := by
  unfold SolvedRelation.additiveExponentialMonomial
  rw [Derivation.leibniz, R.componentDerivation_exponentialMonomial]
  rw [(R.componentDerivation c none).leibniz_pow]
  rw [R.componentDerivation_X]
  simp only [SolvedRelation.componentVector, nsmul_eq_mul, smul_eq_mul,
    MvPolynomial.C_mul]
  have hcast : ((col.1 : ℕ) : MvPolynomial R.Variable R.CoefficientField) =
      MvPolynomial.C ((col.1 : ℕ) : R.CoefficientField) := by
    exact (map_natCast (MvPolynomial.C : R.CoefficientField →+*
      MvPolynomial R.Variable R.CoefficientField) (col.1 : ℕ)).symm
  rw [hcast]
  ring

end GaloisForLFunctions.RHTower.BakerGeneralProof
