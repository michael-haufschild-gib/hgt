import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.SymmetricPolynomialJets

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Polynomial differentiation as a complex-linear endomorphism. -/
def polynomialDerivativeEnd : Module.End ℂ (Polynomial ℂ) where
  toFun := Polynomial.derivative
  map_add' P Q := by exact Polynomial.derivative_add
  map_smul' c P := by simp

/-- Functional-equation reflection as a complex-linear endomorphism of polynomials. -/
def reflectPolyEnd : Module.End ℂ (Polynomial ℂ) where
  toFun := reflectPoly
  map_add' := reflectPoly_add
  map_smul' := reflectPoly_smul

/-- Differentiation and functional-equation reflection form a split supertranslation sector. -/
def polynomialReflectionD1N2Split :
    SuperPoincare.D1N2Split (Module.End ℂ (Polynomial ℂ)) :=
  SuperPoincare.D1N2Split.ofEqNeg
    polynomialDerivativeEnd reflectPolyEnd (by
      apply LinearMap.ext
      intro P
      exact derivative_reflectPoly P)

/-- Differentiation momentum is the second derivative. -/
theorem polynomialReflection_momentum0_apply (P : Polynomial ℂ) :
    polynomialReflectionD1N2Split.momentum0 P =
      P.derivative.derivative := rfl

/-- Functional-equation reflection generates identity momentum. -/
theorem polynomialReflection_momentum1_eq_one :
    polynomialReflectionD1N2Split.momentum1 = 1 := by
  apply LinearMap.ext
  exact reflectPoly_reflectPoly

end GaloisForLFunctions.HTGeometry
