import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInfinityValuation
import GaloisForLFunctions.HTGeometry.ABHN.ValuationCoordinateTransport

/-!
# Uniform equivalence between infinity and the `X`-adic coordinate

The change of variable `t ↦ t⁻¹` sends the uniform topology at infinity on `F(t)` to the
`X`-adic uniform topology.  This is the direct topological input for comparing their
completions.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped RatFunc

universe u

noncomputable section

/-- Coordinate inversion is a uniform equivalence from the pulled-back `X`-adic topology to the
`X`-adic topology. -/
def rationalFunctionInversionComapPolynomialValuation_uniformEquiv
    (F : Type u) [Field F] :
    WithVal (rationalFunctionInversionComapPolynomialValuation F) ≃ᵤ
      WithVal (RatFunc.polynomialValuationX F) :=
  uniformEquiv_congr_of_valuation_eq
    (rationalFunctionInversionComapPolynomialValuation F)
    (RatFunc.polynomialValuationX F)
    (rationalFunctionInversionAlgEquiv F).toRingEquiv (by
      intro x
      rfl)

/-- The infinity topology on `F(t)` is uniformly equivalent to its `X`-adic topology after
inverting the rational-function coordinate. -/
def rationalFunctionInftyValuation_uniformEquiv_polynomialValuationX
    (F : Type u) [Field F] [DecidableEq (RatFunc F)] :
    WithVal (RatFunc.inftyValuation F) ≃ᵤ WithVal (RatFunc.polynomialValuationX F) :=
  (rationalFunctionInftyValuation_isEquiv_inversionComapPolynomialValuation F).uniformEquiv.trans
    (rationalFunctionInversionComapPolynomialValuation_uniformEquiv F)

end

end GaloisForLFunctions.HTGeometry.ABHN
