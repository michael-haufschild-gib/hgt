import GaloisForLFunctions.HTGeometry.TwoCylinderDifferentialAutomorphisms

/-!
# The dilations fix the complex constants

Both translation actions on the two-cylinder function field fix the embedded complex constants: the
outer dilation because constants of the coefficient field are fixed by every dilation of the
variable, the coefficient dilation because it acts on the coefficient field by a dilation, which
fixes the constants of that field in turn.

With the derivation-commutation of the previous module this makes each of them a differential
`ℂ`-algebra automorphism of the base, the shape the source-boundary matroid law consumes.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem cylinderCoeffScale_algebraMap_base {q : ℂ} (hq : q ≠ 0) (x : RatFunc ℂ) :
    cylinderCoeffScale hq (algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) x)
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (ratFuncScale q hq x) := by
  rw [algebraMap_ratFunc_eq_polynomialC, cylinderCoeffScale_algebraMap, polyCoeffScale,
    Polynomial.coe_mapRingHom, Polynomial.map_C, ← algebraMap_ratFunc_eq_polynomialC]
  rfl

/-- **The coefficient dilation fixes the complex constants.** -/
theorem cylinderCoeffScale_algebraMap_complex {q : ℂ} (hq : q ≠ 0) (c : ℂ) :
    cylinderCoeffScale hq (algebraMap ℂ (RatFunc (RatFunc ℂ)) c)
      = algebraMap ℂ (RatFunc (RatFunc ℂ)) c := by
  have htower : algebraMap ℂ (RatFunc (RatFunc ℂ)) c
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) c) :=
    IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c
  rw [htower, cylinderCoeffScale_algebraMap_base, ratFuncScale_algebraMap_base]

/-- **The outer dilation fixes the complex constants.** -/
theorem ratFuncScale_algebraMap_complex {s : RatFunc ℂ} (hs : s ≠ 0) (c : ℂ) :
    ratFuncScale s hs (algebraMap ℂ (RatFunc (RatFunc ℂ)) c)
      = algebraMap ℂ (RatFunc (RatFunc ℂ)) c := by
  have htower : algebraMap ℂ (RatFunc (RatFunc ℂ)) c
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) c) :=
    IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c
  rw [htower, ratFuncScale_algebraMap_base]

/-- **The complex constants are differential constants of the two-cylinder derivation.** -/
theorem twoCylDerivation_algebraMap_complex [Differential (RatFunc ℂ)]
    (hC : ∀ c : ℂ, (algebraMap ℂ (RatFunc ℂ) c)′ = 0) (lam : RatFunc ℂ) (c : ℂ) :
    twoCylDerivation lam (algebraMap ℂ (RatFunc (RatFunc ℂ)) c) = 0 := by
  have htower : algebraMap ℂ (RatFunc (RatFunc ℂ)) c
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) c) :=
    IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c
  rw [htower, algebraMap_ratFunc_eq_polynomialC, twoCylDerivation_algebraMap]
  have hcoeff : coeffDeriv (Polynomial.C (algebraMap ℂ (RatFunc ℂ) c)) = 0 := by
    rw [← Polynomial.monomial_zero_left, coeffDeriv_monomial, hC c]
    simp
  rw [hcoeff, Polynomial.derivative_C]
  simp

end

end GaloisForLFunctions.HTGeometry
