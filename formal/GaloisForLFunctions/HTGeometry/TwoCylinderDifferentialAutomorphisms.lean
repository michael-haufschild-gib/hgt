import GaloisForLFunctions.HTGeometry.TwoCylinderDilationEquivariance
import GaloisForLFunctions.HTGeometry.TwoCylinderTranslationAction
import GaloisForLFunctions.HTGeometry.DilatedCharacterOrbitObstruction

/-!
# The coefficient dilation is differential too

The companion of `twoCylDerivation_ratFuncScale`: the dilation of the coefficient field commutes
with the total two-cylinder derivation.  Its coefficient part is the one-cylinder statement that
the Euler operator commutes with dilations; its variable part is untouched, since the coefficient
map fixes the outer coordinate and the logarithmic derivative of that coordinate is a constant.

Both dilations are therefore differential automorphisms of the two-cylinder field, which is what
the source-boundary matroid law asks of the translation action.
-/

open Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The one-cylinder statement -/

theorem cylDeriv_ratFuncScale {K : Type*} [Field K] (lam : K) {q : K} (hq : q ≠ 0)
    (y : RatFunc K) :
    cylDeriv lam (ratFuncScale q hq y) = ratFuncScale q hq (cylDeriv lam y) := by
  rw [cylDeriv, cylDeriv, ratFuncEulerOp_ratFuncScale, map_mul, ratFuncScale_algebraMap_base]

/-! ### The coefficient dilation of the two-cylinder field -/

section

variable [Differential (RatFunc ℂ)]

local instance tdaIntAlgebraPoly : Algebra ℤ (Polynomial (RatFunc ℂ)) := Ring.toIntAlgebra _
local instance tdaIntAlgebraRatFunc : Algebra ℤ (RatFunc (RatFunc ℂ)) := Ring.toIntAlgebra _

local instance tdaIntTower :
    IsScalarTower ℤ (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun n => by
    show ((n : ℤ) : RatFunc (RatFunc ℂ))
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) ((n : ℤ) : Polynomial (RatFunc ℂ))
    rw [map_intCast]

theorem coeffDeriv_polyCoeffScale {q : ℂ} (hq : q ≠ 0)
    (hcomm : ∀ c : RatFunc ℂ, (ratFuncScale q hq c)′ = ratFuncScale q hq (c′))
    (p : Polynomial (RatFunc ℂ)) :
    coeffDeriv (polyCoeffScale hq p) = polyCoeffScale hq (coeffDeriv p) := by
  refine Polynomial.ext fun n => ?_
  have hL : (coeffDeriv (polyCoeffScale hq p)).coeff n
      = (ratFuncScale q hq (p.coeff n))′ := by
    rw [coeffDeriv_coeff, polyCoeffScale, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
    rfl
  have hR : (polyCoeffScale hq (coeffDeriv p)).coeff n
      = ratFuncScale q hq ((p.coeff n)′) := by
    rw [polyCoeffScale, Polynomial.coe_mapRingHom, Polynomial.coeff_map, coeffDeriv_coeff]
    rfl
  rw [hL, hR, hcomm]

omit [Differential (RatFunc ℂ)] in
theorem cylinderCoeffScale_algebraMap {q : ℂ} (hq : q ≠ 0) (p : Polynomial (RatFunc ℂ)) :
    cylinderCoeffScale hq (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (polyCoeffScale hq p) := by
  have h := cylinderCoeffScale_div hq p 1
  rw [map_one] at h
  set A : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p with hA
  set B : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (polyCoeffScale hq p) with hB
  have h1 : A / 1 = A := div_one A
  have h2 : B / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (polyCoeffScale hq 1) = B := by
    rw [map_one, map_one]
    exact div_one B
  rw [h1, h2] at h
  exact h

/-- **The coefficient dilation commutes with the total two-cylinder derivation.** -/
theorem twoCylDerivation_cylinderCoeffScale (lam : RatFunc ℂ) {q : ℂ} (hq : q ≠ 0)
    (hcomm : ∀ c : RatFunc ℂ, (ratFuncScale q hq c)′ = ratFuncScale q hq (c′))
    (hlam : ratFuncScale q hq lam = lam) (y : RatFunc (RatFunc ℂ)) :
    twoCylDerivation lam (cylinderCoeffScale hq y)
      = cylinderCoeffScale hq (twoCylDerivation lam y) := by
  classical
  have hD : ∀ x y : RatFunc (RatFunc ℂ),
      twoCylDerivation lam (x * y)
        = x * twoCylDerivation lam y + y * twoCylDerivation lam x := by
    intro x y
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hlamAlg : cylinderCoeffScale hq
        (algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) lam)
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) lam := by
    rw [algebraMap_ratFunc_eq_polynomialC, cylinderCoeffScale_algebraMap, polyCoeffScale,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    exact congrArg (fun z => algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (Polynomial.C z)) hlam
  have hpoly : ∀ p : Polynomial (RatFunc ℂ),
      twoCylDerivation lam (cylinderCoeffScale hq
          (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p))
        = cylinderCoeffScale hq (twoCylDerivation lam
          (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)) := by
    intro p
    rw [cylinderCoeffScale_algebraMap, twoCylDerivation_algebraMap, twoCylDerivation_algebraMap,
      coeffDeriv_polyCoeffScale hq hcomm, map_add, map_mul, map_mul,
      cylinderCoeffScale_algebraMap, cylinderCoeffScale_algebraMap, hlamAlg,
      polyCoeffScale, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.derivative_map]
    rw [cylinderCoeffScale_algebraMap, polyCoeffScale, Polynomial.coe_mapRingHom]
  refine RatFunc.induction_on
    (P := fun y => twoCylDerivation lam (cylinderCoeffScale hq y)
      = cylinderCoeffScale hq (twoCylDerivation lam y)) y ?_
  intro p t ht
  set A : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p with hA
  set B : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) t with hB
  have hBne : B ≠ 0 := RatFunc.algebraMap_ne_zero ht
  have hSB : cylinderCoeffScale hq B ≠ 0 := by
    rw [hB, cylinderCoeffScale_algebraMap]
    refine RatFunc.algebraMap_ne_zero ?_
    intro hcon
    exact ht (polyCoeffScale_injective hq (by rw [hcon, map_zero]))
  have hdiv : cylinderCoeffScale hq (A / B)
      = cylinderCoeffScale hq A / cylinderCoeffScale hq B :=
    map_div₀ (cylinderCoeffScale hq) A B
  have hpA := hpoly p
  have hpB := hpoly t
  rw [← hA] at hpA
  rw [← hB] at hpB
  have hpush : cylinderCoeffScale hq
        ((twoCylDerivation lam A * B - A * twoCylDerivation lam B) / B ^ 2)
      = (cylinderCoeffScale hq (twoCylDerivation lam A) * cylinderCoeffScale hq B
          - cylinderCoeffScale hq A * cylinderCoeffScale hq (twoCylDerivation lam B))
        / (cylinderCoeffScale hq B) ^ 2 := by
    have hd2 := map_div₀ (cylinderCoeffScale hq)
      (twoCylDerivation lam A * B - A * twoCylDerivation lam B) (B ^ 2)
    rw [hd2, map_sub, map_mul, map_mul, map_pow]
  rw [hdiv, leibniz_div (twoCylDerivation lam) hD hSB,
    leibniz_div (twoCylDerivation lam) hD hBne, hpA, hpB, hpush]

end

end

end GaloisForLFunctions.HTGeometry
