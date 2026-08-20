import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# The total derivation of a rational function field

The parameterised Galois theory of a difference equation runs over a base whose constants carry a
nontrivial derivation, so the derivation of `K(X)` has to move the coefficients as well as the
coordinate:

```text
D(f) = (coefficientwise derivation of K)(f) + (d/dX) f.
```

It is built by extending the corresponding polynomial derivation across the fraction field, reusing
the coefficientwise derivation the corpus already owns, and it makes `K(X)` a differential field in
which `K` keeps its own derivation and the coordinate has derivative one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Differential

variable {K : Type*} [Field K] [CharZero K] [Differential K]

/-- **The total derivation on polynomials**: the formal derivative in the coordinate plus the
ambient derivation on the coefficients. -/
def polyTotalDeriv : Derivation ℚ K[X] K[X] :=
  Derivation.mk'
    ((Polynomial.derivative (R := K)).restrictScalars ℚ + (coeffDerivHom K).toRatLinearMap)
    (by
      intro p q
      simp only [LinearMap.add_apply, LinearMap.coe_restrictScalars,
        AddMonoidHom.coe_toRatLinearMap, coeffDerivHom_apply,
        Polynomial.derivative_mul, coeffDeriv_mul, smul_eq_mul]
      ring)

@[simp] theorem polyTotalDeriv_apply (p : K[X]) :
    polyTotalDeriv p = Polynomial.derivative p + coeffDeriv p := rfl

theorem polyTotalDeriv_X : polyTotalDeriv (X : K[X]) = 1 := by
  rw [polyTotalDeriv_apply, Polynomial.derivative_X]
  have hX : (X : K[X]) = Polynomial.monomial 1 (1 : K) := (Polynomial.monomial_one_one_eq_X).symm
  rw [hX, coeffDeriv_monomial 1 (1 : K)]
  simp

theorem polyTotalDeriv_C (a : K) :
    polyTotalDeriv (Polynomial.C a) = Polynomial.C (a′) := by
  rw [polyTotalDeriv_apply, Polynomial.derivative_C]
  have hC : (Polynomial.C a : K[X]) = Polynomial.monomial 0 a := by
    rw [Polynomial.monomial_zero_left]
  rw [hC, coeffDeriv_monomial 0 a]
  simp

/-- The total derivation on polynomials, valued in the rational function field. -/
def polyToRatDeriv : Derivation ℚ K[X] (RatFunc K) :=
  (Algebra.linearMap K[X] (RatFunc K)).compDer polyTotalDeriv

theorem polyToRatDeriv_apply (p : K[X]) :
    polyToRatDeriv p = algebraMap K[X] (RatFunc K) (polyTotalDeriv p) := rfl

/-- **The total derivation of `K(X)`**: the coefficient field keeps its own derivation and the
coordinate has derivative one. -/
def coordinateTotalDerivation : Derivation ℚ (RatFunc K) (RatFunc K) :=
  GaloisForLFunctions.fractionRingDerivation polyToRatDeriv

theorem coordinateTotalDerivation_algebraMap (p : K[X]) :
    coordinateTotalDerivation (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (polyTotalDeriv p) := by
  rw [coordinateTotalDerivation, GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- The total differential structure on the rational function field. -/
@[reducible] def coordinateTotalDifferential : Differential (RatFunc K) where
  deriv :=
    letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
    Derivation.restrictScalars ℤ coordinateTotalDerivation

@[simp] theorem coordinateTotalDifferential_deriv (y : RatFunc K) :
    letI := coordinateTotalDifferential (K := K)
    Differential.deriv y = coordinateTotalDerivation y := rfl

/-- The total derivation extends the derivation of the coefficient field. -/
@[simp] theorem coordinateTotalDerivation_base (c : K) :
    coordinateTotalDerivation (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) (c′) := by
  have hC : algebraMap K (RatFunc K) c = algebraMap K[X] (RatFunc K) (Polynomial.C c) := by
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have hCd : algebraMap K (RatFunc K) (c′) = algebraMap K[X] (RatFunc K) (Polynomial.C (c′)) := by
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [hC, hCd, coordinateTotalDerivation_algebraMap, polyTotalDeriv_C]

/-- The total derivation sends the coordinate to one. -/
@[simp] theorem coordinateTotalDerivation_X :
    coordinateTotalDerivation (RatFunc.X : RatFunc K) = 1 := by
  have hX : (RatFunc.X : RatFunc K) = algebraMap K[X] (RatFunc K) Polynomial.X := by
    rw [RatFunc.algebraMap_X]
  rw [hX, coordinateTotalDerivation_algebraMap, polyTotalDeriv_X, map_one]

end

end GaloisForLFunctions.HTGeometry
