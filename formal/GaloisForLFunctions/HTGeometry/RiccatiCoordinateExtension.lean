import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential

/-!
# Adjoining a coordinate with a prescribed derivative

Extending a differential field `K` by a transcendental coordinate whose derivative is a prescribed
rational function of that coordinate produces a differential field `K(X)`.  Taking the prescribed
value to be `X²/a` realises the Boltzmann coordinate `H = −a/log w`, whose Euler derivative obeys
the Riccati relation `θH = H²/a`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc Differential

noncomputable section

variable {K : Type*} [Field K] [Differential K]

local instance rcIntAlgebraPoly : Algebra ℤ (Polynomial K) := Ring.toIntAlgebra _
local instance rcIntAlgebraRatFunc : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

local instance rcIntTower : IsScalarTower ℤ (Polynomial K) (RatFunc K) :=
  IsScalarTower.of_algebraMap_eq fun n => by
    show ((n : ℤ) : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) ((n : ℤ) : Polynomial K)
    rw [map_intCast]

/-- The polynomial derivation that differentiates coefficients by the derivation of `K` and sends
the coordinate to the prescribed value `q`. -/
def riccatiPolyDerivation (q : RatFunc K) : Derivation ℤ (Polynomial K) (RatFunc K) where
  toFun p := algebraMap (Polynomial K) (RatFunc K) (coeffDeriv p)
      + q * algebraMap (Polynomial K) (RatFunc K) (Polynomial.derivative p)
  map_add' p r := by
    simp only [coeffDeriv_add, map_add, Polynomial.derivative_add]
    ring
  map_smul' n p := by
    simp only [RingHom.id_apply]
    rw [show coeffDeriv (n • p) = n • coeffDeriv p from map_zsmul (coeffDerivHom K) n p,
      show Polynomial.derivative (n • p) = n • Polynomial.derivative p from
        map_zsmul (Polynomial.derivative (R := K)) n p, map_zsmul, map_zsmul]
    rw [smul_add, mul_smul_comm]
  map_one_eq_zero' := by
    simp
  leibniz' p r := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, coeffDeriv_mul,
      Polynomial.derivative_mul, map_add, map_mul]
    ring

@[simp] theorem riccatiPolyDerivation_apply (q : RatFunc K) (p : Polynomial K) :
    riccatiPolyDerivation q p
      = algebraMap (Polynomial K) (RatFunc K) (coeffDeriv p)
        + q * algebraMap (Polynomial K) (RatFunc K) (Polynomial.derivative p) := rfl

/-- The derivation of `K(X)` extending that of `K` with `X′ = q`. -/
def riccatiDerivation (q : RatFunc K) : Derivation ℤ (RatFunc K) (RatFunc K) :=
  GaloisForLFunctions.fractionRingDerivation (riccatiPolyDerivation q)

@[simp] theorem riccatiDerivation_algebraMap (q : RatFunc K) (p : Polynomial K) :
    riccatiDerivation q (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) (coeffDeriv p)
        + q * algebraMap (Polynomial K) (RatFunc K) (Polynomial.derivative p) :=
  GaloisForLFunctions.fractionRingDerivation_algebraMap (riccatiPolyDerivation q) p

/-- The differential structure of `K(X)` with `X′ = q`. -/
@[reducible] def riccatiDifferential (q : RatFunc K) : Differential (RatFunc K) where
  deriv := riccatiDerivation q

theorem riccatiDifferential_deriv (q : RatFunc K) (y : RatFunc K) :
    (riccatiDifferential q).deriv y = riccatiDerivation q y := rfl

theorem riccatiDerivation_X (q : RatFunc K) : riccatiDerivation q (RatFunc.X : RatFunc K) = q := by
  have hX : (RatFunc.X : RatFunc K)
      = algebraMap (Polynomial K) (RatFunc K) Polynomial.X := (RatFunc.algebraMap_X).symm
  rw [hX, riccatiDerivation_algebraMap, Polynomial.derivative_X, map_one, mul_one,
    show coeffDeriv (Polynomial.X : Polynomial K) = 0 from by
      refine Polynomial.ext fun n => ?_
      rw [coeffDeriv_coeff, Polynomial.coeff_X, Polynomial.coeff_zero]
      by_cases h : 1 = n
      · rw [if_pos h, Derivation.map_one_eq_zero]
      · rw [if_neg h, map_zero],
    map_zero, zero_add]

theorem riccatiDerivation_algebraMap_const (q : RatFunc K) (c : K) :
    riccatiDerivation q (algebraMap K (RatFunc K) c) = algebraMap K (RatFunc K) (c′) := by
  have hC : algebraMap K (RatFunc K) c
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) := (RatFunc.algebraMap_C c).symm
  rw [hC, riccatiDerivation_algebraMap, Polynomial.derivative_C, map_zero, mul_zero, add_zero,
    show coeffDeriv (Polynomial.C c) = Polynomial.C (c′) from by
      refine Polynomial.ext fun n => ?_
      rw [coeffDeriv_coeff, Polynomial.coeff_C, Polynomial.coeff_C]
      by_cases h : n = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, map_zero]]
  exact (RatFunc.algebraMap_C (c′))

end

end GaloisForLFunctions.HTGeometry
