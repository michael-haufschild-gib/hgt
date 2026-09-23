import GaloisForLFunctions.HTGeometry.RatFuncLaurentShift
import GaloisForLFunctions.HTGeometry.RationalFunctionPartialInvariant

/-!
# The rational function field is a differential subfield of the Laurent field at infinity

The embedding `ℂ(s) ↪ ℂ((s⁻¹))` intertwines the ordinary derivative of rational functions with
`d/ds`, because both send the coordinate to `1`.
-/

open PowerSeries
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance ratFuncLaurentDifferentialInst1 : Differential (LaurentSeries ℂ) := laurentSDifferential

theorem deriv_laurentCHom (c : ℂ) : (laurentCHom c)′ = 0 := by
  show (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (PowerSeries.C c))′ = 0
  rw [laurentSDeriv_algebraMap, coordDerivPS, PowerSeries.derivative_C, mul_zero, map_zero]

theorem polyToLaurent_C (c : ℂ) : polyToLaurent (Polynomial.C c) = laurentCHom c := by
  rw [polyToLaurent]
  simp

theorem polyToLaurent_X : polyToLaurent (Polynomial.X : Polynomial ℂ) = coordS := by
  rw [polyToLaurent]
  simp

theorem deriv_polyToLaurent (p : Polynomial ℂ) :
    (polyToLaurent p)′ = polyToLaurent (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on with
  | C c =>
      rw [polyToLaurent_C, Polynomial.derivative_C, map_zero, deriv_laurentCHom]
  | add p q hp hq =>
      rw [map_add, laurentSDeriv_add, hp, hq, ← map_add, ← Polynomial.derivative_add]
  | monomial n c _ =>
      have hlhs : polyToLaurent (Polynomial.C c * Polynomial.X ^ (n + 1))
          = laurentCHom c * coordS ^ (n + 1) := by
        rw [map_mul, map_pow, polyToLaurent_C, polyToLaurent_X]
      have hder : Polynomial.derivative (Polynomial.C c * Polynomial.X ^ (n + 1))
          = Polynomial.C (c * ((n : ℂ) + 1)) * Polynomial.X ^ n := by
        rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Polynomial.C_mul]
        push_cast
        ring
      have hrhs : polyToLaurent (Polynomial.C (c * ((n : ℂ) + 1)) * Polynomial.X ^ n)
          = laurentCHom (c * ((n : ℂ) + 1)) * coordS ^ n := by
        rw [map_mul, map_pow, polyToLaurent_C, polyToLaurent_X]
      rw [hlhs, hder, hrhs, laurentSDeriv_mul, deriv_laurentCHom, mul_zero, add_zero,
        laurentSDeriv_pow, deriv_coordS, mul_one]
      simp only [Nat.add_sub_cancel]
      rw [map_mul, map_add, map_natCast, map_one]
      push_cast
      ring

/-! ### The differential structure of the rational function field -/

local instance ratFuncIntAlgebra : Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

/-- `d/ds` on the rational function field. -/
@[reducible] def ratFuncSDifferential : Differential (RatFunc ℂ) where
  deriv := Derivation.restrictScalars ℤ (ratFuncDerivative ℂ)

local instance ratFuncLaurentDifferentialInst2 : Differential (RatFunc ℂ) := ratFuncSDifferential

theorem ratFuncSDeriv_apply (r : RatFunc ℂ) : r′ = ratFuncDerivative ℂ r := by
  show (Derivation.restrictScalars ℤ (ratFuncDerivative ℂ)) r = _
  rw [Derivation.coe_restrictScalars]

theorem ratFuncSDeriv_algebraMap (p : Polynomial ℂ) :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)′
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative p) := by
  rw [ratFuncSDeriv_apply, ratFuncDerivative_algebraMap]

theorem ratFuncSDeriv_mul (x y : RatFunc ℂ) : (x * y)′ = x * y′ + y * x′ := by
  simp only [ratFuncSDeriv_apply, Derivation.leibniz, smul_eq_mul]

/-- **The embedding is a morphism of differential fields.** -/
theorem deriv_ratToLaurent (r : RatFunc ℂ) :
    (ratToLaurent r)′ = ratToLaurent (r′) := by
  have hq : (algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom) ≠ 0 := by
    intro hc
    exact RatFunc.denom_ne_zero r (RatFunc.algebraMap_injective ℂ (by rw [hc, map_zero]))
  have hqL : polyToLaurent r.denom ≠ 0 := by
    intro hc
    have : ratToLaurent (algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom) = 0 := by
      rw [ratToLaurent_algebraMap]; exact hc
    exact hq (ratToLaurent_injective (by rw [this, map_zero]))
  have hnum : r * algebraMap (Polynomial ℂ) (RatFunc ℂ) r.denom
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) r.num := by
    have h := RatFunc.num_div_denom r
    field_simp at h
    linear_combination -h
  -- differentiate in the rational function field and transport
  have hrat := congrArg (fun z : RatFunc ℂ => z′) hnum
  simp only [ratFuncSDeriv_mul, ratFuncSDeriv_algebraMap] at hrat
  have hratL := congrArg ratToLaurent hrat
  simp only [map_add, map_mul, ratToLaurent_algebraMap] at hratL
  -- differentiate in the Laurent field
  have hlaur := congrArg (fun z : LaurentSeries ℂ => z′) (congrArg ratToLaurent hnum)
  simp only [map_mul, ratToLaurent_algebraMap, laurentSDeriv_mul, deriv_polyToLaurent] at hlaur
  have hzero : polyToLaurent r.denom * (ratToLaurent (r′) - (ratToLaurent r)′) = 0 := by
    linear_combination hratL - hlaur
  rcases mul_eq_zero.mp hzero with hc | hc
  · exact absurd hc hqL
  · exact (sub_eq_zero.mp hc).symm

end

end GaloisForLFunctions.HTGeometry
