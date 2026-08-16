import GaloisForLFunctions.HTGeometry.QuadraticOrbifoldTail
import GaloisForLFunctions.HTGeometry.RationalOrderComposition

/-!
# The alternating protocol of two quadratic coarse-grainings

Composing `z ↦ z² + 1` with `z ↦ (z − 1)²` in the two possible orders gives the fourth power map
and its translate:

`(R₁(z) − 1)² = z⁴`,  `(R₂(z))² + 1 = (z − 1)⁴ + 1`.

Neither step fixes a rational current, but each transports one of the two currents `dz/z` and
`dz/(z − 1)` into the other with multiplier two, so one full period returns a current with
multiplier four.  The two period maps therefore do carry an invariant differential of weight one,
and its current drags a whole differential field into the stable observable field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions _root_.Polynomial

noncomputable section

/-- The fourth power map, the period map of the alternating protocol at phase zero. -/
def quadPow : Polynomial ℂ := X ^ 4

/-- The translated fourth power map, the period map at phase one. -/
def quadPowShift : Polynomial ℂ := (X - Polynomial.C 1) ^ 4 + Polynomial.C 1

/-! ## The two period maps -/

/-- **The phase-zero period map is the fourth power map.** -/
theorem quadTwo_comp_quadOne : quadTwo.comp quadOne = quadPow := by
  rw [quadTwo, quadPow, sub_comp, pow_comp, X_comp, C_comp, quadOne]
  ring

/-- **The phase-one period map is the translated fourth power map.** -/
theorem quadOne_comp_quadTwo : quadOne.comp quadTwo = quadPowShift := by
  rw [quadOne, quadPowShift, add_comp, pow_comp, X_comp, C_comp, quadTwo]
  ring

@[simp]
theorem natDegree_quadPow : quadPow.natDegree = 4 := by
  rw [quadPow, natDegree_X_pow]

@[simp]
theorem derivative_quadPow : Polynomial.derivative quadPow = Polynomial.C 4 * X ^ 3 := by
  rw [quadPow, Polynomial.derivative_X_pow]
  norm_num

@[simp]
theorem derivative_quadPowShift :
    Polynomial.derivative quadPowShift = Polynomial.C 4 * (X - Polynomial.C 1) ^ 3 := by
  rw [quadPowShift, Polynomial.derivative_add, Polynomial.derivative_pow,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]
  norm_num

/-! ## Rational currents -/

theorem algebraMap_ratFunc_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) P ≠ 0 :=
  fun h => hP ((RatFunc.algebraMap_injective ℂ) (by rw [h, map_zero]))

theorem ratFuncSubstitution_algebraMap_inv {R : Polynomial ℂ}
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) R) = RatFunc.C c) (P : Polynomial ℂ) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) R) hR
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹
      = (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.comp R))⁻¹ := by
  rw [map_inv₀, ratFuncSubstitution_algebraMap]

/-- **The first step transports the current at one to twice the current at zero.** -/
theorem quadOne_pullback_current
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne) hR
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - Polynomial.C 1))⁻¹
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadOne))
      = RatFunc.C 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)⁻¹ := by
  have hcomp : (X - Polynomial.C 1).comp quadOne = X ^ 2 := by
    rw [sub_comp, X_comp, C_comp, quadOne]
    ring
  rw [ratFuncSubstitution_algebraMap_inv hR, hcomp, derivative_quadOne]
  simp only [map_mul, map_pow, map_sub, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hx : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  field_simp
  ring

/-- **The second step transports the current at zero to twice the current at one.** -/
theorem quadTwo_pullback_current
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo) hR
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)⁻¹
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadTwo))
      = RatFunc.C 2 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - Polynomial.C 1))⁻¹ := by
  have hcomp : (X : Polynomial ℂ).comp quadTwo = (X - Polynomial.C 1) ^ 2 := by
    rw [X_comp, quadTwo]
  rw [ratFuncSubstitution_algebraMap_inv hR, hcomp, derivative_quadTwo]
  simp only [map_mul, map_pow, map_sub, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hx : (RatFunc.X - 1 : RatFunc ℂ) ≠ 0 := by
    have h := algebraMap_ratFunc_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℂ))
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_one] using h
  field_simp
  ring

/-! ## The invariant differential of the period maps -/

/-- **The fourth power map has an invariant differential of weight one.** -/
theorem quadPow_invariant_relation
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadPow) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadPow) hR
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)⁻¹
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadPow))
      = RatFunc.C 4 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)⁻¹ := by
  have hcomp : (X : Polynomial ℂ).comp quadPow = X ^ 4 := by
    rw [X_comp, quadPow]
  rw [ratFuncSubstitution_algebraMap_inv hR, hcomp, derivative_quadPow]
  simp only [map_mul, map_pow, map_sub, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hx : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  field_simp
  ring

/-- **The translated fourth power map has an invariant differential of weight one.** -/
theorem quadPowShift_invariant_relation
    (hR : ¬ ∃ c : ℂ, (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadPowShift) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadPowShift) hR
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - Polynomial.C 1))⁻¹
      * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.derivative quadPowShift))
      = RatFunc.C 4 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (X - Polynomial.C 1))⁻¹ := by
  have hcomp : (X - Polynomial.C 1).comp quadPowShift = (X - Polynomial.C 1) ^ 4 := by
    rw [sub_comp, X_comp, C_comp, quadPowShift]
    ring
  rw [ratFuncSubstitution_algebraMap_inv hR, hcomp, derivative_quadPowShift]
  simp only [map_mul, map_pow, map_sub, map_one, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hx : (RatFunc.X - 1 : RatFunc ℂ) ≠ 0 := by
    have h := algebraMap_ratFunc_ne_zero (Polynomial.X_sub_C_ne_zero (1 : ℂ))
    simpa only [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_one] using h
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
