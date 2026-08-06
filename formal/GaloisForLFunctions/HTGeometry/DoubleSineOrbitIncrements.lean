import GaloisForLFunctions.HTGeometry.TwoCylinderGeneralTranslation
import GaloisForLFunctions.HTGeometry.DilatedCharacterOrbitObstruction

/-!
# Translating a constant-coefficient increment only dilates the outer variable

An increment of the double-sine source in the direction whose cotangent lives in the second
cylinder is a rational function of the outer coordinate with constant coefficients.  A general
translation dilates both coordinates, but on such an element the coefficient dilation is invisible:
constants are fixed by every dilation.  So the orbit of that increment under arbitrary translations
is a family of dilated cotangent models, which is exactly what the separated character obstruction
consumes.

The dilation factor of the translate `h` is `exp(l₁ h)`, and two translates lie on the same
multiplicative orbit of the structural multiplier exactly when their difference lies in the period
lattice.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Constant coefficients are fixed by the coefficient dilation -/

theorem polyCoeffScale_map_algebraMap {q : ℂ} (hq : q ≠ 0) (p : Polynomial ℂ) :
    polyCoeffScale hq (p.map (algebraMap ℂ (RatFunc ℂ)))
      = p.map (algebraMap ℂ (RatFunc ℂ)) := by
  have hcomp : ((ratFuncScale q hq : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ) :
        RatFunc ℂ →+* RatFunc ℂ).comp (algebraMap ℂ (RatFunc ℂ))
      = algebraMap ℂ (RatFunc ℂ) := by
    ext x
    exact ratFuncScale_algebraMap_base q hq x
  simp only [polyCoeffScale, Polynomial.coe_mapRingHom]
  rw [Polynomial.map_map, hcomp]

theorem cylinderCoeffScale_coeffExtend {q : ℂ} (hq : q ≠ 0) (y : RatFunc ℂ) :
    cylinderCoeffScale hq (coeffExtend (K := RatFunc ℂ) y) = coeffExtend y := by
  refine RatFunc.induction_on
    (P := fun y => cylinderCoeffScale hq (coeffExtend (K := RatFunc ℂ) y) = coeffExtend y) y ?_
  intro p s _
  rw [coeffExtend_div, cylinderCoeffScale_div, polyCoeffScale_map_algebraMap,
    polyCoeffScale_map_algebraMap]

/-! ### The outer dilation commutes with coefficient extension -/

theorem polyScale_map_algebraMap (s : ℂ) (p : Polynomial ℂ) :
    polyScale (algebraMap ℂ (RatFunc ℂ) s) (p.map (algebraMap ℂ (RatFunc ℂ)))
      = (polyScale s p).map (algebraMap ℂ (RatFunc ℂ)) := by
  rw [polyScale_eq_comp, polyScale_eq_comp, Polynomial.map_comp]
  congr 1
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

theorem ratFuncScale_coeffExtend {s : ℂ} (hs : s ≠ 0) (y : RatFunc ℂ) :
    ratFuncScale (algebraMap ℂ (RatFunc ℂ) s) (by simpa using hs)
        (coeffExtend (K := RatFunc ℂ) y)
      = coeffExtend (ratFuncScale s hs y) := by
  refine RatFunc.induction_on
    (P := fun y => ratFuncScale (algebraMap ℂ (RatFunc ℂ) s) (by simpa using hs)
      (coeffExtend (K := RatFunc ℂ) y) = coeffExtend (ratFuncScale s hs y)) y ?_
  intro p t _
  rw [coeffExtend_div, ratFuncScale_div, ratFuncScale_div, coeffExtend_div,
    polyScale_map_algebraMap, polyScale_map_algebraMap]

/-- **A general translation dilates a constant-coefficient increment only in the outer
variable.** -/
theorem twoCylTranslate_coeffExtend {q0 q1 : ℂ} (hq0 : q0 ≠ 0) (hq1 : q1 ≠ 0) (y : RatFunc ℂ) :
    twoCylTranslate hq0 hq1 (coeffExtend (K := RatFunc ℂ) y)
      = coeffExtend (ratFuncScale q1 hq1 y) := by
  rw [twoCylTranslate_apply, cylinderCoeffScale_coeffExtend, ratFuncScale_coeffExtend]

/-! ### Separation of the translates -/

/-- **Two translates lie on distinct multiplicative orbits exactly when their difference is not in
the period lattice.**  This is the coset condition of the defect matroid. -/
theorem separated_of_notMem_periodLattice {l : Fin 2 → ℂ} {ω : Fin 2 → ℂ} {h₁ h₂ : ℂ}
    (hω1 : ω 1 ≠ 0) (hl1 : l 1 = 2 * (Real.pi : ℂ) * Complex.I / ω 1)
    (hnot : ∀ m n : ℤ, h₁ - h₂ ≠ (m : ℂ) * ω 0 + (n : ℂ) * ω 1) (n : ℤ) :
    (Complex.exp (l 1 * h₁))⁻¹ * Complex.exp (l 1 * ω 0) ^ n
      ≠ (Complex.exp (l 1 * h₂))⁻¹ := by
  intro hcon
  have hA : Complex.exp (l 1 * h₁) ≠ 0 := Complex.exp_ne_zero _
  have hB : Complex.exp (l 1 * h₂) ≠ 0 := Complex.exp_ne_zero _
  have hexp : Complex.exp (l 1 * (h₂ - h₁ + (n : ℂ) * ω 0)) = 1 := by
    have h1 : Complex.exp (l 1 * (h₂ - h₁ + (n : ℂ) * ω 0))
        = Complex.exp (l 1 * h₂) * (Complex.exp (l 1 * h₁))⁻¹
          * Complex.exp (l 1 * ω 0) ^ n := by
      rw [show l 1 * (h₂ - h₁ + (n : ℂ) * ω 0)
          = l 1 * h₂ - l 1 * h₁ + (n : ℂ) * (l 1 * ω 0) by ring,
        Complex.exp_add, Complex.exp_sub, Complex.exp_int_mul]
      ring
    rw [h1]
    field_simp at hcon
    field_simp
    linear_combination hcon
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  have hl1ne : l 1 ≠ 0 := by
    rw [hl1]
    refine div_ne_zero ?_ hω1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have h2pi : 2 * (Real.pi : ℂ) * Complex.I = l 1 * ω 1 := by
    rw [hl1]
    field_simp
  have hcancel : h₂ - h₁ + (n : ℂ) * ω 0 = (k : ℂ) * ω 1 := by
    refine mul_left_cancel₀ hl1ne ?_
    rw [hk, h2pi]
    ring
  refine hnot n (-k) ?_
  push_cast
  linear_combination -hcancel

end

end GaloisForLFunctions.HTGeometry
