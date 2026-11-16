import GaloisForLFunctions.HTGeometry.ConormalLiftObstruction

/-!
# Compatible motions at a double curve

For the branch model `P(P + qr)`, the two first-order normal equations
must use the same motion. Eliminating it gives a squared divisibility
condition, not merely two independent first-order conditions. This is the
local mechanism in Proposition 6.3 of *A projective Calabi–Yau threefold in
characteristic 5 non-liftable to characteristic 0*,
https://arxiv.org/abs/2611.15943.

At the polynomial parameter `r = X`, liftability is classified by exactly
two coefficients. The result holds in every characteristic.
-/

namespace GaloisForLFunctions.HTGeometry
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Elimination of a common normal motion gives the exact conormal obstruction. -/
theorem doubleCurve_motion_iff (r gq gP : R) (hr : r ≠ 0) :
    (∃ p d, gq + r * p = 0 ∧ gP + 2 * p + r * d = 0) ↔
      r ∣ gq ∧ r ^ 2 ∣ r * gP - 2 * gq := by
  constructor
  · rintro ⟨p, d, hp, hd⟩
    constructor
    · refine ⟨-p, ?_⟩
      linear_combination hp
    · refine ⟨-d, ?_⟩
      linear_combination r * hd - 2 * hp
  · rintro ⟨⟨q, hq⟩, ⟨e, he⟩⟩
    have hc : gP - 2 * q = r * e := by
      apply mul_left_cancel₀ hr
      linear_combination he + 2 * hq
    refine ⟨-q, -e, ?_, ?_⟩
    · linear_combination hq
    · linear_combination hc

/-- A regular parameter makes both components of the compatible motion unique. -/
theorem doubleCurve_motion_unique (r gq gP p d p' d' : R) (hr : r ≠ 0)
    (h : gq + r * p = 0 ∧ gP + 2 * p + r * d = 0)
    (h' : gq + r * p' = 0 ∧ gP + 2 * p' + r * d' = 0) :
    p = p' ∧ d = d' := by
  have hp : p = p' := mul_left_cancel₀ hr (by linear_combination h.1 - h'.1)
  refine ⟨hp, mul_left_cancel₀ hr ?_⟩
  rw [hp] at h
  linear_combination h.2 - h'.2

/-- For a polynomial parameter, compatibility depends only on the constant
coefficient of `gq` and the mixed first jet `gP₀ - 2 gq₁`. -/
theorem polynomial_doubleCurve_motion_iff (gq gP : R[X]) :
    (∃ p d, gq + X * p = 0 ∧ gP + 2 * p + X * d = 0) ↔
      gq.coeff 0 = 0 ∧ gP.coeff 0 = 2 * gq.coeff 1 := by
  rw [doubleCurve_motion_iff X gq gP X_ne_zero, X_dvd_iff, X_pow_dvd_iff]
  constructor
  · rintro ⟨hq, h⟩
    have h1 := h 1 (by omega)
    simp only [coeff_sub, coeff_X_mul, coeff_ofNat_mul] at h1
    exact ⟨hq, sub_eq_zero.mp h1⟩
  · rintro ⟨hq, h1⟩
    refine ⟨hq, fun n hn => ?_⟩
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp only [coeff_sub, coeff_X_mul_zero, coeff_ofNat_mul, hq, mul_zero, sub_zero]
    · simp only [coeff_sub, coeff_X_mul, coeff_ofNat_mul, h1, sub_self]

/-- Vanishing along the centre alone does not ensure a common motion: the
linear `q`-jet forces a nonzero constant `P`-jet in characteristic zero. -/
theorem doubleCurve_first_divisibility_insufficient :
    (X : ℚ[X]) ∣ X ∧
      ¬ ∃ p d : ℚ[X], X + X * p = 0 ∧ 0 + 2 * p + X * d = 0 := by
  refine ⟨dvd_refl _, ?_⟩
  rw [polynomial_doubleCurve_motion_iff]
  simp

#print axioms polynomial_doubleCurve_motion_iff
#print axioms doubleCurve_motion_unique
#print axioms doubleCurve_first_divisibility_insufficient
end GaloisForLFunctions.HTGeometry
