import GaloisForLFunctions.Bottcher.RamanujanChazy
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Eisenstein zeros and the discriminant of the weight-two jet

Ramanujan's equations recover `E₄` and `E₆` from the first two normalized derivatives of
`E₂`. The nonvanishing modular discriminant then forbids simultaneous vanishing of the
first three entries of that jet. The same argument makes the zeros of `E₄` and `E₆`
simple in the normalized differential coordinate.
-/

noncomputable section

namespace Bottcher

open UpperHalfPlane ModularForm

local notation "D" => Derivative.normalizedDerivOfComplex
local notation "P" => EisensteinSeries.E2

/-- The weight-four form is recovered from the first weight-two jet. -/
theorem eisensteinSeries_E4_eq_weightTwoJet (z : ℍ) :
    E₄ z = P z ^ 2 - 12 * D P z := by
  linear_combination 12 * normalizedDeriv_eisensteinSeries_E2 z

/-- The weight-six form is recovered from the second weight-two jet. -/
theorem eisensteinSeries_E6_eq_weightTwoJet (z : ℍ) :
    E₆ z = P z ^ 3 - 18 * P z * D P z + 36 * D (D P) z := by
  rw [normalizedDeriv_two_eisensteinSeries_E2,
    normalizedDeriv_eisensteinSeries_E2, normalizedDeriv_eisensteinSeries_E4]
  ring

/-- The modular discriminant is an explicit polynomial in `E₂`, `D E₂`, and `D² E₂`. -/
theorem discriminant_eq_weightTwoJet (z : ℍ) :
    discriminant z =
      P z ^ 2 * D P z ^ 2 / 16 - D P z ^ 3 - P z ^ 3 * D (D P) z / 24 +
        3 * P z * D P z * D (D P) z / 4 - 3 * D (D P) z ^ 2 / 4 := by
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, eisensteinSeries_E4_eq_weightTwoJet,
    eisensteinSeries_E6_eq_weightTwoJet]
  ring

/-- The discriminant forbids a common zero of the weight-four and weight-six forms. -/
theorem eisensteinSeries_E4_or_E6_ne_zero (z : ℍ) : E₄ z ≠ 0 ∨ E₆ z ≠ 0 := by
  by_contra h
  push Not at h
  have hd := discriminant_ne_zero z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq, h.1, h.2] at hd
  norm_num at hd

/-- No weight-two zero has its first two normalized derivatives both zero. -/
theorem eisensteinSeries_E2_zero_jet_nonvanishing (z : ℍ) :
    P z ≠ 0 ∨ D P z ≠ 0 ∨ D (D P) z ≠ 0 := by
  by_contra h
  push Not at h
  have hd := discriminant_ne_zero z
  rw [discriminant_eq_weightTwoJet, h.1, h.2.1, h.2.2] at hd
  norm_num at hd

/-- A zero of `E₄` has nonzero first normalized derivative. -/
theorem eisensteinSeries_E4_zero_jet_nonvanishing (z : ℍ) :
    E₄ z ≠ 0 ∨ D (E₄ : ℍ → ℂ) z ≠ 0 := by
  by_cases h4 : E₄ z = 0
  · right
    have h6 := (eisensteinSeries_E4_or_E6_ne_zero z).resolve_left (not_not.mpr h4)
    rw [normalizedDeriv_eisensteinSeries_E4, h4, mul_zero, zero_sub]
    exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr h6)
  · exact Or.inl h4

/-- A zero of `E₆` has nonzero first normalized derivative. -/
theorem eisensteinSeries_E6_zero_jet_nonvanishing (z : ℍ) :
    E₆ z ≠ 0 ∨ D (E₆ : ℍ → ℂ) z ≠ 0 := by
  by_cases h6 : E₆ z = 0
  · right
    have h4 := (eisensteinSeries_E4_or_E6_ne_zero z).resolve_right (not_not.mpr h6)
    rw [normalizedDeriv_eisensteinSeries_E6, h6, mul_zero, zero_sub]
    exact mul_ne_zero (by norm_num) (neg_ne_zero.mpr (pow_ne_zero 2 h4))
  · exact Or.inl h6

end Bottcher
