import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rational rescalings separate additive characters

An additive character into the multiplicative complex numbers is trivial if two
distinct rational rescalings agree. A conjugate pairing identity reduces to this
cancellation law after applying the two rescalings once more.
-/

open Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Distinct rational rescalings can agree only for the trivial additive character. -/
theorem rational_character_eq_one_of_rescaling (χ : ℚ → ℂ) (h0 : χ 0 = 1)
    (ha : ∀ x y, χ (x + y) = χ x * χ y) {u v : ℚ} (huv : u ≠ v)
    (hs : ∀ t, χ (u * t) = χ (v * t)) : ∀ t, χ t = 1 := by
  have hne (t : ℚ) : χ t ≠ 0 := by
    intro hz
    have h := ha t (-t)
    rw [add_neg_cancel, h0, hz, zero_mul] at h
    exact one_ne_zero h
  have he (t : ℚ) : χ ((u - v) * t) = 1 := by
    apply mul_right_cancel₀ (hne (v * t))
    rw [one_mul, ← ha, show (u - v) * t + v * t = u * t by ring, hs]
  intro t
  have h := he (t / (u - v))
  have harg : (u - v) * (t / (u - v)) = t := by
    field_simp [sub_ne_zero.mpr huv]
  rw [harg] at h
  exact h

/-- Conjugate rescalings with different squared factors force character triviality. -/
theorem rational_character_eq_one_of_conjugate_rescaling (χ : ℚ → ℂ) (h0 : χ 0 = 1)
    (ha : ∀ x y, χ (x + y) = χ x * χ y) {u v : ℚ} (huv : u ^ 2 ≠ v ^ 2)
    (hs : ∀ t, conj (χ (u * t)) * χ (v * t) = 1) : ∀ t, χ t = 1 := by
  have hne (t : ℚ) : χ t ≠ 0 := by
    intro hz
    have h := ha t (-t)
    rw [add_neg_cancel, h0, hz, zero_mul] at h
    exact one_ne_zero h
  apply rational_character_eq_one_of_rescaling χ h0 ha huv
  intro t
  have h1 := hs (u * t)
  have h2 := congrArg conj (hs (v * t))
  simp only [map_mul, conj_conj, map_one] at h2
  have huu : u * (u * t) = u ^ 2 * t := by ring
  have hvv : v * (v * t) = v ^ 2 * t := by ring
  have huv' : u * (v * t) = v * (u * t) := by ring
  rw [huu] at h1
  rw [hvv, huv'] at h2
  have he : conj (χ (u ^ 2 * t)) = conj (χ (v ^ 2 * t)) := by
    apply mul_right_cancel₀ (hne (v * (u * t)))
    rw [h1, mul_comm, h2]
  simpa only [conj_conj] using congrArg conj he

#print axioms rational_character_eq_one_of_rescaling
#print axioms rational_character_eq_one_of_conjugate_rescaling
end GaloisForLFunctions.BiarithmeticGeometry
