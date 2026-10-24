import GaloisForLFunctions.goldbach.BalancedProductCollisions
import Mathlib.Data.Int.ModEq

/-!
# Exact determinant coordinates for reflected products

Eliminating the common dilation parameter retains its divisibility and both
range endpoints. The parameter is unique, so the resulting determinant
condition describes the same finite set of balanced product quadruples.
-/

namespace GaloisForLFunctions.Goldbach

open Finset

noncomputable section
set_option autoImplicit false

/-- Exact elimination of the integer parameter, including its full progression step and range. -/
theorem reflectedValues_determinant_iff
    (p : ℕ+) (q h T R u v : ℤ) :
    (∃ r : ℤ, 0 < r ∧ r ≤ R ∧ h ∣ r ∧
      u + (p : ℤ) * r = T ∧ v + q * r = T) ↔
      q * u - (p : ℤ) * v = T * (q - (p : ℤ)) ∧
        Int.ModEq ((p : ℤ) * h) u T ∧
          0 < T - u ∧ T - u ≤ R * (p : ℤ) := by
  have hp : (0 : ℤ) < (p : ℤ) := by exact_mod_cast p.pos
  rw [Int.modEq_iff_dvd]
  constructor
  · rintro ⟨r, hr, hR, ⟨s, hs⟩, hu, hv⟩
    have hdelta : T - u = r * (p : ℤ) := by linear_combination -hu
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination q * hu - (p : ℤ) * hv
    · refine ⟨s, ?_⟩
      rw [hdelta, hs]
      ring
    · rw [hdelta]
      exact mul_pos hr hp
    · rw [hdelta]
      exact (mul_le_mul_iff_left₀ hp).mpr hR
  · rintro ⟨hdet, ⟨s, hs⟩, hpos, hle⟩
    let r : ℤ := h * s
    have hdelta : T - u = r * (p : ℤ) := by
      dsimp [r]
      rw [hs]
      ring
    have hr : 0 < r := by
      apply (mul_lt_mul_iff_left₀ hp).mp
      simpa only [zero_mul, hdelta] using hpos
    have hR : r ≤ R := by
      apply (mul_le_mul_iff_left₀ hp).mp
      simpa only [hdelta] using hle
    refine ⟨r, hr, hR, ⟨s, rfl⟩, ?_, ?_⟩
    · linear_combination -hdelta
    · apply mul_left_cancel₀ hp.ne'
      linear_combination -hdet - q * hdelta

/-- The determinant and progression conditions reconstruct exactly one dilation parameter. -/
theorem reflectedValues_existsUnique_iff_determinant
    (p : ℕ+) (q h T R u v : ℤ) :
    (∃! r : ℤ, 0 < r ∧ r ≤ R ∧ h ∣ r ∧
      u + (p : ℤ) * r = T ∧ v + q * r = T) ↔
      q * u - (p : ℤ) * v = T * (q - (p : ℤ)) ∧
        Int.ModEq ((p : ℤ) * h) u T ∧
          0 < T - u ∧ T - u ≤ R * (p : ℤ) := by
  constructor
  · intro he
    exact (reflectedValues_determinant_iff p q h T R u v).mp he.exists
  · intro hd
    obtain ⟨r, hr⟩ := (reflectedValues_determinant_iff p q h T R u v).mpr hd
    refine ⟨r, hr, ?_⟩
    intro s hs
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast p.pos.ne'
    apply mul_left_cancel₀ hp
    linear_combination hs.2.2.2.1 - hr.2.2.2.1

/-- The product of two actual coordinates in `(X,2X]`, read in the integers. -/
def reflectedBoxProduct {X : ℕ} (a : Fin X × Fin X) : ℤ :=
  (balancedIntervalValue a.1 : ℤ) * (balancedIntervalValue a.2 : ℤ)

/-- Balanced product quadruples meeting the two reflected dilation equations. -/
def reflectedProductPairs (X : ℕ) (p : ℕ+) (q h T R : ℤ) :
    Finset ((Fin X × Fin X) × (Fin X × Fin X)) := by
  classical
  exact univ.filter fun a => ∃ r : ℤ, 0 < r ∧ r ≤ R ∧ h ∣ r ∧
    reflectedBoxProduct a.1 + (p : ℤ) * r = T ∧
      reflectedBoxProduct a.2 + q * r = T

/-- The same balanced quadruples in determinant, progression, and range coordinates. -/
def determinantProductPairs (X : ℕ) (p : ℕ+) (q h T R : ℤ) :
    Finset ((Fin X × Fin X) × (Fin X × Fin X)) := by
  classical
  exact univ.filter fun a =>
    q * reflectedBoxProduct a.1 - (p : ℤ) * reflectedBoxProduct a.2 =
        T * (q - (p : ℤ)) ∧
      Int.ModEq ((p : ℤ) * h) (reflectedBoxProduct a.1) T ∧
        0 < T - reflectedBoxProduct a.1 ∧
          T - reflectedBoxProduct a.1 ≤ R * (p : ℤ)

/-- Parameter elimination preserves the actual finite set, hence every weighted count on it. -/
theorem reflectedProductPairs_eq_determinantProductPairs
    (X : ℕ) (p : ℕ+) (q h T R : ℤ) :
    reflectedProductPairs X p q h T R = determinantProductPairs X p q h T R := by
  classical
  ext a
  simp only [reflectedProductPairs, determinantProductPairs, mem_filter,
    mem_univ, true_and, reflectedValues_determinant_iff]

end
end GaloisForLFunctions.Goldbach
