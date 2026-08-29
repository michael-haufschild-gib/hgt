import GaloisForLFunctions.HTGeometry.SimplePoleUnit
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The additive lattice behind a multiplicative `q`-orbit

For `q = exp(2πiτ)` with `τ` off the real axis, the multiplier is not a root of unity and the
preimage of the orbit `q^ℤ` under `h ↦ exp(2πih)` is exactly the rank-two lattice `ℤ + τℤ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- The multiplier attached to a period. -/
def periodMultiplier (τ : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)

theorem periodMultiplier_ne_zero (τ : ℂ) : periodMultiplier τ ≠ 0 :=
  Complex.exp_ne_zero _

theorem periodMultiplier_zpow (τ : ℂ) (n : ℤ) :
    (periodMultiplier τ) ^ n = Complex.exp (2 * Real.pi * Complex.I * (n * τ)) := by
  rw [periodMultiplier, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **A period off the real axis gives a non-torsion multiplier.** -/
theorem periodMultiplier_zpow_ne_one {τ : ℂ} (hτ : τ.im ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    (periodMultiplier τ) ^ n ≠ 1 := by
  intro hcon
  rw [periodMultiplier_zpow, Complex.exp_eq_one_iff] at hcon
  obtain ⟨k, hk⟩ := hcon
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hnτ : (n : ℂ) * τ = (k : ℂ) := by
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero hpi) hI
    field_simp at hk
    rcases mul_eq_mul_right_iff.1 (by linear_combination hk : ((n : ℂ) * τ) * (2 * Real.pi * Complex.I)
        = (k : ℂ) * (2 * Real.pi * Complex.I)) with h | h
    · exact h
    · exact absurd h h2
  have him : ((n : ℂ) * τ).im = 0 := by
    rw [hnτ]
    simp
  rw [Complex.mul_im] at him
  simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero] at him
  rcases mul_eq_zero.1 him with h | h
  · exact hn (by exact_mod_cast h)
  · exact hτ h

/-- **The additive lattice of a multiplicative orbit.**  The preimage of `q^ℤ` under
`h ↦ exp(2πih)` is the rank-two lattice `ℤ + τℤ`. -/
theorem exp_mem_zpow_iff_lattice {τ : ℂ} (h : ℂ) :
    (∃ n : ℤ, Complex.exp (2 * Real.pi * Complex.I * h) = (periodMultiplier τ) ^ n)
      ↔ ∃ m k : ℤ, h = (m : ℂ) * τ + (k : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    rw [periodMultiplier_zpow, Complex.exp_eq_exp_iff_exists_int] at hn
    obtain ⟨k, hk⟩ := hn
    refine ⟨n, k, ?_⟩
    have hmul : (2 * Real.pi * Complex.I) * h
        = (2 * Real.pi * Complex.I) * ((n : ℂ) * τ + (k : ℂ)) := by
      rw [hk]
      ring
    exact mul_left_cancel₀ h2 hmul
  · rintro ⟨m, k, rfl⟩
    refine ⟨m, ?_⟩
    rw [periodMultiplier_zpow, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by ring⟩

end

end GaloisForLFunctions.HTGeometry
