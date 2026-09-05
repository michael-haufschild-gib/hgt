import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaModularInvariant
import Mathlib.Tactic

/-!
# Global sign laws for Brizard's Weierstrass invariants

The invariant formulas in equations (74)--(76) of arXiv:2607.21750 admit complete real
classifications.  The cubic invariant factors through the three real lemniscatic moduli
`{-1, 1/2, 2}`; the discriminant is positive precisely off the singular moduli `{0,1}`.
Consequently every nonsingular real Brizard curve has `j ≥ 1728`, with equality exactly on the
three-member lemniscatic orbit.  This derives the global modular extremum directly from the paper's
identity `Δ = g₂³ - 27g₃²`, without analytic estimates.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Complete linear factorization of the numerator in paper equation (75). -/
theorem g₃_factor (P : Parameters) :
    g₃ P =
      4 * (2 * P.modulus - 1) * (P.modulus + 1) * (P.modulus - 2) /
        (27 * (P.q₀ : ℝ) ^ 3) := by
  rw [g₃]
  congr 1
  ring

/-- Exactly three real moduli make Brizard's weight-six invariant vanish. -/
theorem g₃_eq_zero_iff (P : Parameters) :
    g₃ P = 0 ↔
      P.modulus = -1 ∨ P.modulus = 1 / 2 ∨ P.modulus = 2 := by
  rw [g₃_factor, div_eq_zero_iff]
  have hden : 27 * (P.q₀ : ℝ) ^ 3 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 3 P.q₀.ne_zero)
  simp only [hden, or_false]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · right
          left
          linarith
      · left
        linarith
    · right
      right
      linarith
  · rintro (h | h | h) <;> rw [h] <;> norm_num

/-- Nonsingularity is equivalent to strict positivity of the paper's real discriminant. -/
theorem discriminant_pos_iff (P : Parameters) :
    0 < discriminant P ↔ P.modulus ≠ 0 ∧ P.modulus ≠ 1 := by
  constructor
  · intro h
    constructor
    · intro hm
      rw [discriminant, hm] at h
      norm_num at h
    · intro hm
      rw [discriminant, hm] at h
      norm_num at h
  · intro hm
    have hne : discriminant P ≠ 0 := by
      intro hzero
      rcases (discriminant_eq_zero_iff P).mp hzero with h | h
      · exact hm.1 h
      · exact hm.2 h
    exact lt_of_le_of_ne (discriminant_nonneg P) hne.symm

/-- Paper parameter data away from the two singular Legendre moduli. -/
abbrev NonsingularParameters :=
  {P : Parameters // P.modulus ≠ 0 ∧ P.modulus ≠ 1}

/-- Every nonsingular real member of Brizard's family lies above the real modular minimum. -/
theorem parameterJ_ge_1728 (P : NonsingularParameters) :
    1728 ≤ parameterJ P := by
  have hΔ : 0 < discriminant P := (discriminant_pos_iff P).mpr P.property
  rw [parameterJ, g₂_cubed_sub_g₃_sq]
  rw [le_div_iff₀ hΔ]
  rw [← g₂_cubed_sub_g₃_sq]
  nlinarith [sq_nonneg (g₃ P)]

/-- Equality in the real modular bound is exactly the full lemniscatic orbit. -/
theorem parameterJ_eq_1728_iff (P : NonsingularParameters) :
    parameterJ P = 1728 ↔
      P.val.modulus = -1 ∨ P.val.modulus = 1 / 2 ∨ P.val.modulus = 2 := by
  have hΔ : discriminant P ≠ 0 := ne_of_gt ((discriminant_pos_iff P).mpr P.property)
  constructor
  · intro h
    rw [parameterJ, g₂_cubed_sub_g₃_sq] at h
    field_simp [hΔ] at h
    have hg₃sq : g₃ P ^ 2 = 0 := by
      have hrel := g₂_cubed_sub_g₃_sq P
      nlinarith
    exact (g₃_eq_zero_iff P).mp (sq_eq_zero_iff.mp hg₃sq)
  · intro h
    have hg₃ : g₃ P = 0 := (g₃_eq_zero_iff P).mpr h
    rw [parameterJ, hg₃]
    have hg₂ : g₂ P ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt (g₂_pos P))
    field_simp [hg₂]
    ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
