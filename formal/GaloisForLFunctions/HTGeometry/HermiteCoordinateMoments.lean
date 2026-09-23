import GaloisForLFunctions.HTGeometry.SchwartzOscillatorAlgebra
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality

/-!
# Coordinate moments of the Hermite states

Multiplication by the coordinate is `(4π)⁻¹` times the sum of the two oscillator operators, so it
acts on the Hermite basis by the ladder

`x h_n = ½ h_{n+1} + (n/2π) h_{n-1}`.

Pairing this with itself and using orthogonality together with the norm recursion
`⟨h_{n+1}, h_{n+1}⟩ = ((n+1)/π)⟨h_n, h_n⟩` gives the exact second coordinate moment of every
Hermite state.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- **Multiplication by the coordinate is self-adjoint for the bilinear pairing.** -/
theorem schwartzPair_mulXCLM (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair f (mulXCLM g) = schwartzPair (mulXCLM f) g := by
  rw [schwartzPair_eq_integral, schwartzPair_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mulXCLM_apply]
  ring

/-- **The coordinate acts on the Hermite basis by the ladder.** -/
theorem mulXCLM_hermiteSchwartz (n : ℕ) :
    mulXCLM (hermiteSchwartz n)
      = (1 / 2 : ℂ) • hermiteSchwartz (n + 1)
        + ((n : ℂ) / (2 * (π : ℂ))) • hermiteSchwartz (n - 1) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mulXCLM_eq_oscillator, creationCLM_hermiteSchwartz]
  cases n with
  | zero =>
    rw [annihilationCLM_hermiteSchwartz_zero, add_zero, smul_smul]
    simp only [Nat.cast_zero, zero_div, zero_smul, add_zero]
    congr 1
    field_simp
    norm_num
  | succ m =>
    rw [annihilationCLM_hermiteSchwartz, smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1
      field_simp
      norm_num
    · simp only [Nat.add_sub_cancel]
      congr 1
      push_cast
      field_simp
      ring

/-- **The norm recursion.** -/
theorem schwartzPair_hermiteSchwartz_succ_self (n : ℕ) :
    schwartzPair (hermiteSchwartz (n + 1)) (hermiteSchwartz (n + 1))
      = (((n : ℂ) + 1) / (π : ℂ))
        * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hadj := schwartzPair_creationCLM (hermiteSchwartz n) (hermiteSchwartz (n + 1))
  rw [creationCLM_hermiteSchwartz, annihilationCLM_hermiteSchwartz,
    schwartzPair_smul_left, schwartzPair_smul_right] at hadj
  field_simp at hadj ⊢
  linear_combination hadj

/-- **(24.186) The second coordinate moment of a Hermite state.** -/
theorem schwartzPair_mulXCLM_hermiteSchwartz_self (n : ℕ) :
    schwartzPair (mulXCLM (hermiteSchwartz n)) (mulXCLM (hermiteSchwartz n))
      = ((2 * (n : ℂ) + 1) / (4 * (π : ℂ)))
        * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mulXCLM_hermiteSchwartz]
  rw [schwartzPair_add_left, schwartzPair_add_right, schwartzPair_add_right]
  rw [schwartzPair_smul_left, schwartzPair_smul_right, schwartzPair_smul_left,
    schwartzPair_smul_right, schwartzPair_smul_left, schwartzPair_smul_right,
    schwartzPair_smul_left, schwartzPair_smul_right]
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_div, zero_mul, mul_zero, add_zero, zero_add,
      Nat.zero_sub]
    rw [schwartzPair_hermiteSchwartz_succ_self 0]
    push_cast
    field_simp
    ring
  | succ m =>
    have hne : m + 1 + 1 ≠ m + 1 - 1 := by omega
    have hne' : m + 1 - 1 ≠ m + 1 + 1 := by omega
    rw [schwartzPair_hermiteSchwartz_eq_zero hne, schwartzPair_hermiteSchwartz_eq_zero hne']
    simp only [Nat.add_sub_cancel, mul_zero, add_zero, zero_add]
    have hstep := schwartzPair_hermiteSchwartz_succ_self (m + 1)
    have hstep' := schwartzPair_hermiteSchwartz_succ_self m
    rw [hstep, hstep']
    push_cast
    field_simp
    ring

/-- **The cross pairing of two coordinate-shifted Hermite states.** -/
theorem schwartzPair_mulXCLM_hermiteSchwartz_cross (n : ℕ) :
    schwartzPair (mulXCLM (hermiteSchwartz (n + 2))) (mulXCLM (hermiteSchwartz n))
      = (((n : ℂ) + 2) / (4 * (π : ℂ)))
        * schwartzPair (hermiteSchwartz (n + 1)) (hermiteSchwartz (n + 1)) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mulXCLM_hermiteSchwartz (n + 2), mulXCLM_hermiteSchwartz n,
    show n + 2 - 1 = n + 1 from rfl]
  simp only [schwartzPair_add_left, schwartzPair_add_right, schwartzPair_smul_left,
    schwartzPair_smul_right]
  rw [schwartzPair_hermiteSchwartz_eq_zero (by omega : n + 2 + 1 ≠ n + 1),
    schwartzPair_hermiteSchwartz_eq_zero (by omega : n + 2 + 1 ≠ n - 1),
    schwartzPair_hermiteSchwartz_eq_zero (by omega : n + 1 ≠ n - 1)]
  push_cast
  field_simp
  ring

/-- **(24.186) The fourth coordinate moment of a Hermite state.** -/
theorem schwartzPair_mulXCLM_sq_hermiteSchwartz_self (n : ℕ) :
    schwartzPair (mulXCLM (mulXCLM (hermiteSchwartz n)))
        (mulXCLM (mulXCLM (hermiteSchwartz n)))
      = (3 * (2 * (n : ℂ) ^ (2 : ℕ) + 2 * (n : ℂ) + 1) / (16 * (π : ℂ) ^ (2 : ℕ)))
        * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mulXCLM_hermiteSchwartz n, map_add, map_smul, map_smul]
  simp only [schwartzPair_add_left, schwartzPair_add_right, schwartzPair_smul_left,
    schwartzPair_smul_right]
  match n with
  | 0 =>
    simp only [Nat.cast_zero, zero_div, zero_mul, mul_zero, add_zero, zero_add]
    rw [schwartzPair_mulXCLM_hermiteSchwartz_self 1,
      schwartzPair_hermiteSchwartz_succ_self 0]
    push_cast
    field_simp
    ring
  | (m + 1) =>
    rw [show m + 1 - 1 = m from rfl, show m + 1 + 1 = m + 2 from rfl]
    rw [schwartzPair_mulXCLM_hermiteSchwartz_self (m + 2),
      schwartzPair_mulXCLM_hermiteSchwartz_self m,
      schwartzPair_mulXCLM_hermiteSchwartz_cross m,
      schwartzPair_comm (mulXCLM (hermiteSchwartz m)) (mulXCLM (hermiteSchwartz (m + 2))),
      schwartzPair_mulXCLM_hermiteSchwartz_cross m]
    rw [schwartzPair_hermiteSchwartz_succ_self (m + 1),
      schwartzPair_hermiteSchwartz_succ_self m]
    push_cast
    field_simp
    ring

/-- **(24.186) The second coordinate moment, in the `∫ x² h_n²` form.** -/
theorem schwartzPair_hermiteSchwartz_second_moment (n : ℕ) :
    schwartzPair (hermiteSchwartz n) (mulXCLM (mulXCLM (hermiteSchwartz n)))
      = ((2 * (n : ℂ) + 1) / (4 * (π : ℂ)))
        * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  rw [schwartzPair_mulXCLM, schwartzPair_mulXCLM_hermiteSchwartz_self]

/-- **(24.186) The fourth coordinate moment, in the `∫ x⁴ h_n²` form.** -/
theorem schwartzPair_hermiteSchwartz_fourth_moment (n : ℕ) :
    schwartzPair (hermiteSchwartz n)
        (mulXCLM (mulXCLM (mulXCLM (mulXCLM (hermiteSchwartz n)))))
      = (3 * (2 * (n : ℂ) ^ (2 : ℕ) + 2 * (n : ℂ) + 1) / (16 * (π : ℂ) ^ (2 : ℕ)))
        * schwartzPair (hermiteSchwartz n) (hermiteSchwartz n) := by
  rw [schwartzPair_mulXCLM, schwartzPair_mulXCLM,
    schwartzPair_mulXCLM_sq_hermiteSchwartz_self]

/-- **(24.186) The universal Paley--Zygmund ratio of the actual Hermite states.**  The two
coordinate-moment coefficients of `h_n` have ratio at least `1/3`, uniformly in the level. -/
theorem hermiteCoordinateMomentRatio_ge (n : ℕ) :
    (1 : ℝ) / 3 ≤ ((2 * (n : ℝ) + 1) / (4 * Real.pi)) ^ (2 : ℕ)
      / (3 * (2 * (n : ℝ) ^ (2 : ℕ) + 2 * (n : ℝ) + 1) / (16 * Real.pi ^ (2 : ℕ))) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (0 : ℝ) < 3 * (2 * (n : ℝ) ^ (2 : ℕ) + 2 * (n : ℝ) + 1) / (16 * Real.pi ^ (2 : ℕ)) := by
    have h1 : (0 : ℝ) < 2 * (n : ℝ) ^ (2 : ℕ) + 2 * (n : ℝ) + 1 := by positivity
    positivity
  rw [le_div_iff₀ hden]
  have hexp : ((2 * (n : ℝ) + 1) / (4 * Real.pi)) ^ (2 : ℕ)
      = (2 * (n : ℝ) + 1) ^ (2 : ℕ) / (16 * Real.pi ^ (2 : ℕ)) := by
    rw [div_pow]
    congr 1
    ring
  rw [hexp]
  have hpos : (0 : ℝ) < 16 * Real.pi ^ (2 : ℕ) := by positivity
  rw [show (1 : ℝ) / 3 * (3 * (2 * (n : ℝ) ^ (2 : ℕ) + 2 * (n : ℝ) + 1) / (16 * Real.pi ^ (2 : ℕ)))
      = (2 * (n : ℝ) ^ (2 : ℕ) + 2 * (n : ℝ) + 1) / (16 * Real.pi ^ (2 : ℕ)) by ring]
  rw [div_le_div_iff_of_pos_right hpos]
  nlinarith [hn]

end GaloisForLFunctions

end
