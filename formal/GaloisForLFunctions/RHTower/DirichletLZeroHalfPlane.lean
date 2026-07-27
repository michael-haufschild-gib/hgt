import GaloisForLFunctions.RHTower.DirichletCompletedLConjugate
import GaloisForLFunctions.RHTower.DirichletLZeroExistence
import GaloisForLFunctions.RHTower.TwistedMobiusZeroObstruction

/-!
# The zero frontier of a primitive Dirichlet L-function reaches the critical line

Conjugation sends a zero of `Λ(·,χ)` to a zero of `Λ(·,χ⁻¹)`, and the functional equation sends
that back to a zero of `Λ(·,χ)`.  The composite is the reflection `ρ ↦ 1 - conj ρ` in the critical
line, so the zero divisor is symmetric about `Re = 1/2` and some zero has `Re ≥ 1/2`.

Fed to the twisted Mellin obstruction this rules out every subpower bound of exponent below
`k - 1` on the twisted Hermitian mixed convolution coefficients.
-/

open Complex
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **Reflection of the completed zero divisor in the critical line.** -/
theorem completedLFunction_eq_zero_reflect {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {ρ : ℂ} (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    DirichletCharacter.completedLFunction χ (1 - (starRingEnd ℂ) ρ) = 0 := by
  have hconj : DirichletCharacter.completedLFunction χ⁻¹ ((starRingEnd ℂ) ρ) = 0 := by
    rw [← conj_completedLFunction hχ, hρ, map_zero]
  rw [hprim.completedLFunction_one_sub ((starRingEnd ℂ) ρ), hconj, mul_zero]

/-- **A primitive Dirichlet L-function has a zero on or right of the critical line.** -/
theorem exists_LFunction_eq_zero_half_le_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ ρ : ℂ, 1 / 2 ≤ ρ.re ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  obtain ⟨z, hz⟩ := exists_completedLFunction_eq_zero hχ
  have hpick : ∃ w : ℂ, 1 / 2 ≤ w.re ∧ DirichletCharacter.completedLFunction χ w = 0 := by
    rcases le_or_gt (1 / 2 : ℝ) z.re with h | h
    · exact ⟨z, h, hz⟩
    · refine ⟨1 - (starRingEnd ℂ) z, ?_, completedLFunction_eq_zero_reflect hχ hprim hz⟩
      rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
  obtain ⟨w, hwre, hw⟩ := hpick
  refine ⟨w, hwre, ?_⟩
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hwre
    simp at hwre
    linarith
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w (Or.inl hwne)
  rw [hw, zero_div] at hL
  exact hL

/-- **The twisted order law.**  No subpower bound of exponent below `k - 1` can hold for the
twisted Hermitian mixed convolution coefficients of a nontrivial primitive character. -/
theorem not_twistedMixedSubpower_of_lt_sub_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hlt : α < (k : ℝ) - 1) :
    ¬ (∀ M : ℕ,
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ C * ((M : ℝ) + 1) ^ α) := by
  obtain ⟨ρ, hρre, hzero⟩ := exists_LFunction_eq_zero_half_le_re hχ hprim
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have habs : (α + 1) / (2 * (k : ℝ)) < ρ.re := by
    have hhalf : (α + 1) / (2 * (k : ℝ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ hkR (by norm_num : (0 : ℝ) < 2)]
      linarith
    linarith
  exact not_twistedMixedSubpower_of_LFunction_eq_zero hχ hk hα hC hzero habs

end RHTower
