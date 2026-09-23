import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionTailStatistics

/-!
# The exact adjacent Hankel determinant of Gibbs collision history

The two decay modes of the critical thermal kernel from arXiv:2609.00025
form a positive two-atom moment sequence. Its adjacent determinant detects
whether both nonconstant spectral sectors are occupied.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The adjacent two-by-two Hankel determinant at positive time. -/
def egbFixedChargeAGibbsCollisionHankelDefect (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  egbFixedChargeAGibbsCollisionExcess n (m + 1) β E *
    egbFixedChargeAGibbsCollisionExcess n (m + 3) β E -
      egbFixedChargeAGibbsCollisionExcess n (m + 2) β E ^ (2 : ℕ)

/-- The determinant is a positive geometric factor times the product of the two spectral energies. -/
theorem egbFixedChargeAGibbsCollisionHankelDefect_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionHankelDefect n m β E =
      (25 / 144 : ℝ) * (1 / 81 : ℝ) ^ (m + 1) *
        egbFixedChargeAGibbsSlowModeEnergy n β E * egbFixedChargeAGibbsFastModeEnergy n β E := by
  unfold egbFixedChargeAGibbsCollisionHankelDefect
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n m β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 2) β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 1) β E]
  have hr : (1 / 81 : ℝ) = (4 / 9 : ℝ) * (1 / 36 : ℝ) := by norm_num
  rw [hr, mul_pow]
  ring

/-- Every adjacent collision Hankel determinant is nonnegative. -/
theorem egbFixedChargeAGibbsCollisionHankelDefect_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsCollisionHankelDefect n m β E := by
  rw [egbFixedChargeAGibbsCollisionHankelDefect_formula]
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  positivity

/-- An adjacent determinant vanishes exactly when at least one nonconstant sector is absent. -/
theorem egbFixedChargeAGibbsCollisionHankelDefect_zero_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionHankelDefect n m β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsCollisionHankelDefect_formula]
  have hc : (25 / 144 : ℝ) ≠ 0 := by norm_num
  have hp : (1 / 81 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [mul_eq_zero, hc, hp, false_or]

/-- Strict Hankel positivity detects precisely a mixture of slow and fast spectral energies. -/
theorem egbFixedChargeAGibbsCollisionHankelDefect_pos_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsCollisionHankelDefect n m β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧ 0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsCollisionHankelDefect_formula, mul_assoc]
  have hc : 0 < (25 / 144 : ℝ) * (1 / 81 : ℝ) ^ (m + 1) := by positivity
  rw [mul_pos_iff_of_pos_left hc]
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · exact h
    · exfalso; linarith [h.1]
  · rintro ⟨ha, hb⟩
    exact mul_pos ha hb

/-- Positive-time collision excess is log-convex at every adjacent triple of times. -/
theorem egbFixedChargeAGibbsCollisionExcess_logConvex (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 2) β E ^ (2 : ℕ) ≤
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E *
        egbFixedChargeAGibbsCollisionExcess n (m + 3) β E := by
  have h := egbFixedChargeAGibbsCollisionHankelDefect_nonneg n m β E
  unfold egbFixedChargeAGibbsCollisionHankelDefect at h
  linarith

end
end GaloisForLFunctions.HTGeometry
