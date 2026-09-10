import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTwoRateBudgets

/-!
# Identifying the complete collision history from two measurements

The two-rate law for the critical thermal kernel from arXiv:2609.00025
makes the retained spectral energies observable from collision excess at
steps one and two. No phase or full-population reconstruction is needed.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Two consecutive positive-time collision measurements recover the slow spectral energy. -/
theorem egbFixedChargeAGibbsSlowModeEnergy_reconstruction (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsSlowModeEnergy n β E =
      (egbFixedChargeAGibbsCollisionExcess n 2 β E -
        (1 / 36 : ℝ) * egbFixedChargeAGibbsCollisionExcess n 1 β E) /
        ((4 / 9 : ℝ) * ((4 / 9 : ℝ) - 1 / 36)) := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n 1 β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n 0 β E]
  ring

/-- The same two measurements recover the fast spectral energy. -/
theorem egbFixedChargeAGibbsFastModeEnergy_reconstruction (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFastModeEnergy n β E =
      ((4 / 9 : ℝ) * egbFixedChargeAGibbsCollisionExcess n 1 β E -
        egbFixedChargeAGibbsCollisionExcess n 2 β E) /
        ((1 / 36 : ℝ) * ((4 / 9 : ℝ) - 1 / 36)) := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n 1 β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n 0 β E]
  ring

/-- Equality of the first two collision measurements is equivalent to equality of the complete positive-time history. -/
theorem egbFixedChargeAGibbsCollisionExcess_history_iff_two_values (n : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    (∀ m : ℕ, egbFixedChargeAGibbsCollisionExcess n (m + 1) β E =
      egbFixedChargeAGibbsCollisionExcess n (m + 1) γ F) ↔
      egbFixedChargeAGibbsCollisionExcess n 1 β E = egbFixedChargeAGibbsCollisionExcess n 1 γ F ∧
        egbFixedChargeAGibbsCollisionExcess n 2 β E = egbFixedChargeAGibbsCollisionExcess n 2 γ F := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h1, h2⟩ m
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E = egbFixedChargeAGibbsSlowModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsSlowModeEnergy_reconstruction n β E,
        egbFixedChargeAGibbsSlowModeEnergy_reconstruction n γ F, h1, h2]
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E = egbFixedChargeAGibbsFastModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsFastModeEnergy_reconstruction n β E,
        egbFixedChargeAGibbsFastModeEnergy_reconstruction n γ F, h1, h2]
    rw [egbFixedChargeAGibbsCollisionExcess_two_rate, egbFixedChargeAGibbsCollisionExcess_two_rate, ha, hb]

/-- Every positive-time collision history satisfies the same exact second-order recurrence. -/
theorem egbFixedChargeAGibbsCollisionExcess_recurrence (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 3) β E =
      (17 / 36 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 2) β E -
        (1 / 81 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 2) β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 1) β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n m β E]
  ring

end
end GaloisForLFunctions.HTGeometry
