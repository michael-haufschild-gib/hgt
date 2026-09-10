import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionQuantumGeometry

/-!
# Fisher value of the temporal two-mode realization

The existing pure-state Fisher scalar becomes four times the normalized
Hankel defect. It detects spectral coexistence and is also the product of
the retained collision fraction and its one-step increase.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Pure-state Fisher value for the first two shifted collision moment vectors. -/
def egbFixedChargeAGibbsCollisionFisherValue (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  _root_.HTGeometry.pureStateQuantumFisherValue
    (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
    (egbFixedChargeAGibbsCollisionExcess n (m + 2) β E)
    (egbFixedChargeAGibbsCollisionExcess n (m + 3) β E)

/-- The collision Fisher value is exactly four times the normalized temporal Gram determinant. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_formula (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E =
      4 * egbFixedChargeAGibbsCollisionHankelDefect n m β E /
        egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ^ 2 := by
  rfl

/-- The temporal Fisher value is always nonnegative, including the equilibrium convention. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 ≤ egbFixedChargeAGibbsCollisionFisherValue n m β E := by
  exact _root_.HTGeometry.pureStateQuantumFisherValue_nonneg
    (egbFixedChargeAGibbsCollisionHankelDefect_nonneg n m β E)

private theorem active_collision_pos (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬ (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) :
    0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  have hn := egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E
  have hne : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ≠ 0 := by
    intro he
    exact hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp he)
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- Strictly positive Fisher value detects the simultaneous presence of both decay sectors. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_pos_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
        0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hc := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
    simp [egbFixedChargeAGibbsCollisionFisherValue_formula, hc, hz.1]
  · have hc := active_collision_pos n m β E hz
    rw [egbFixedChargeAGibbsCollisionFisherValue_formula, div_pos_iff_of_pos_right (sq_pos_of_pos hc),
      mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)]
    exact egbFixedChargeAGibbsCollisionHankelDefect_pos_iff n m β E

/-- Fisher collapse is exactly a one-sector or equilibrium history. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_zero_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E = 0 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hc := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
    simp [egbFixedChargeAGibbsCollisionFisherValue_formula, hc, hz.1]
  · have hc := active_collision_pos n m β E hz
    rw [egbFixedChargeAGibbsCollisionFisherValue_formula]
    simp only [div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0),
      show (4 : ℝ) ≠ 0 by norm_num, hc.ne', false_or, or_false]
    exact egbFixedChargeAGibbsCollisionHankelDefect_zero_iff n m β E

/-- Fisher value measures the one-step change of the retained collision fraction. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_ratio_increment (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E =
      4 * egbFixedChargeAGibbsCollisionRatio n m β E *
        (egbFixedChargeAGibbsCollisionRatio n (m + 1) β E -
          egbFixedChargeAGibbsCollisionRatio n m β E) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_formula,
    egbFixedChargeAGibbsCollisionRatio_step_difference, egbFixedChargeAGibbsCollisionRatio]
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hc := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
    simp [hc]
  · have hc := active_collision_pos n m β E hz
    have hd := active_collision_pos n (m + 1) β E hz
    have hd' : egbFixedChargeAGibbsCollisionExcess n (m + 2) β E ≠ 0 := by
      simpa only [Nat.add_assoc] using hd.ne'
    field_simp [hc.ne', hd']
    <;> ring

end
end GaloisForLFunctions.HTGeometry
