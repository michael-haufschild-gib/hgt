import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionRatioOrder

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Fraction of remaining collision excess lost at the next positive-time step. -/
def egbFixedChargeAGibbsCollisionLossFraction (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E -
    egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) /
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E

/-- For a surviving input, lost and retained fractions are complementary; erased inputs have zero loss. -/
theorem egbFixedChargeAGibbsCollisionLossFraction_complement (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionLossFraction n m β E =
      if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0
      else 1 - egbFixedChargeAGibbsCollisionRatio n m β E := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp only [if_pos hz]
    unfold egbFixedChargeAGibbsCollisionLossFraction
    rw [(egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz, div_zero]
  · simp only [if_neg hz]
    have hc : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ≠ 0 :=
      fun h => hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp h)
    unfold egbFixedChargeAGibbsCollisionLossFraction egbFixedChargeAGibbsCollisionRatio
    rw [sub_div, div_self hc]

/-- The relative loss of collision excess never increases over time. -/
theorem egbFixedChargeAGibbsCollisionLossFraction_antitone (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Antitone (fun m : ℕ => egbFixedChargeAGibbsCollisionLossFraction n m β E) := by
  intro i j hij
  have h := egbFixedChargeAGibbsCollisionRatio_monotone n β E hij
  change egbFixedChargeAGibbsCollisionLossFraction n j β E ≤ egbFixedChargeAGibbsCollisionLossFraction n i β E
  rw [egbFixedChargeAGibbsCollisionLossFraction_complement n i β E,
    egbFixedChargeAGibbsCollisionLossFraction_complement n j β E]
  split_ifs <;> linarith

/-- Strictly decreasing relative losses occur precisely for a mixture of slow and fast modes. -/
theorem egbFixedChargeAGibbsCollisionLossFraction_strictAnti_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    StrictAnti (fun m : ℕ => egbFixedChargeAGibbsCollisionLossFraction n m β E) ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧ 0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro h
    apply (egbFixedChargeAGibbsCollisionRatio_strictMono_iff n β E).mp
    intro i j hij
    have hl := h hij
    change egbFixedChargeAGibbsCollisionLossFraction n j β E < egbFixedChargeAGibbsCollisionLossFraction n i β E at hl
    change egbFixedChargeAGibbsCollisionRatio n i β E < egbFixedChargeAGibbsCollisionRatio n j β E
    rw [egbFixedChargeAGibbsCollisionLossFraction_complement n i β E,
      egbFixedChargeAGibbsCollisionLossFraction_complement n j β E] at hl
    split_ifs at hl <;> linarith
  · intro h
    have hr := (egbFixedChargeAGibbsCollisionRatio_strictMono_iff n β E).mpr h
    have hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0) := by intro he; linarith [h.1, he.1]
    intro i j hij
    have hijr := hr hij
    change egbFixedChargeAGibbsCollisionLossFraction n j β E < egbFixedChargeAGibbsCollisionLossFraction n i β E
    rw [egbFixedChargeAGibbsCollisionLossFraction_complement n i β E,
      egbFixedChargeAGibbsCollisionLossFraction_complement n j β E]
    simp only [if_neg hz]
    linarith

/-- Every surviving relative loss stays between five ninths and thirty-five thirty-sixths. -/
theorem egbFixedChargeAGibbsCollisionLossFraction_bounds (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then
      egbFixedChargeAGibbsCollisionLossFraction n m β E = 0
    else (5 / 9 : ℝ) ≤ egbFixedChargeAGibbsCollisionLossFraction n m β E ∧
      egbFixedChargeAGibbsCollisionLossFraction n m β E ≤ 35 / 36 := by
  have hr := egbFixedChargeAGibbsCollisionRatio_bounds n m β E
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simpa only [if_pos hz] using egbFixedChargeAGibbsCollisionLossFraction_complement n m β E
  · simp only [if_neg hz] at hr ⊢
    rw [egbFixedChargeAGibbsCollisionLossFraction_complement, if_neg hz]
    constructor <;> linarith [hr.1, hr.2]

/-- A plateau in fractional loss detects a pure mode or immediate equilibration. -/
theorem egbFixedChargeAGibbsCollisionLossFraction_plateau_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionLossFraction n (m + 1) β E = egbFixedChargeAGibbsCollisionLossFraction n m β E ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  constructor
  · intro h
    by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · exact Or.inl hz.1
    · apply (egbFixedChargeAGibbsCollisionRatio_plateau_iff n m β E).mp
      rw [egbFixedChargeAGibbsCollisionLossFraction_complement n (m + 1) β E,
        egbFixedChargeAGibbsCollisionLossFraction_complement n m β E] at h
      simp only [if_neg hz] at h
      linarith
  · intro h
    have hr := (egbFixedChargeAGibbsCollisionRatio_plateau_iff n m β E).mpr h
    rw [egbFixedChargeAGibbsCollisionLossFraction_complement n (m + 1) β E,
      egbFixedChargeAGibbsCollisionLossFraction_complement n m β E, hr]

end
end GaloisForLFunctions.HTGeometry
