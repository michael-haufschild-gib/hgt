import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHankelDefect

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The fraction of collision excess retained by the next positive-time transition. -/
def egbFixedChargeAGibbsCollisionRatio (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E

private theorem active_collision_pos (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) :
    0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  have hn := egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E
  exact lt_of_le_of_ne hn (fun h => hz
    ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp h.symm))

/-- Change in the retained collision fraction is exactly the adjacent Hankel determinant divided by two positive-time masses. -/
theorem egbFixedChargeAGibbsCollisionRatio_step_difference (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionRatio n (m + 1) β E - egbFixedChargeAGibbsCollisionRatio n m β E =
      egbFixedChargeAGibbsCollisionHankelDefect n m β E /
        (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E *
          egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) := by
  unfold egbFixedChargeAGibbsCollisionRatio egbFixedChargeAGibbsCollisionHankelDefect
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have h1 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
    have h2 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n (m + 1) β E).mpr hz
    have h3 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n (m + 2) β E).mpr hz
    simp only [h1, h2, h3, zero_div, zero_sub, sub_zero, zero_mul, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · have h1 := (active_collision_pos n m β E hz).ne'
    have h2 := (active_collision_pos n (m + 1) β E hz).ne'
    field_simp [h1, h2]
    <;> ring

/-- The retained collision fraction never decreases as the faster spectral component fades. -/
theorem egbFixedChargeAGibbsCollisionRatio_monotone (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Monotone (fun m : ℕ => egbFixedChargeAGibbsCollisionRatio n m β E) := by
  apply monotone_nat_of_le_succ
  intro m
  have h := div_nonneg (egbFixedChargeAGibbsCollisionHankelDefect_nonneg n m β E)
    (mul_nonneg (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E)
      (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 2) β E))
  rw [← egbFixedChargeAGibbsCollisionRatio_step_difference] at h
  linarith

/-- Strictly increasing retained fractions occur exactly when both nonconstant spectral sectors are present. -/
theorem egbFixedChargeAGibbsCollisionRatio_strictMono_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    StrictMono (fun m : ℕ => egbFixedChargeAGibbsCollisionRatio n m β E) ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧ 0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro h
    have hlt : egbFixedChargeAGibbsCollisionRatio n 0 β E < egbFixedChargeAGibbsCollisionRatio n 1 β E :=
      h (by norm_num)
    have hs := egbFixedChargeAGibbsCollisionRatio_step_difference n 0 β E
    have hn : egbFixedChargeAGibbsCollisionHankelDefect n 0 β E ≠ 0 := by
      intro hz; rw [hz, zero_div] at hs; linarith
    exact (egbFixedChargeAGibbsCollisionHankelDefect_pos_iff n 0 β E).mp
      (lt_of_le_of_ne (egbFixedChargeAGibbsCollisionHankelDefect_nonneg n 0 β E) (fun h => hn h.symm))
  · intro h
    have hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0) := by
      intro he; linarith [h.1, he.1]
    apply strictMono_nat_of_lt_succ
    intro m
    have hp := div_pos ((egbFixedChargeAGibbsCollisionHankelDefect_pos_iff n m β E).mpr h)
      (mul_pos (active_collision_pos n m β E hz) (active_collision_pos n (m + 1) β E hz))
    rw [← egbFixedChargeAGibbsCollisionRatio_step_difference] at hp
    linarith

/-- Equality of two consecutive retained fractions detects a pure sector or immediate equilibration. -/
theorem egbFixedChargeAGibbsCollisionRatio_plateau_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionRatio n (m + 1) β E = egbFixedChargeAGibbsCollisionRatio n m β E ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  have hs := egbFixedChargeAGibbsCollisionRatio_step_difference n m β E
  constructor
  · intro he
    by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · exact Or.inl hz.1
    · have h1 := (active_collision_pos n m β E hz).ne'
      have h2 := (active_collision_pos n (m + 1) β E hz).ne'
      rw [he, sub_self] at hs
      field_simp [h1, h2] at hs
      apply (egbFixedChargeAGibbsCollisionHankelDefect_zero_iff n m β E).mp
      linarith
  · intro h
    rw [(egbFixedChargeAGibbsCollisionHankelDefect_zero_iff n m β E).mpr h, zero_div] at hs
    linarith

/-- Every surviving retained fraction stays between the fast and slow spectral rates. -/
theorem egbFixedChargeAGibbsCollisionRatio_bounds (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then
      egbFixedChargeAGibbsCollisionRatio n m β E = 0
    else (1 / 36 : ℝ) ≤ egbFixedChargeAGibbsCollisionRatio n m β E ∧
      egbFixedChargeAGibbsCollisionRatio n m β E ≤ 4 / 9 := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp only [if_pos hz]
    unfold egbFixedChargeAGibbsCollisionRatio
    rw [(egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n (m + 1) β E).mpr hz, zero_div]
  · simp only [if_neg hz]
    have hp := active_collision_pos n m β E hz
    have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
    have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
    have hl : egbFixedChargeAGibbsCollisionExcess n (m + 2) β E -
        (1 / 36 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E =
          (5 / 12 : ℝ) * (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E := by
      rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 1) β E,
        egbFixedChargeAGibbsCollisionExcess_two_rate n m β E]
      ring
    have hu : (4 / 9 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E -
        egbFixedChargeAGibbsCollisionExcess n (m + 2) β E =
          (5 / 12 : ℝ) * (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E := by
      rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 1) β E,
        egbFixedChargeAGibbsCollisionExcess_two_rate n m β E]
      ring
    have hl0 : 0 ≤ egbFixedChargeAGibbsCollisionExcess n (m + 2) β E -
        (1 / 36 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by rw [hl]; positivity
    have hu0 : 0 ≤ (4 / 9 : ℝ) * egbFixedChargeAGibbsCollisionExcess n (m + 1) β E -
        egbFixedChargeAGibbsCollisionExcess n (m + 2) β E := by rw [hu]; positivity
    unfold egbFixedChargeAGibbsCollisionRatio
    exact ⟨(le_div_iff₀ hp).mpr (by linarith), (div_le_iff₀ hp).mpr (by linarith)⟩

end
end GaloisForLFunctions.HTGeometry
