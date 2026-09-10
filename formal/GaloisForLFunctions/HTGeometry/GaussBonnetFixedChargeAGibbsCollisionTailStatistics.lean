import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionLifetime

/-!
# Two aggregate statistics reconstruct collision relaxation

The total positive-time mass and its normalized mean time recover both
nonconstant mode energies. They therefore determine the complete later
collision history. The mean endpoints identify pure fast and slow sectors.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem mean_mul_tail_mass (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionMeanTime n β E * egbFixedChargeAGibbsCollisionTailMass n β E =
      (36 / 25 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (36 / 1225 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  by_cases ht : egbFixedChargeAGibbsCollisionTailMass n β E = 0
  · obtain ⟨ha, hb⟩ := (egbFixedChargeAGibbsCollisionTailMass_zero_iff n β E).mp ht
    simp [ht, ha, hb]
  · unfold egbFixedChargeAGibbsCollisionMeanTime
    field_simp

private theorem active_tail_mass_pos (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) :
    0 < egbFixedChargeAGibbsCollisionTailMass n β E := by
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  have hn : 0 ≤ egbFixedChargeAGibbsCollisionTailMass n β E := by
    unfold egbFixedChargeAGibbsCollisionTailMass; positivity
  exact lt_of_le_of_ne hn (fun h => hz ((egbFixedChargeAGibbsCollisionTailMass_zero_iff n β E).mp h.symm))

/-- Every nonzero collision history has a mean time between the exact fast and slow geometric means. -/
theorem egbFixedChargeAGibbsCollisionMeanTime_bounds (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then
      egbFixedChargeAGibbsCollisionMeanTime n β E = 0
    else (36 / 35 : ℝ) ≤ egbFixedChargeAGibbsCollisionMeanTime n β E ∧
      egbFixedChargeAGibbsCollisionMeanTime n β E ≤ 9 / 5 := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp [hz, egbFixedChargeAGibbsCollisionMeanTime, egbFixedChargeAGibbsCollisionTailMass, hz.1, hz.2]
  · simp only [if_neg hz]
    have hp := active_tail_mass_pos n β E hz
    have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
    have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
    constructor
    · unfold egbFixedChargeAGibbsCollisionMeanTime
      apply (le_div_iff₀ hp).mpr
      unfold egbFixedChargeAGibbsCollisionTailMass
      nlinarith
    · unfold egbFixedChargeAGibbsCollisionMeanTime
      apply (div_le_iff₀ hp).mpr
      unfold egbFixedChargeAGibbsCollisionTailMass
      nlinarith

/-- The earliest possible mean identifies exactly a nonzero pure fast-sector history. -/
theorem egbFixedChargeAGibbsCollisionMeanTime_fast_endpoint_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionMeanTime n β E = 36 / 35 ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧ 0 < egbFixedChargeAGibbsFastModeEnergy n β E := by
  constructor
  · intro hm
    have h := mean_mul_tail_mass n β E
    rw [hm] at h
    unfold egbFixedChargeAGibbsCollisionTailMass at h
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 := by nlinarith
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0 := by
      intro hb
      have hz : egbFixedChargeAGibbsCollisionMeanTime n β E = 0 := by
        simp [egbFixedChargeAGibbsCollisionMeanTime, ha, hb]
      rw [hm] at hz
      norm_num at hz
    exact ⟨ha, lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E)
      (fun h => hb h.symm)⟩
  · rintro ⟨ha, hb⟩
    unfold egbFixedChargeAGibbsCollisionMeanTime egbFixedChargeAGibbsCollisionTailMass
    rw [ha]
    field_simp [hb.ne']
    <;> ring

/-- The latest possible mean identifies exactly a nonzero pure slow-sector history. -/
theorem egbFixedChargeAGibbsCollisionMeanTime_slow_endpoint_iff (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionMeanTime n β E = 9 / 5 ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧ egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  constructor
  · intro hm
    have h := mean_mul_tail_mass n β E
    rw [hm] at h
    unfold egbFixedChargeAGibbsCollisionTailMass at h
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by nlinarith
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E ≠ 0 := by
      intro ha
      have hz : egbFixedChargeAGibbsCollisionMeanTime n β E = 0 := by
        simp [egbFixedChargeAGibbsCollisionMeanTime, ha, hb]
      rw [hm] at hz
      norm_num at hz
    exact ⟨lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E)
      (fun h => ha h.symm), hb⟩
  · rintro ⟨ha, hb⟩
    unfold egbFixedChargeAGibbsCollisionMeanTime egbFixedChargeAGibbsCollisionTailMass
    rw [hb]
    field_simp [ha.ne']
    <;> ring

/-- Total tail mass and mean time recover the initial slow Fourier energy. -/
theorem egbFixedChargeAGibbsSlowModeEnergy_from_tail_statistics (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsSlowModeEnergy n β E =
      (175 / 108 : ℝ) * egbFixedChargeAGibbsCollisionTailMass n β E *
        (egbFixedChargeAGibbsCollisionMeanTime n β E - 36 / 35) := by
  calc
    _ = (175 / 108 : ℝ) *
        ((36 / 25 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
          (36 / 1225 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E -
          (36 / 35 : ℝ) * egbFixedChargeAGibbsCollisionTailMass n β E) := by
      unfold egbFixedChargeAGibbsCollisionTailMass
      ring
    _ = _ := by rw [← mean_mul_tail_mass]; ring

/-- The same two aggregate statistics recover the initial fast Fourier energy. -/
theorem egbFixedChargeAGibbsFastModeEnergy_from_tail_statistics (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsFastModeEnergy n β E =
      (1225 / 27 : ℝ) * egbFixedChargeAGibbsCollisionTailMass n β E *
        (9 / 5 - egbFixedChargeAGibbsCollisionMeanTime n β E) := by
  calc
    _ = (1225 / 27 : ℝ) *
        ((9 / 5 : ℝ) * egbFixedChargeAGibbsCollisionTailMass n β E -
          ((36 / 25 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
            (36 / 1225 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E)) := by
      unfold egbFixedChargeAGibbsCollisionTailMass
      ring
    _ = _ := by rw [← mean_mul_tail_mass]; ring

/-- Equality of total mass and mean time is equivalent to equality of the entire positive-time collision history. -/
theorem egbFixedChargeAGibbsCollisionExcess_history_iff_tail_statistics (n : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    (∀ m : ℕ, egbFixedChargeAGibbsCollisionExcess n (m + 1) β E =
      egbFixedChargeAGibbsCollisionExcess n (m + 1) γ F) ↔
      egbFixedChargeAGibbsCollisionTailMass n β E = egbFixedChargeAGibbsCollisionTailMass n γ F ∧
        egbFixedChargeAGibbsCollisionMeanTime n β E = egbFixedChargeAGibbsCollisionMeanTime n γ F := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (egbFixedChargeAGibbsCollisionExcess_history_iff_two_values n β γ E F).mp h
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E = egbFixedChargeAGibbsSlowModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsSlowModeEnergy_reconstruction n β E,
        egbFixedChargeAGibbsSlowModeEnergy_reconstruction n γ F, h1, h2]
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E = egbFixedChargeAGibbsFastModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsFastModeEnergy_reconstruction n β E,
        egbFixedChargeAGibbsFastModeEnergy_reconstruction n γ F, h1, h2]
    constructor <;> simp only [egbFixedChargeAGibbsCollisionMeanTime, egbFixedChargeAGibbsCollisionTailMass, ha, hb]
  · rintro ⟨hT, hM⟩ m
    have ha : egbFixedChargeAGibbsSlowModeEnergy n β E = egbFixedChargeAGibbsSlowModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsSlowModeEnergy_from_tail_statistics n β E,
        egbFixedChargeAGibbsSlowModeEnergy_from_tail_statistics n γ F, hT, hM]
    have hb : egbFixedChargeAGibbsFastModeEnergy n β E = egbFixedChargeAGibbsFastModeEnergy n γ F := by
      rw [egbFixedChargeAGibbsFastModeEnergy_from_tail_statistics n β E,
        egbFixedChargeAGibbsFastModeEnergy_from_tail_statistics n γ F, hT, hM]
    rw [egbFixedChargeAGibbsCollisionExcess_two_rate n m β E,
      egbFixedChargeAGibbsCollisionExcess_two_rate n m γ F, ha, hb]

end
end GaloisForLFunctions.HTGeometry
