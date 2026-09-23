import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionHausdorffSource

/-!
# Exact turning signs of the collision Fisher value

The Fisher shape of two positive masses is a scaled two-point variance.
Under one thermal-kernel step its sign of change is controlled exactly by
whether the fast mass is larger or smaller than four times the slow mass.
Pure-mode and equilibrium histories retain the zero convention.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The scaled two-mass Fisher shape for the fixed pair of collision rates. -/
def egbFixedChargeAGibbsCollisionFisherShape (x y : ℝ) : ℝ :=
  (25 / 36 : ℝ) * x * y / (x + y) ^ (2 : ℕ)

/-- The actual collision Fisher value is the two-mass shape of its positive source atoms. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_two_mass (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E =
      egbFixedChargeAGibbsCollisionFisherShape
        (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ)
        (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_formula,
    egbFixedChargeAGibbsCollisionHankelDefect_formula,
    egbFixedChargeAGibbsCollisionExcess_two_rate]
  change 4 * ((25 / 144 : ℝ) * (1 / 81 : ℝ) ^ (m + 1) *
      egbFixedChargeAGibbsSlowModeEnergy n β E * egbFixedChargeAGibbsFastModeEnergy n β E) /
      ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) ^ (2 : ℕ) =
    (25 / 36 : ℝ) * ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E) *
      ((1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) /
      ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E +
        (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E) ^ (2 : ℕ)
  rw [show (1 / 81 : ℝ) = (4 / 9 : ℝ) * (1 / 36 : ℝ) by norm_num, mul_pow]
  ring

private theorem shape_step_signs (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (egbFixedChargeAGibbsCollisionFisherShape x y <
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) ↔ 4 * x < y) ∧
    (egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) <
      egbFixedChargeAGibbsCollisionFisherShape x y ↔ y < 4 * x) ∧
    (egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) =
      egbFixedChargeAGibbsCollisionFisherShape x y ↔ y = 4 * x) := by
  let c : ℝ := (125 / 15552 : ℝ) * x * y * (y + 4 * x) /
    ((x + y) ^ (2 : ℕ) * ((4 / 9 : ℝ) * x + (1 / 36 : ℝ) * y) ^ (2 : ℕ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hsum : x + y ≠ 0 := (show 0 < x + y by positivity).ne'
  have hsum' : (4 / 9 : ℝ) * x + (1 / 36 : ℝ) * y ≠ 0 :=
    (show 0 < (4 / 9 : ℝ) * x + (1 / 36 : ℝ) * y by positivity).ne'
  have hd : egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) -
      egbFixedChargeAGibbsCollisionFisherShape x y = c * (y - 4 * x) := by
    dsimp [egbFixedChargeAGibbsCollisionFisherShape, c]
    field_simp [hsum, hsum']
    <;> ring
  have hd' : egbFixedChargeAGibbsCollisionFisherShape x y -
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) = c * (4 * x - y) := by
    calc
      _ = -(egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) * x) ((1 / 36 : ℝ) * y) -
        egbFixedChargeAGibbsCollisionFisherShape x y) := by ring
      _ = -(c * (y - 4 * x)) := by rw [hd]
      _ = _ := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_pos, hd, mul_pos_iff_of_pos_left hc, sub_pos]
  · rw [← sub_pos, hd', mul_pos_iff_of_pos_left hc, sub_pos]
  · rw [← sub_eq_zero, hd, mul_eq_zero]
    simp only [hc.ne', false_or, sub_eq_zero]

private theorem mixed_step_signs (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E)
    (hB : 0 < egbFixedChargeAGibbsFastModeEnergy n β E) :
    (egbFixedChargeAGibbsCollisionFisherValue n m β E <
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E ↔
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) <
        (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ)) ∧
    (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E <
      egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) <
        4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ)) ∧
    (egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E =
      egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) =
        4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ)) := by
  have hx : 0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
    change 0 < (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E
    positivity
  have hy : 0 < (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
    change 0 < (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E
    positivity
  have hxr : (egbFixedChargeAGibbsCollisionSlowSourceMass n (m + 1) β E : ℝ) =
      (4 / 9 : ℝ) * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
    change (4 / 9 : ℝ) ^ ((m + 1) + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E =
      (4 / 9 : ℝ) * ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E)
    rw [pow_succ (4 / 9 : ℝ) (m + 1)]
    ring
  have hys : (egbFixedChargeAGibbsCollisionFastSourceMass n (m + 1) β E : ℝ) =
      (1 / 36 : ℝ) * (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
    change (1 / 36 : ℝ) ^ ((m + 1) + 1) * egbFixedChargeAGibbsFastModeEnergy n β E =
      (1 / 36 : ℝ) * ((1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n β E)
    rw [pow_succ (1 / 36 : ℝ) (m + 1)]
    ring
  simp only [egbFixedChargeAGibbsCollisionFisherValue_two_mass, hxr, hys]
  exact shape_step_signs _ _ hx hy

/-- Fisher value increases exactly while both sectors survive and the fast mass exceeds four slow masses. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_increase_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n m β E <
      egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsFastModeEnergy n β E ∧
      4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) <
        (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) := by
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inl ha)
    simp [hz, ha]
  by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inr hb)
    simp [hz, hb]
  have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm ha)
  have hB := lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (Ne.symm hb)
  simpa only [hA, hB, true_and] using (mixed_step_signs n m β E hA hB).1

/-- Fisher value decreases exactly while both sectors survive and the fast mass is below four slow masses. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_decrease_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E <
      egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      0 < egbFixedChargeAGibbsSlowModeEnergy n β E ∧
      0 < egbFixedChargeAGibbsFastModeEnergy n β E ∧
      (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) <
        4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inl ha)
    simp [hz, ha]
  by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inr hb)
    simp [hz, hb]
  have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm ha)
  have hB := lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (Ne.symm hb)
  simpa only [hA, hB, true_and] using (mixed_step_signs n m β E hA hB).2.1

/-- A discrete Fisher plateau is exactly a missing sector or the fast-to-slow mass ratio four. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_plateau_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E =
      egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨
      egbFixedChargeAGibbsFastModeEnergy n β E = 0 ∨
      (egbFixedChargeAGibbsCollisionFastSourceMass n m β E : ℝ) =
        4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
  by_cases ha : egbFixedChargeAGibbsSlowModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inl ha)
    simp [hz, ha]
  by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hz (j : ℕ) := (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n j β E).mpr (Or.inr hb)
    simp [hz, hb]
  have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm ha)
  have hB := lt_of_le_of_ne (egbFixedChargeAGibbsFastModeEnergy_nonneg n β E) (Ne.symm hb)
  simpa only [ha, hb, false_or] using (mixed_step_signs n m β E hA hB).2.2

/-- Equal consecutive Fisher values are either both zero or both the universal mixed plateau level one ninth. -/
theorem egbFixedChargeAGibbsCollisionFisherValue_plateau_values (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E =
      egbFixedChargeAGibbsCollisionFisherValue n m β E ↔
      (egbFixedChargeAGibbsCollisionFisherValue n m β E = 0 ∧
        egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E = 0) ∨
      (egbFixedChargeAGibbsCollisionFisherValue n m β E = 1 / 9 ∧
        egbFixedChargeAGibbsCollisionFisherValue n (m + 1) β E = 1 / 9) := by
  constructor
  · intro he
    by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∨ egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · exact Or.inl ⟨(egbFixedChargeAGibbsCollisionFisherValue_zero_iff n m β E).mpr hz,
        (egbFixedChargeAGibbsCollisionFisherValue_zero_iff n (m + 1) β E).mpr hz⟩
    · have ha : egbFixedChargeAGibbsSlowModeEnergy n β E ≠ 0 := fun h => hz (Or.inl h)
      have hb : egbFixedChargeAGibbsFastModeEnergy n β E ≠ 0 := fun h => hz (Or.inr h)
      have hA := lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (Ne.symm ha)
      have hx : 0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) := by
        change 0 < (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n β E
        positivity
      have hy := ((egbFixedChargeAGibbsCollisionFisherValue_plateau_iff n m β E).mp he).resolve_left ha
      have hy' := hy.resolve_left hb
      have hsum : (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) +
          4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) ≠ 0 :=
        (show 0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) +
          4 * (egbFixedChargeAGibbsCollisionSlowSourceMass n m β E : ℝ) by positivity).ne'
      have hm : egbFixedChargeAGibbsCollisionFisherValue n m β E = 1 / 9 := by
        rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass, hy', egbFixedChargeAGibbsCollisionFisherShape]
        field_simp [hsum]
        <;> ring
      exact Or.inr ⟨hm, he.trans hm⟩
  · rintro (⟨hm, hn⟩ | ⟨hm, hn⟩) <;> rw [hm, hn]

end
end GaloisForLFunctions.HTGeometry
