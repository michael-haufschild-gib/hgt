import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionFisherValue

/-!
# Optimal scalar shift of the collision tangent

Applying the existing projective completion of the square shows that the
retained collision fraction is the optimal scalar shift. It is unique for
every active history; at equilibrium all shifts give zero.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Shifted tangent square built from three consecutive positive-time collision moments. -/
def egbFixedChargeAGibbsCollisionShiftedEnergy (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ) : ℝ :=
  _root_.HTGeometry.scalarShiftedQuantumTangentValue
    (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
    (egbFixedChargeAGibbsCollisionExcess n (m + 2) β E)
    (egbFixedChargeAGibbsCollisionExcess n (m + 3) β E) c

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

private theorem inactive_shift_zero (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ)
    (hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0) :
    egbFixedChargeAGibbsCollisionShiftedEnergy n m β E c = 0 := by
  have h1 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz
  have h2 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n (m + 1) β E).mpr hz
  have h3 := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n (m + 2) β E).mpr hz
  simp only [Nat.add_assoc] at h2 h3
  simp [egbFixedChargeAGibbsCollisionShiftedEnergy,
    _root_.HTGeometry.scalarShiftedQuantumTangentValue, h1, h2, h3]

/-- The projective square completion holds for every real shift and every collision history. -/
theorem egbFixedChargeAGibbsCollisionShiftedEnergy_completion (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E *
      egbFixedChargeAGibbsCollisionShiftedEnergy n m β E c =
      egbFixedChargeAGibbsCollisionHankelDefect n m β E +
        (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E * c -
          egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) ^ 2 := by
  exact _root_.HTGeometry.mass_mul_scalarShiftedQuantumTangentValue _ _ _ c

/-- The retained collision fraction realizes the normalized projective defect, even at equilibrium. -/
theorem egbFixedChargeAGibbsCollisionShiftedEnergy_canonical (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionShiftedEnergy n m β E
      (egbFixedChargeAGibbsCollisionRatio n m β E) =
      egbFixedChargeAGibbsCollisionHankelDefect n m β E /
        egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · rw [inactive_shift_zero n m β E _ hz,
      (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz]
    simp
  · exact _root_.HTGeometry.scalarShiftedQuantumTangentValue_canonical
      (active_collision_pos n m β E hz).ne' _ _

/-- The retained collision fraction minimizes the shifted tangent square over all real shifts. -/
theorem egbFixedChargeAGibbsCollisionShiftedEnergy_minimum (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ) :
    egbFixedChargeAGibbsCollisionShiftedEnergy n m β E
      (egbFixedChargeAGibbsCollisionRatio n m β E) ≤
      egbFixedChargeAGibbsCollisionShiftedEnergy n m β E c := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · rw [inactive_shift_zero n m β E _ hz, inactive_shift_zero n m β E _ hz]
  · rw [egbFixedChargeAGibbsCollisionShiftedEnergy_canonical]
    exact _root_.HTGeometry.projectiveQuantumTangentValue_div_le_shifted
      (active_collision_pos n m β E hz) _ _ c

/-- Every active collision history has a unique minimizing shift; every shift minimizes at equilibrium. -/
theorem egbFixedChargeAGibbsCollisionShiftedEnergy_minimizer_iff (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (c : ℝ) :
    egbFixedChargeAGibbsCollisionShiftedEnergy n m β E c =
      egbFixedChargeAGibbsCollisionShiftedEnergy n m β E
        (egbFixedChargeAGibbsCollisionRatio n m β E) ↔
      (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0) ∨
      c = egbFixedChargeAGibbsCollisionRatio n m β E := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp [inactive_shift_zero n m β E c hz, inactive_shift_zero n m β E _ hz, hz]
  · rw [or_iff_right hz]
    have hc := active_collision_pos n m β E hz
    have hR : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E *
        egbFixedChargeAGibbsCollisionRatio n m β E =
        egbFixedChargeAGibbsCollisionExcess n (m + 2) β E := by
      unfold egbFixedChargeAGibbsCollisionRatio
      field_simp [hc.ne'] <;> ring
    have hbase := egbFixedChargeAGibbsCollisionShiftedEnergy_completion n m β E
      (egbFixedChargeAGibbsCollisionRatio n m β E)
    rw [hR] at hbase
    have hcomp := egbFixedChargeAGibbsCollisionShiftedEnergy_completion n m β E c
    constructor
    · intro he
      rw [he] at hcomp
      have hs : (egbFixedChargeAGibbsCollisionExcess n (m + 1) β E * c -
          egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) ^ 2 = 0 := by
        nlinarith [hbase, hcomp]
      have heq : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E * c =
          egbFixedChargeAGibbsCollisionExcess n (m + 2) β E :=
        sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs)
      unfold egbFixedChargeAGibbsCollisionRatio
      apply (eq_div_iff hc.ne').mpr
      nlinarith [heq]
    · intro he
      rw [he]

end
end GaloisForLFunctions.HTGeometry
