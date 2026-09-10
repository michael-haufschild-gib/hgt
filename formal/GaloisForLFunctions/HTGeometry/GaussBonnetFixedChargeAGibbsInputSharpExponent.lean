import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDominantCollisionBounds

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

private theorem geometric_lower_forces_base (c C r t : ℝ) (hc : 0 < c)
    (hr : 0 < r) (ht : 0 ≤ t)
    (h : ∀ m : ℕ, c * r ^ m ≤ C * t ^ m) : r ≤ t := by
  by_contra hrt
  have hlt : t / r < 1 := (div_lt_one hr).mpr (lt_of_not_ge hrt)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ht hr.le) hlt
  have hbound (m : ℕ) : c ≤ C * (t / r) ^ m := by
    have hn : r ^ m ≠ 0 := pow_ne_zero _ hr.ne'
    calc
      c = (c * r ^ m) / r ^ m := by field_simp
      _ ≤ (C * t ^ m) / r ^ m :=
        div_le_div_of_nonneg_right (h m) (pow_nonneg hr.le _)
      _ = _ := by rw [div_pow t r m]; ring
  have hC : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
  have hl : Tendsto (fun m : ℕ => C * (t / r) ^ m) atTop (nhds 0) := by
    simpa using hC.mul hp
  have hz : c ≤ 0 := ge_of_tendsto hl (Filter.Eventually.of_forall hbound)
  linarith

/-- A fixed Gibbs input admits a collision bound exactly at bases above its surviving rate. -/
theorem egbFixedChargeAGibbsCollisionExcess_input_exponent_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∃ M : ℝ, 0 < M ∧ ∀ m : ℕ,
      egbFixedChargeAGibbsCollisionExcess n m β E ≤ M * (q ^ 2) ^ m) ↔
        egbFixedChargeAGibbsDominantCollisionRate n β E ≤ q ^ 2 := by
  have hr := (egbFixedChargeAGibbsDominantCollisionRate_bounds n β E).1
  constructor
  · rintro ⟨M, _, hM⟩
    by_cases hz : egbFixedChargeAGibbsDominantCollisionRate n β E = 0
    · rw [hz]; exact sq_nonneg q
    · have hp : 0 < egbFixedChargeAGibbsDominantCollisionRate n β E :=
        lt_of_le_of_ne hr (by intro h; exact hz h.symm)
      have hW := (egbFixedChargeAGibbsDominantModeEnergy_pos_iff n β E).mpr hp
      apply geometric_lower_forces_base
        (egbFixedChargeAGibbsDominantModeEnergy n β E *
          egbFixedChargeAGibbsDominantCollisionRate n β E) (M * q ^ 2)
        _ _ (mul_pos hW hp) hp (sq_nonneg q)
      intro m
      have hl := (egbFixedChargeAGibbsCollisionExcess_dominant_bounds n m β E).1
      have hu := hM (m + 1)
      rw [pow_succ (egbFixedChargeAGibbsDominantCollisionRate n β E) m] at hl
      rw [pow_succ (q ^ 2) m] at hu
      nlinarith
  · intro hq
    let M := egbFixedChargeAGibbsCollisionExcess n 0 β E +
      egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E + 1
    have hC := egbFixedChargeAGibbsCollisionExcess_nonneg n 0 β E
    have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
    have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
    have hM : 0 < M := by dsimp [M]; linarith
    refine ⟨M, hM, ?_⟩
    intro m
    cases m with
    | zero => simp only [pow_zero, mul_one]; dsimp [M]; linarith
    | succ m =>
      have hsum : egbFixedChargeAGibbsSlowModeEnergy n β E +
          egbFixedChargeAGibbsFastModeEnergy n β E ≤ M := by dsimp [M]; linarith
      calc
        _ ≤ egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) *
            (egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E) :=
          (egbFixedChargeAGibbsCollisionExcess_dominant_bounds n m β E).2
        _ ≤ (q ^ 2) ^ (m + 1) *
            (egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hq _) (add_nonneg hA hB)
        _ ≤ (q ^ 2) ^ (m + 1) * M := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := mul_comm _ _

/-- The best entropy exponent depends on the actual Gibbs input through its surviving rate. -/
theorem egbFixedChargeAGibbsEntropyDeficit_input_exponent_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∃ M : ℝ, 0 < M ∧ ∀ m : ℕ,
      egbFixedChargeAGibbsEntropyDeficit n m β E ≤ M * (q ^ 2) ^ m) ↔
        egbFixedChargeAGibbsDominantCollisionRate n β E ≤ q ^ 2 := by
  constructor
  · rintro ⟨M, hM, hm⟩
    apply (egbFixedChargeAGibbsCollisionExcess_input_exponent_iff n β q E).mp
    refine ⟨4 * M, mul_pos (by norm_num) hM, fun m => ?_⟩
    have hl := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m β E
    nlinarith [hm m]
  · intro hq
    obtain ⟨M, hM, hm⟩ := (egbFixedChargeAGibbsCollisionExcess_input_exponent_iff n β q E).mpr hq
    refine ⟨(2 : ℝ) ^ (n + 3) * M, mul_pos (by positivity) hM, fun m => ?_⟩
    calc
      _ ≤ (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E :=
        egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E
      _ ≤ (2 : ℝ) ^ (n + 3) * (M * (q ^ 2) ^ m) :=
        mul_le_mul_of_nonneg_left (hm m) (by positivity)
      _ = _ := by ring

/-- Squared Hellinger distance has the same input-selected optimal exponential base. -/
theorem egbFixedChargeAGibbsHellingerSquared_input_exponent_iff (n : ℕ) (β q : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∃ M : ℝ, 0 < M ∧ ∀ m : ℕ,
      egbFixedChargeAGibbsHellingerSquared n m β E ≤ M * (q ^ 2) ^ m) ↔
        egbFixedChargeAGibbsDominantCollisionRate n β E ≤ q ^ 2 := by
  constructor
  · rintro ⟨M, hM, hm⟩
    apply (egbFixedChargeAGibbsCollisionExcess_input_exponent_iff n β q E).mp
    refine ⟨4 * M, mul_pos (by norm_num) hM, fun m => ?_⟩
    have hl : egbFixedChargeAGibbsCollisionExcess n m β E ≤
        4 * egbFixedChargeAGibbsHellingerSquared n m β E :=
      egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E
    nlinarith [hm m]
  · intro hq
    obtain ⟨M, hM, hm⟩ := (egbFixedChargeAGibbsEntropyDeficit_input_exponent_iff n β q E).mpr hq
    exact ⟨M, hM, fun m => (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E).trans (hm m)⟩

end
end GaloisForLFunctions.HTGeometry
