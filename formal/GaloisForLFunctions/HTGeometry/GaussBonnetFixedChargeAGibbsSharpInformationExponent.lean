import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSlowInformation

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Topology

private theorem geometric_lower_forces_base (c C q : ℝ) (hc : 0 < c)
    (h : ∀ m : ℕ, c * (4 / 9 : ℝ) ^ m ≤ C * (q ^ (2 : ℕ)) ^ m) : 4 / 9 ≤ q ^ (2 : ℕ) := by
  by_contra hq
  have hlt : q ^ (2 : ℕ) / (4 / 9 : ℝ) < 1 := (div_lt_one (by norm_num)).mpr (by linarith)
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ q ^ (2 : ℕ) / (4 / 9 : ℝ) by positivity) hlt
  have hbound (m : ℕ) : c ≤ C * (q ^ (2 : ℕ) / (4 / 9 : ℝ)) ^ m := by
    have hr : (4 / 9 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
    calc
      c = (c * (4 / 9 : ℝ) ^ m) / (4 / 9 : ℝ) ^ m := by field_simp
      _ ≤ (C * (q ^ (2 : ℕ)) ^ m) / (4 / 9 : ℝ) ^ m :=
        div_le_div_of_nonneg_right (h m) (by positivity)
      _ = _ := by rw [div_pow (q ^ (2 : ℕ)) (4 / 9 : ℝ) m]; ring
  have hC : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
  have hl : Tendsto (fun m : ℕ => C * (q ^ (2 : ℕ) / (4 / 9 : ℝ)) ^ m) atTop (nhds 0) := by
    simpa using hC.mul hp
  have hz : c ≤ 0 := ge_of_tendsto hl (Filter.Eventually.of_forall hbound)
  linarith

/-- The slow Gibbs law admits a geometric information bound exactly at bases at least four ninths. -/
theorem egbFixedChargeAGibbsSlow_information_exponent_iff (n : ℕ) (q : ℝ) :
    (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) ≤ C * (q ^ (2 : ℕ)) ^ m) ↔
        4 / 9 ≤ q ^ (2 : ℕ) := by
  constructor
  · rintro ⟨C, _, hC⟩
    apply geometric_lower_forces_base
      (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) / 4) C q
      (div_pos (egbFixedChargeAGibbsSlow_collision_initial_pos n) (by norm_num))
    intro m
    have hl := (egbFixedChargeAGibbsSlow_information_bounds n m).1
    nlinarith [hC m]
  · intro hq
    let C := (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)
    have hC : 0 < C := mul_pos (pow_pos (by norm_num) _) (egbFixedChargeAGibbsSlow_collision_initial_pos n)
    refine ⟨C, hC, ?_⟩
    intro m
    calc
      _ ≤ (4 / 9 : ℝ) ^ m * C := (egbFixedChargeAGibbsSlow_information_bounds n m).2
      _ ≤ (q ^ (2 : ℕ)) ^ m * C :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hq m) hC.le
      _ = _ := mul_comm _ _

/-- Squared Hellinger distinguishability has the same optimal exponential base on the slow Gibbs law. -/
theorem egbFixedChargeAGibbsSlow_hellinger_exponent_iff (n : ℕ) (q : ℝ) :
    (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) ≤ C * (q ^ (2 : ℕ)) ^ m) ↔ 4 / 9 ≤ q ^ (2 : ℕ) := by
  constructor
  · rintro ⟨C, _, hC⟩
    apply geometric_lower_forces_base
      (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) / 4) C q
      (div_pos (egbFixedChargeAGibbsSlow_collision_initial_pos n) (by norm_num))
    intro m
    have hl := (egbFixedChargeAGibbsSlow_hellinger_bounds n m).1
    nlinarith [hC m]
  · intro hq
    obtain ⟨C, hC, hm⟩ := (egbFixedChargeAGibbsSlow_information_exponent_iff n q).mpr hq
    refine ⟨C, hC, fun m => ?_⟩
    exact (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m 1 _).trans (hm m)

/-- Four ninths is the optimal exponential base for an information bound uniform over all Gibbs landscapes. -/
theorem egbFixedChargeAGibbsEntropyDeficit_uniform_exponent_iff (n : ℕ) (q : ℝ) :
    (∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (m : ℕ),
      egbFixedChargeAGibbsEntropyDeficit n m β E ≤ C * (q ^ (2 : ℕ)) ^ m) ↔ 4 / 9 ≤ q ^ (2 : ℕ) := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact (egbFixedChargeAGibbsSlow_information_exponent_iff n q).mp
      ⟨C, hC, h 1 (egbFixedChargeAGibbsSlowEnergy n)⟩
  · intro hq
    refine ⟨(2 : ℝ) ^ (n + 3), pow_pos (by norm_num) _, ?_⟩
    intro β E m
    calc
      _ ≤ (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) :=
        egbFixedChargeAGibbsEntropyDeficit_spectral_universal n m β E
      _ ≤ (4 / 9 : ℝ) ^ m * (2 : ℝ) ^ (n + 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (q ^ (2 : ℕ)) ^ m * (2 : ℝ) ^ (n + 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hq m) (by positivity)
      _ = _ := mul_comm _ _

/-- The uniform squared-Hellinger exponent across Gibbs laws is also sharp. -/
theorem egbFixedChargeAGibbsHellinger_uniform_exponent_iff (n : ℕ) (q : ℝ) :
    (∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (m : ℕ),
      finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) ≤ C * (q ^ (2 : ℕ)) ^ m) ↔ 4 / 9 ≤ q ^ (2 : ℕ) := by
  constructor
  · rintro ⟨C, hC, h⟩
    exact (egbFixedChargeAGibbsSlow_hellinger_exponent_iff n q).mp
      ⟨C, hC, h 1 (egbFixedChargeAGibbsSlowEnergy n)⟩
  · intro hq
    obtain ⟨C, hC, hm⟩ := (egbFixedChargeAGibbsEntropyDeficit_uniform_exponent_iff n q).mpr hq
    exact ⟨C, hC, fun β E m => (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E).trans (hm β E m)⟩

end
end GaloisForLFunctions.HTGeometry
