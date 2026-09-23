import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpectralCollision

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exact spectral rate bounds remaining relative information at every transition count. -/
theorem egbFixedChargeAGibbsEntropyDeficit_spectral_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E ≤
      (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) := by
  calc
    _ ≤ (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E :=
      egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E
    _ ≤ (2 : ℝ) ^ (n + 3) * ((4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E) :=
      mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsCollisionExcess_spectral_bound n m β E)
        (by positivity)
    _ = _ := by ring

/-- An energy-independent spectral bound controls the information deficit of every Gibbs law. -/
theorem egbFixedChargeAGibbsEntropyDeficit_spectral_universal (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E ≤
      (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) := by
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := mul_le_mul_of_nonneg_left
    (egbFixedChargeAGibbsCollisionExcess_le_uniform_complement n 0 β E)
    (show 0 ≤ (2 : ℝ) ^ (n + 3) by positivity)
  have he : (2 : ℝ) ^ (n + 3) * (1 - ((2 : ℝ) ^ (n + 3))⁻¹) =
      (2 : ℝ) ^ (n + 3) - 1 := by field_simp
  rw [he] at h
  exact (egbFixedChargeAGibbsEntropyDeficit_spectral_bound n m β E).trans
    (mul_le_mul_of_nonneg_left h (by positivity))

/-- The spectral estimate gives an explicit lower bound on Shannon entropy after every step. -/
theorem egbFixedChargeAGibbsEntropy_spectral_lower (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (n + 3 : ℝ) * Real.log 2 - (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) ≤
      entropy (egbFixedChargeAGibbsMarkovPopulation n m β E) := by
  have h := egbFixedChargeAGibbsEntropyDeficit_spectral_universal n m β E
  rw [egbFixedChargeAGibbsEntropyDeficit_identity] at h
  linarith

/-- Squared Hellinger distance to equilibrium obeys the same explicit information bound. -/
theorem egbFixedChargeAGibbsHellinger_spectral_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ (2 : ℕ) ≤
        (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) - 1) :=
  (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E).trans
    (egbFixedChargeAGibbsEntropyDeficit_spectral_universal n m β E)

end
end GaloisForLFunctions.HTGeometry
