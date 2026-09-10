import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationLower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The slow Gibbs law has matching geometric upper and lower bounds for relative information. -/
theorem egbFixedChargeAGibbsSlow_information_bounds (n m : ℕ) :
    (4 / 9 : ℝ) ^ m * (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) / 4) ≤
      egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) ∧
    egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) ≤
      (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) *
        egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) := by
  constructor
  · have h := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m 1 (egbFixedChargeAGibbsSlowEnergy n)
    rw [egbFixedChargeAGibbsSlow_collision_exact] at h
    nlinarith
  · exact egbFixedChargeAGibbsEntropyDeficit_spectral_bound n m 1 _

/-- The same spectral base bounds squared Hellinger distance above and below. -/
theorem egbFixedChargeAGibbsSlow_hellinger_bounds (n m : ℕ) :
    (4 / 9 : ℝ) ^ m * (egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n) / 4) ≤
      finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 ∧
    finitePacketHellinger (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 ≤
      (4 / 9 : ℝ) ^ m * ((2 : ℝ) ^ (n + 3) *
        egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsSlowEnergy n)) := by
  constructor
  · have h := egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m 1 (egbFixedChargeAGibbsSlowEnergy n)
    rw [egbFixedChargeAGibbsSlow_collision_exact] at h
    nlinarith
  · exact (egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m 1 _).trans
      (egbFixedChargeAGibbsSlow_information_bounds n m).2

/-- Positive relative information survives at every finite time in the slow Gibbs state. -/
theorem egbFixedChargeAGibbsSlow_information_pos (n m : ℕ) :
    0 < egbFixedChargeAGibbsEntropyDeficit n m 1 (egbFixedChargeAGibbsSlowEnergy n) := by
  have h := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m 1 (egbFixedChargeAGibbsSlowEnergy n)
  linarith [egbFixedChargeAGibbsSlow_collision_pos n m]

/-- The slow Gibbs entropy stays strictly below its capacity at every finite time. -/
theorem egbFixedChargeAGibbsSlow_entropy_strict (n m : ℕ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n)) <
      (n + 3 : ℝ) * Real.log 2 := by
  have h := egbFixedChargeAGibbsSlow_information_pos n m
  rw [egbFixedChargeAGibbsEntropyDeficit_identity] at h
  linarith

/-- Squared distinguishability remains positive for every finite transition count. -/
theorem egbFixedChargeAGibbsSlow_hellinger_sq_pos (n m : ℕ) :
    0 < finitePacketHellinger
      (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsSlowEnergy n))
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) ^ 2 := by
  have h := egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m 1 (egbFixedChargeAGibbsSlowEnergy n)
  linarith [egbFixedChargeAGibbsSlow_collision_pos n m]

end
end GaloisForLFunctions.HTGeometry
