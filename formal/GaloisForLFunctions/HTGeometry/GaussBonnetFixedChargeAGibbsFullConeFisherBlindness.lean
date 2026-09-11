import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeObservability
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeFisherHistory

/-! # Exact erased-sector blindness and its full-support Gibbs witnesses -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem shape_scale (c a b : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    egbFixedChargeAGibbsCollisionFisherShape (c * a) (c * b) =
      egbFixedChargeAGibbsCollisionFisherShape a b := by
  by_cases h : a + b = 0
  · have haz : a = 0 := by linarith
    have hbz : b = 0 := by linarith
    simp [haz, hbz, egbFixedChargeAGibbsCollisionFisherShape]
  · have hs : c * a + c * b ≠ 0 := by
      rw [← mul_add]
      exact mul_ne_zero hc.ne' h
    unfold egbFixedChargeAGibbsCollisionFisherShape
    field_simp
    <;> ring

/-- The complete actual Fisher history sees only the slow and fast prescribed masses. -/
theorem egbFixedChargeAGibbsFullCone_fisher_history (n k m : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsCollisionFisherShape ((4 / 9 : ℝ) ^ (m + 1) * A) ((1 / 36 : ℝ) ^ (m + 1) * B) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass]
  change egbFixedChargeAGibbsCollisionFisherShape
    ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B))
    ((1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)) = _
  rw [egbFixedChargeAGibbsFullCone_slow_energy, egbFixedChargeAGibbsFullCone_fast_energy]
  calc
    _ = egbFixedChargeAGibbsCollisionFisherShape
      (egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * ((4 / 9 : ℝ) ^ (m + 1) * A))
      (egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * ((1 / 36 : ℝ) ^ (m + 1) * B)) := by
        congr 1 <;> ring
    _ = _ := shape_scale _ _ _ (egbFixedChargeAGibbsFullConeScale_pos n k R A B) (by positivity) (by positivity)

/-- Changing the erased mass or attenuation leaves every Fisher observation unchanged. -/
theorem egbFixedChargeAGibbsFullCone_fisher_erased_independent (n k l m : ℕ) (R T A B : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsFullConeEnergy n l T A B) := by
  rw [egbFixedChargeAGibbsFullCone_fisher_history, egbFixedChargeAGibbsFullCone_fisher_history]

/-- Fisher vanishes precisely on the two coordinate faces where a surviving mass is absent. -/
theorem egbFixedChargeAGibbsFullCone_fisher_zero_iff (n k m : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) = 0 ↔
      A = 0 ∨ B = 0 := by
  have h := egbFixedChargeAGibbsCollisionFisherValue_zero_iff n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)
  rw [egbFixedChargeAGibbsFullCone_slow_energy, egbFixedChargeAGibbsFullCone_fast_energy] at h
  have ha : egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 ≠ 0 :=
    (egbFixedChargeAGibbsFullConeScale_pos n k R A B).ne'
  simpa [ha] using h

/-- Two actual full-support Gibbs laws have identical raw positive histories but distinct initial collision energies. -/
theorem egbFixedChargeAGibbsFullCone_erased_blind_witness (n k : ℕ) :
    (∀ m : ℕ, egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsFullConeEnergy n k 1 0 0) =
      egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsFullConeEnergy n k 0 0 0)) ∧
    egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsFullConeEnergy n k 1 0 0) ≠
      egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsFullConeEnergy n k 0 0 0) := by
  constructor
  · intro m
    simp [egbFixedChargeAGibbsFullCone_collision]
  · have h := egbFixedChargeAGibbsFullConeScale_pos n k 1 0 0
    change 0 < egbFixedChargeAGibbsFullConeAmplitude n k 1 0 0 ^ 2 at h
    simpa [egbFixedChargeAGibbsFullCone_collision] using h.ne'

/-- No decoder of raw positive-time collisions recovers the initial collision value for every full-support realization. -/
theorem egbFixedChargeAGibbsFullCone_no_positive_history_decoder (n k : ℕ) :
    ¬ ∃ D : (ℕ → ℝ) → ℝ, ∀ R A B : NNReal,
      D (fun m => egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B)) =
        egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) := by
  rintro ⟨D, hD⟩
  have h := egbFixedChargeAGibbsFullCone_erased_blind_witness n k
  have he := congrArg D (funext h.1)
  rw [hD 1 0 0, hD 0 0 0] at he
  exact h.2 he

end
end GaloisForLFunctions.HTGeometry
