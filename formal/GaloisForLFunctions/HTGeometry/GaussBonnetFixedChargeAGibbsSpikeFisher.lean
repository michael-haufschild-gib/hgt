import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeSpectralEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionFisherStepSigns

/-!
# Dimension-independent Fisher geometry of the spike Gibbs family

The surviving collision mass shrinks with grid size, but its normalized Fisher
shape is identical on every grid and strictly decreases from its initial peak.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem spike_mass_ratio (n m : ℕ) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n m 1 (egbFixedChargeAGibbsSpikeEnergy n) : ℝ) =
      (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1 (egbFixedChargeAGibbsSpikeEnergy n) : ℝ) *
        (1 / 16 : ℝ) ^ (m + 1) := by
  change (1 / 36 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n) =
    ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n)) *
      (1 / 16 : ℝ) ^ (m + 1)
  rw [egbFixedChargeAGibbsSpike_slow_energy, egbFixedChargeAGibbsSpike_fast_energy,
    show (1 / 36 : ℝ) = (4 / 9 : ℝ) * (1 / 16 : ℝ) by norm_num, mul_pow]
  ring

private theorem spike_slow_mass_pos (n m : ℕ) :
    0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1 (egbFixedChargeAGibbsSpikeEnergy n) : ℝ) := by
  change 0 < (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsSpikeEnergy n)
  exact mul_pos (pow_pos (by norm_num) _) (egbFixedChargeAGibbsSpike_three_energies_pos n).2.1

private theorem fisher_shape_scale (x q : ℝ) (hx : 0 < x) (hq : 0 < q) :
    egbFixedChargeAGibbsCollisionFisherShape x (x * q) =
      (25 / 36 : ℝ) * q / (1 + q) ^ (2 : ℕ) := by
  have hsum : x + x * q ≠ 0 := (show 0 < x + x * q by positivity).ne'
  have hq1 : 1 + q ≠ 0 := (show 0 < 1 + q by positivity).ne'
  unfold egbFixedChargeAGibbsCollisionFisherShape
  field_simp [hsum, hq1, hx.ne']
  <;> ring

/-- Every grid has exactly the same normalized collision Fisher curve. -/
theorem egbFixedChargeAGibbsSpike_fisher_formula (n m : ℕ) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      (25 / 36 : ℝ) * (1 / 16 : ℝ) ^ (m + 1) / (1 + (1 / 16 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  rw [egbFixedChargeAGibbsCollisionFisherValue_two_mass, spike_mass_ratio]
  exact fisher_shape_scale _ _ (spike_slow_mass_pos n m) (pow_pos (by norm_num) _)

/-- Changing the grid dimension leaves the entire normalized Fisher history unchanged. -/
theorem egbFixedChargeAGibbsSpike_fisher_dimension_invariant (n l m : ℕ) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n) =
      egbFixedChargeAGibbsCollisionFisherValue l m 1 (egbFixedChargeAGibbsSpikeEnergy l) := by
  rw [egbFixedChargeAGibbsSpike_fisher_formula, egbFixedChargeAGibbsSpike_fisher_formula]

/-- The initial normalized Fisher value is the exact rational one hundred over two thousand six hundred one. -/
theorem egbFixedChargeAGibbsSpike_fisher_initial (n : ℕ) :
    egbFixedChargeAGibbsCollisionFisherValue n 0 1 (egbFixedChargeAGibbsSpikeEnergy n) = (100 / 2601 : ℝ) := by
  rw [egbFixedChargeAGibbsSpike_fisher_formula]
  norm_num

/-- The Fisher history of this three-sector Gibbs witness strictly decreases from the first observation onward. -/
theorem egbFixedChargeAGibbsSpike_fisher_strictAnti (n : ℕ) :
    StrictAnti (fun m : ℕ => egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n)) := by
  apply strictAnti_nat_of_succ_lt
  intro m
  apply (egbFixedChargeAGibbsCollisionFisherValue_decrease_iff n m 1 (egbFixedChargeAGibbsSpikeEnergy n)).mpr
  have h := egbFixedChargeAGibbsSpike_three_energies_pos n
  refine ⟨h.2.1, h.2.2, ?_⟩
  rw [spike_mass_ratio]
  have hx := spike_slow_mass_pos n m
  have hq : (1 / 16 : ℝ) ^ (m + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    _ ≤ (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1 (egbFixedChargeAGibbsSpikeEnergy n) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hq hx.le
    _ < _ := by linarith

/-- The initial Fisher value is the unique global peak on every grid. -/
theorem egbFixedChargeAGibbsSpike_fisher_peak (n m : ℕ) :
    egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n) ≤ (100 / 2601 : ℝ) ∧
      (egbFixedChargeAGibbsCollisionFisherValue n m 1 (egbFixedChargeAGibbsSpikeEnergy n) = (100 / 2601 : ℝ) ↔ m = 0) := by
  cases m with
  | zero => rw [egbFixedChargeAGibbsSpike_fisher_initial]; simp
  | succ m =>
      have h := egbFixedChargeAGibbsSpike_fisher_strictAnti n (show 0 < m + 1 by omega)
      change egbFixedChargeAGibbsCollisionFisherValue n (m + 1) 1 (egbFixedChargeAGibbsSpikeEnergy n) <
        egbFixedChargeAGibbsCollisionFisherValue n 0 1 (egbFixedChargeAGibbsSpikeEnergy n) at h
      rw [egbFixedChargeAGibbsSpike_fisher_initial] at h
      refine ⟨h.le, ?_⟩
      constructor
      · intro he
        linarith
      · intro he
        omega

end
end GaloisForLFunctions.HTGeometry
