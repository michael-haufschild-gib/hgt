import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionGeneratingSeries

/-!
# Exact leading amplitudes at the input-selected decay rate

Normalizing by the actual surviving rate retains the fast-sector amplitude
when the slow energy vanishes. Equilibrated inputs have zero amplitude.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- Collision normalized by its actual surviving rate tends to the corresponding mode energy. -/
theorem egbFixedChargeAGibbsCollisionExcess_dominant_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n m β E /
      egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) atTop
        (nhds (egbFixedChargeAGibbsDominantModeEnergy n β E)) := by
  unfold egbFixedChargeAGibbsDominantModeEnergy
  split_ifs with ha
  · apply (Filter.tendsto_add_atTop_iff_nat (f := fun m : ℕ =>
      egbFixedChargeAGibbsCollisionExcess n m β E /
        egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) 1).mp
    by_cases hb : egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · simpa [egbFixedChargeAGibbsDominantCollisionRate, ha, hb] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    · have he (m : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E /
          egbFixedChargeAGibbsDominantCollisionRate n β E ^ (m + 1) =
            egbFixedChargeAGibbsFastModeEnergy n β E := by
        have hr : egbFixedChargeAGibbsDominantCollisionRate n β E = (1 / 36 : ℝ) := by
          simp [egbFixedChargeAGibbsDominantCollisionRate, ha, hb]
        rw [hr, egbFixedChargeAGibbsCollisionExcess_two_rate, ha]
        simp only [mul_zero, zero_add]
        have hp : (1 / 36 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
      simpa only [he] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => egbFixedChargeAGibbsFastModeEnergy n β E) atTop
          (nhds (egbFixedChargeAGibbsFastModeEnergy n β E)))
  · simpa only [egbFixedChargeAGibbsDominantCollisionRate, if_neg ha,
      egbFixedChargeAGibbsNormalizedCollision] using egbFixedChargeAGibbsNormalizedCollision_limit n β E

private theorem observable_dominant_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ) (a : ℝ)
    (hzero : ∀ m, egbFixedChargeAGibbsCollisionExcess n m β E = 0 → f m = 0)
    (hratio : Tendsto (fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a))) :
    Tendsto (fun m => f m / egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) atTop
      (nhds (a * egbFixedChargeAGibbsDominantModeEnergy n β E)) := by
  have h := hratio.mul (egbFixedChargeAGibbsCollisionExcess_dominant_prefactor_limit n β E)
  have he (m : ℕ) : f m / egbFixedChargeAGibbsDominantCollisionRate n β E ^ m =
      (f m / egbFixedChargeAGibbsCollisionExcess n m β E) *
        (egbFixedChargeAGibbsCollisionExcess n m β E /
          egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) := by
    by_cases hc : egbFixedChargeAGibbsCollisionExcess n m β E = 0
    · simp only [hzero m hc, hc, zero_div, zero_mul]
    · field_simp [hc]
  have hv : (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a) *
        egbFixedChargeAGibbsDominantModeEnergy n β E = a * egbFixedChargeAGibbsDominantModeEnergy n β E := by
    by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · simp [egbFixedChargeAGibbsDominantModeEnergy, hz.1, hz.2]
    · simp only [if_neg hz]
  simp_rw [he]
  simpa only [hv] using h

/-- Entropy has a nonzero leading amplitude in whichever nonconstant spectral sector survives. -/
theorem egbFixedChargeAGibbsEntropyDeficit_dominant_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E /
      egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) atTop
        (nhds (((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsDominantModeEnergy n β E)) := by
  apply observable_dominant_prefactor_limit n β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
    ((2 : ℝ) ^ (n + 3) / 2)
  · intro m hc
    exact (egbFixedChargeAGibbsEntropyDeficit_zero_iff_uniform n m β E).mpr
      ((egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform n m β E).mp hc)
  · exact egbFixedChargeAGibbsEntropyDeficit_collision_ratio_limit n β E

/-- Squared Hellinger distance has one quarter of grid size times the surviving mode energy as its amplitude. -/
theorem egbFixedChargeAGibbsHellingerSquared_dominant_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsHellingerSquared n m β E /
      egbFixedChargeAGibbsDominantCollisionRate n β E ^ m) atTop
        (nhds (((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsDominantModeEnergy n β E)) := by
  apply observable_dominant_prefactor_limit n β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    ((2 : ℝ) ^ (n + 3) / 4)
  · intro m hc
    exact (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n m β E).mpr hc
  · exact egbFixedChargeAGibbsHellingerSquared_collision_ratio_limit n β E

end
end GaloisForLFunctions.HTGeometry
