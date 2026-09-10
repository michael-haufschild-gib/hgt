import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationCollisionLimits

/-!
# General Gibbs information prefactors and the entropy/Hellinger ratio

The common quadratic coefficients apply to every surviving Gibbs input.
Combining them with the exact collision prefactor identifies the leading
information amplitudes, including inputs with no slow Fourier component.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

private theorem observable_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ) (a : ℝ)
    (hzero : ∀ m, egbFixedChargeAGibbsCollisionExcess n m β E = 0 → f m = 0)
    (hratio : Tendsto (fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a))) :
    Tendsto (fun m => f m / (4 / 9 : ℝ) ^ m) atTop
      (nhds (a * egbFixedChargeAGibbsSlowModeEnergy n β E)) := by
  have h := hratio.mul (egbFixedChargeAGibbsNormalizedCollision_limit n β E)
  have he (m : ℕ) : f m / (4 / 9 : ℝ) ^ m =
      (f m / egbFixedChargeAGibbsCollisionExcess n m β E) *
        egbFixedChargeAGibbsNormalizedCollision n m β E := by
    unfold egbFixedChargeAGibbsNormalizedCollision
    by_cases hc : egbFixedChargeAGibbsCollisionExcess n m β E = 0
    · simp only [hzero m hc, hc, zero_div, zero_mul]
    · field_simp [hc]
  have hv : (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a) *
        egbFixedChargeAGibbsSlowModeEnergy n β E = a * egbFixedChargeAGibbsSlowModeEnergy n β E := by
    by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0
    · simp only [if_pos hz, hz.1, mul_zero]
    · simp only [if_neg hz]
  simp_rw [he]
  simpa only [hv] using h

/-- The entropy prefactor is half the grid size times the actual initial slow spectral energy. -/
theorem egbFixedChargeAGibbsEntropyDeficit_spectral_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E / (4 / 9 : ℝ) ^ m) atTop
      (nhds (((2 : ℝ) ^ (n + 3) / 2) * egbFixedChargeAGibbsSlowModeEnergy n β E)) := by
  apply observable_prefactor_limit n β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
    ((2 : ℝ) ^ (n + 3) / 2)
  · intro m hc
    exact (egbFixedChargeAGibbsEntropyDeficit_zero_iff_uniform n m β E).mpr
      ((egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform n m β E).mp hc)
  · exact egbFixedChargeAGibbsEntropyDeficit_collision_ratio_limit n β E

/-- The squared Hellinger prefactor is one quarter of the grid size times the slow spectral energy. -/
theorem egbFixedChargeAGibbsHellingerSquared_spectral_prefactor_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsHellingerSquared n m β E / (4 / 9 : ℝ) ^ m) atTop
      (nhds (((2 : ℝ) ^ (n + 3) / 4) * egbFixedChargeAGibbsSlowModeEnergy n β E)) := by
  apply observable_prefactor_limit n β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    ((2 : ℝ) ^ (n + 3) / 4)
  · intro m hc
    exact (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n m β E).mpr hc
  · exact egbFixedChargeAGibbsHellingerSquared_collision_ratio_limit n β E

/-- Every surviving Gibbs input has entropy asymptotically twice squared Hellinger distance. -/
theorem egbFixedChargeAGibbsEntropyDeficit_hellinger_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E /
      egbFixedChargeAGibbsHellingerSquared n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else (2 : ℝ))) := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp only [if_pos hz]
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun m =>
      egbFixedChargeAGibbsEntropyDeficit n m β E / egbFixedChargeAGibbsHellingerSquared n m β E) 1).mp
    have he (m : ℕ) : egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E /
        egbFixedChargeAGibbsHellingerSquared n (m + 1) β E = 0 := by
      rw [(egbFixedChargeAGibbsEntropyDeficit_two_rate_zero_iff n m β E).mpr hz, zero_div]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · simp only [if_neg hz]
    have hd := egbFixedChargeAGibbsEntropyDeficit_collision_ratio_limit n β E
    have hh := egbFixedChargeAGibbsHellingerSquared_collision_ratio_limit n β E
    simp only [if_neg hz] at hd hh
    have ha : ((2 : ℝ) ^ (n + 3) / 4) ≠ 0 := by positivity
    have ht : Tendsto (fun m =>
        (egbFixedChargeAGibbsEntropyDeficit n m β E / egbFixedChargeAGibbsCollisionExcess n m β E) /
          (egbFixedChargeAGibbsHellingerSquared n m β E / egbFixedChargeAGibbsCollisionExcess n m β E))
        atTop (nhds (((2 : ℝ) ^ (n + 3) / 2) / ((2 : ℝ) ^ (n + 3) / 4))) := by
      simpa only [Pi.div_def] using hd.div hh ha
    have he (m : ℕ) : egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E /
        egbFixedChargeAGibbsHellingerSquared n (m + 1) β E =
        (egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E / egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) /
          (egbFixedChargeAGibbsHellingerSquared n (m + 1) β E / egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) := by
      have hc : 0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
        apply lt_of_le_of_ne (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E)
        intro h
        exact hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp h.symm)
      have hc0 := hc.ne'
      have hh0 := ((egbFixedChargeAGibbsHellingerSquared_pos_iff_collision n (m + 1) β E).mpr hc).ne'
      field_simp
    have hv : ((2 : ℝ) ^ (n + 3) / 2) / ((2 : ℝ) ^ (n + 3) / 4) = 2 := by
      have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      norm_num
    apply (Filter.tendsto_add_atTop_iff_nat (f := fun m =>
      egbFixedChargeAGibbsEntropyDeficit n m β E / egbFixedChargeAGibbsHellingerSquared n m β E) 1).mp
    simp_rw [he]
    have hs := (Filter.tendsto_add_atTop_iff_nat (f := fun m =>
      (egbFixedChargeAGibbsEntropyDeficit n m β E / egbFixedChargeAGibbsCollisionExcess n m β E) /
        (egbFixedChargeAGibbsHellingerSquared n m β E / egbFixedChargeAGibbsCollisionExcess n m β E)) 1).mpr ht
    simpa only [hv] using hs

end
end GaloisForLFunctions.HTGeometry
