import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationLeadingTerms

/-!
# Complete Gibbs information-rate and loss classifications

Positive quadratic comparison transfers the actual collision ratio limit to
relative entropy and squared Hellinger distance for every Gibbs landscape.
Immediately erased laws remain an explicit branch of each closed theorem.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

private theorem surviving_collision_pos (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ)
    (hz : ¬(egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0)) (m : ℕ) :
    0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E := by
  apply lt_of_le_of_ne (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E)
  intro h
  exact hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp h.symm)

private theorem observable_step_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hzero : ∀ m, (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0) → f (m + 1) = 0)
    (hpos : ∀ m, 0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E → 0 < f (m + 1))
    (hratio : Tendsto (fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a))) :
    Tendsto (fun m : ℕ => f (m + 2) / f (m + 1)) atTop
      (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · have hr : egbFixedChargeAGibbsDominantCollisionRate n β E = 0 := by
      simp [egbFixedChargeAGibbsDominantCollisionRate, hz.1, hz.2]
    rw [hr]
    have he (m : ℕ) : f (m + 2) / f (m + 1) = 0 := by
      rw [hzero (m + 1) hz, zero_div]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · simp only [if_neg hz] at hratio
    have h1 := (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) 1).mpr hratio
    have h2 := (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) 2).mpr hratio
    have hq : Tendsto (fun m =>
        (f (m + 2) / egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) /
          (f (m + 1) / egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)) atTop (nhds (a / a)) := by
      simpa only [Pi.div_def] using h2.div h1 ha.ne'
    have ht := hq.mul (egbFixedChargeAGibbsCollisionExcess_step_ratio_limit n β E)
    have he (m : ℕ) : f (m + 2) / f (m + 1) =
        ((f (m + 2) / egbFixedChargeAGibbsCollisionExcess n (m + 2) β E) /
          (f (m + 1) / egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)) *
            (egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
              egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) := by
      have hc1 := (surviving_collision_pos n β E hz m).ne'
      have hc2 := (surviving_collision_pos n β E hz (m + 1)).ne'
      have hf1 := (hpos m (surviving_collision_pos n β E hz m)).ne'
      field_simp
      <;> ring
    simp_rw [he]
    simpa only [div_self ha.ne', one_mul] using ht

private theorem observable_loss_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ)
    (hzero : ∀ m, (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0) → f (m + 1) = 0)
    (hpos : ∀ m, 0 < egbFixedChargeAGibbsCollisionExcess n (m + 1) β E → 0 < f (m + 1))
    (hstep : Tendsto (fun m : ℕ => f (m + 2) / f (m + 1)) atTop
      (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E))) :
    Tendsto (fun m : ℕ => (f (m + 1) - f (m + 2)) / f (m + 1)) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else
          1 - egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp only [if_pos hz]
    have he (m : ℕ) : (f (m + 1) - f (m + 2)) / f (m + 1) = 0 := by
      rw [hzero m hz, hzero (m + 1) hz, sub_self, zero_div]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · simp only [if_neg hz]
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have he (m : ℕ) : (f (m + 1) - f (m + 2)) / f (m + 1) = 1 - f (m + 2) / f (m + 1) := by
      have hp := (hpos m (surviving_collision_pos n β E hz m)).ne'
      rw [sub_div, div_self hp]
    simp_rw [he]
    exact hc.sub hstep

/-- The actual relative information selects the same asymptotic rate as collision excess. -/
theorem egbFixedChargeAGibbsEntropyDeficit_step_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsEntropyDeficit n (m + 2) β E /
      egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) atTop
        (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  apply observable_step_limit n β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
    ((2 : ℝ) ^ (n + 3) / 2) (by positivity)
  · intro m hz
    exact (egbFixedChargeAGibbsEntropyDeficit_two_rate_zero_iff n m β E).mpr hz
  · intro m hc
    exact (egbFixedChargeAGibbsEntropyDeficit_pos_iff_collision n (m + 1) β E).mpr hc
  · exact egbFixedChargeAGibbsEntropyDeficit_collision_ratio_limit n β E

/-- The late fractional loss of relative information is determined by the retained spectral class. -/
theorem egbFixedChargeAGibbsEntropyDeficit_loss_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => (egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E -
      egbFixedChargeAGibbsEntropyDeficit n (m + 2) β E) / egbFixedChargeAGibbsEntropyDeficit n (m + 1) β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else
          1 - egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  apply observable_loss_limit n β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
  · intro m hz
    exact (egbFixedChargeAGibbsEntropyDeficit_two_rate_zero_iff n m β E).mpr hz
  · intro m hc
    exact (egbFixedChargeAGibbsEntropyDeficit_pos_iff_collision n (m + 1) β E).mpr hc
  · exact egbFixedChargeAGibbsEntropyDeficit_step_ratio_limit n β E

/-- The actual squared Hellinger distance selects the same asymptotic rate as collision excess. -/
theorem egbFixedChargeAGibbsHellingerSquared_step_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsHellingerSquared n (m + 2) β E /
      egbFixedChargeAGibbsHellingerSquared n (m + 1) β E) atTop
        (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  apply observable_step_limit n β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    ((2 : ℝ) ^ (n + 3) / 4) (by positivity)
  · intro m hz
    exact (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n (m + 1) β E).mpr
      ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz)
  · intro m hc
    exact (egbFixedChargeAGibbsHellingerSquared_pos_iff_collision n (m + 1) β E).mpr hc
  · exact egbFixedChargeAGibbsHellingerSquared_collision_ratio_limit n β E

/-- The late fractional loss of squared Hellinger distance is determined by the retained spectral class. -/
theorem egbFixedChargeAGibbsHellingerSquared_loss_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => (egbFixedChargeAGibbsHellingerSquared n (m + 1) β E -
      egbFixedChargeAGibbsHellingerSquared n (m + 2) β E) / egbFixedChargeAGibbsHellingerSquared n (m + 1) β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else
          1 - egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  apply observable_loss_limit n β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
  · intro m hz
    exact (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n (m + 1) β E).mpr
      ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz)
  · intro m hc
    exact (egbFixedChargeAGibbsHellingerSquared_pos_iff_collision n (m + 1) β E).mpr hc
  · exact egbFixedChargeAGibbsHellingerSquared_step_ratio_limit n β E

end
end GaloisForLFunctions.HTGeometry
