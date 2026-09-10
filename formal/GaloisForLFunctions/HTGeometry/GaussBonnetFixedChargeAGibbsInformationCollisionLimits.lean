import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsInformationActivity

/-!
# Exact information-to-collision limits for every Gibbs input

The global Hellinger remainder and eventual logarithm remainder share one
analytic limit argument. Immediately erased inputs are kept explicitly;
every surviving input has the same local quadratic coefficients.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

private theorem normalized_remainder_tendsto (u q w : ℕ → ℝ) (a k : ℝ)
    (hq : ∀ m, 0 < q m) (hw : Tendsto w atTop (nhds 0))
    (hrem : ∀ᶠ m in atTop, |u m - a * q m| ≤ k * w m * q m) :
    Tendsto (fun m => u m / q m) atTop (nhds a) := by
  have hk : Tendsto (fun _ : ℕ => k) atTop (nhds k) := tendsto_const_nhds
  have hb : Tendsto (fun m => k * w m) atTop (nhds 0) := by
    simpa only [mul_zero] using hk.mul hw
  have he : ∀ᶠ m : ℕ in atTop, |u m / q m - a| ≤ k * w m := by
    filter_upwards [hrem] with m hm
    have hp := hq m
    have hi : u m / q m - a = (u m - a * q m) / q m := by
      field_simp [hp.ne']
      <;> ring
    rw [hi, abs_div, abs_of_pos hp]
    calc
      _ ≤ (k * w m * q m) / q m := div_le_div_of_nonneg_right hm hp.le
      _ = _ := by field_simp [hp.ne']
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Filter.Eventually.of_forall (fun m => abs_nonneg (u m / q m - a))) he hb

private theorem gibbs_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) (f : ℕ → ℝ) (a k : ℝ)
    (hzero : ∀ m, (egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0) → f (m + 1) = 0)
    (hrem : ∀ᶠ m : ℕ in atTop,
      |f m - a * egbFixedChargeAGibbsCollisionExcess n m β E| ≤
        k * egbFixedChargeAGibbsDisplacementSize n m β E * egbFixedChargeAGibbsCollisionExcess n m β E) :
    Tendsto (fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else a)) := by
  by_cases hz : egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0
  · simp only [if_pos hz]
    apply (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) 1).mp
    have he (m : ℕ) : f (m + 1) / egbFixedChargeAGibbsCollisionExcess n (m + 1) β E = 0 := by
      rw [hzero m hz, zero_div]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · simp only [if_neg hz]
    apply (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => f m / egbFixedChargeAGibbsCollisionExcess n m β E) 1).mp
    apply normalized_remainder_tendsto (fun m => f (m + 1))
      (fun m => egbFixedChargeAGibbsCollisionExcess n (m + 1) β E)
      (fun m => egbFixedChargeAGibbsDisplacementSize n (m + 1) β E) a k
    · intro m
      apply lt_of_le_of_ne (egbFixedChargeAGibbsCollisionExcess_nonneg n (m + 1) β E)
      intro h
      exact hz ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mp h.symm)
    · exact (Filter.tendsto_add_atTop_iff_nat
        (f := fun m => egbFixedChargeAGibbsDisplacementSize n m β E) 1).mpr
          (egbFixedChargeAGibbsDisplacementSize_limit n β E)
    · exact (Filter.tendsto_add_atTop_nat 1).eventually hrem

/-- Every surviving Gibbs input has Hellinger-to-collision coefficient one quarter of the grid size. -/
theorem egbFixedChargeAGibbsHellingerSquared_collision_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsHellingerSquared n m β E /
      egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else (2 : ℝ) ^ (n + 3) / 4)) := by
  apply gibbs_ratio_limit n β E (fun m => egbFixedChargeAGibbsHellingerSquared n m β E)
    ((2 : ℝ) ^ (n + 3) / 4) ((2 : ℝ) ^ (n + 3))
  · intro m hz
    exact (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n (m + 1) β E).mpr
      ((egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr hz)
  · exact Filter.Eventually.of_forall (fun m => egbFixedChargeAGibbsHellingerSquared_quadratic_remainder n m β E)

/-- Every surviving Gibbs input has entropy-to-collision coefficient one half of the grid size. -/
theorem egbFixedChargeAGibbsEntropyDeficit_collision_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E /
      egbFixedChargeAGibbsCollisionExcess n m β E) atTop
      (nhds (if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
        egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else (2 : ℝ) ^ (n + 3) / 2)) := by
  apply gibbs_ratio_limit n β E (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E)
    ((2 : ℝ) ^ (n + 3) / 2) (7 * (2 : ℝ) ^ (n + 3))
  · intro m hz
    exact (egbFixedChargeAGibbsEntropyDeficit_two_rate_zero_iff n m β E).mpr hz
  · exact egbFixedChargeAGibbsEntropyDeficit_eventually_quadratic_remainder n β E

end
end GaloisForLFunctions.HTGeometry
