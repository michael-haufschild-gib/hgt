import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFisher

/-! # Fixed-grid Gibbs collision inputs vanish while their normalized geometry persists -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- The canonical positive Gibbs encoding never amplifies a centered profile by more than one half. -/
theorem egbFixedChargeAGibbsPerturbationScale_le_half (n : ℕ) (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsPerturbationScale n f ≤ (1 / 2 : ℝ) := by
  have hs : 0 ≤ ∑ i, |egbFixedChargeACriticalCenteredProfile n f i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 2 * (1 + ∑ i, |egbFixedChargeACriticalCenteredProfile n f i|) by linarith)
  simpa only [egbFixedChargeAGibbsPerturbationScale, one_div] using h

/-- The complete tunable collision amplitude has an explicit attenuation bound independent of the ratio parameter. -/
theorem egbFixedChargeAGibbsTunableAmplitude_bound (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsTunableAmplitude n k m t ≤
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k := by
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (egbFixedChargeAGibbsPerturbationScale_le_half n
      (egbFixedChargeAGibbsTunableProfile n k m t)) (by positivity : 0 ≤ (2 : ℝ) ^ (n + 3)))
    (show 0 ≤ egbFixedChargeAGibbsTunableAttenuation k by unfold egbFixedChargeAGibbsTunableAttenuation; positivity)
  change egbFixedChargeAGibbsTunableAmplitude n k m t ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) *
    egbFixedChargeAGibbsTunableAttenuation k at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- For every fixed grid and ratio, the common positive collision amplitude tends to zero. -/
theorem egbFixedChargeAGibbsTunableAmplitude_tendsto_zero (n m : ℕ) (t : ℝ) :
    Tendsto (fun k => egbFixedChargeAGibbsTunableAmplitude n k m t) atTop (nhds 0) := by
  have hu : Tendsto (fun k => (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using egbFixedChargeAGibbsTunableAttenuation_limit.const_mul
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun k => (egbFixedChargeAGibbsTunableAmplitude_pos n k m t).le)
    (fun k => egbFixedChargeAGibbsTunableAmplitude_bound n k m t)

/-- Every observation, including time zero, vanishes along each actual Gibbs attenuation path. -/
theorem egbFixedChargeAGibbsTunable_collision_tendsto_zero (n m l : ℕ) (t : ℝ) :
    Tendsto (fun k => egbFixedChargeAGibbsCollisionExcess n l 1
      (egbFixedChargeAGibbsTunableEnergy n k m t)) atTop (nhds 0) := by
  have h := ((egbFixedChargeAGibbsTunableAmplitude_tendsto_zero n m t).pow 2).mul_const
    ((4 / 9 : ℝ) ^ l + (1 / 36 : ℝ) ^ l * (16 : ℝ) ^ (m + 1) * t ^ (2 : ℕ))
  simpa only [egbFixedChargeAGibbsTunable_collision, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul] using h

/-- The actual three observations used by Fisher normalization approach the origin jointly. -/
theorem egbFixedChargeAGibbsTunable_fisher_inputs_tendsto_zero (n m : ℕ) (t : ℝ) :
    Tendsto (fun k =>
      (egbFixedChargeAGibbsCollisionExcess n (m + 1) 1 (egbFixedChargeAGibbsTunableEnergy n k m t),
       egbFixedChargeAGibbsCollisionExcess n (m + 2) 1 (egbFixedChargeAGibbsTunableEnergy n k m t),
       egbFixedChargeAGibbsCollisionExcess n (m + 3) 1 (egbFixedChargeAGibbsTunableEnergy n k m t)))
      atTop (nhds (0, 0, 0)) := by
  exact (egbFixedChargeAGibbsTunable_collision_tendsto_zero n m (m + 1) t).prodMk_nhds
    ((egbFixedChargeAGibbsTunable_collision_tendsto_zero n m (m + 2) t).prodMk_nhds
      (egbFixedChargeAGibbsTunable_collision_tendsto_zero n m (m + 3) t))

/-- Attenuation leaves the normalized Fisher value exactly constant along the entire path. -/
theorem egbFixedChargeAGibbsTunable_fisher_tendsto_curve (n m : ℕ) (t : ℝ) :
    Tendsto (fun k => egbFixedChargeAGibbsCollisionFisherValue n m 1
      (egbFixedChargeAGibbsTunableEnergy n k m t)) atTop (nhds (egbFixedChargeAGibbsTunableFisherCurve t)) := by
  simpa only [egbFixedChargeAGibbsTunable_fisher_formula] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => egbFixedChargeAGibbsTunableFisherCurve t) atTop (nhds _))

end
end GaloisForLFunctions.HTGeometry
