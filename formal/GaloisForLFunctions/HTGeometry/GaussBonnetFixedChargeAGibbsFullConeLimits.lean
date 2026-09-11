import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeSource

/-! # Exact attenuation limits realizing the whole cone at the zero collision boundary -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- Uniform canonical encoding control bounds the amplitude for every triple of prescribed masses. -/
theorem egbFixedChargeAGibbsFullConeAmplitude_bound (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFullConeAmplitude n k R A B ≤
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k := by
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (egbFixedChargeAGibbsPerturbationScale_le_half n
      (egbFixedChargeAGibbsFullConeProfile n k R A B)) (by positivity : 0 ≤ (2 : ℝ) ^ (n + 3)))
    (show 0 ≤ egbFixedChargeAGibbsTunableAttenuation k by unfold egbFixedChargeAGibbsTunableAttenuation; positivity)
  change egbFixedChargeAGibbsFullConeAmplitude n k R A B ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) *
    egbFixedChargeAGibbsTunableAttenuation k at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- Every fixed cone point has a sequence of positive actual amplitudes tending to zero. -/
theorem egbFixedChargeAGibbsFullConeAmplitude_tendsto_zero (n : ℕ) (R A B : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsFullConeAmplitude n k R A B) atTop (nhds 0) := by
  have hu : Tendsto (fun k => (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using egbFixedChargeAGibbsTunableAttenuation_limit.const_mul
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun k => (egbFixedChargeAGibbsFullConeAmplitude_pos n k R A B).le)
    (fun k => egbFixedChargeAGibbsFullConeAmplitude_bound n k R A B)

/-- The exact measure scaling factor tends to zero while remaining positive at every finite stage. -/
theorem egbFixedChargeAGibbsFullConeScale_tendsto_zero (n : ℕ) (R A B : NNReal) :
    Tendsto (fun k => (egbFixedChargeAGibbsFullConeScale n k R A B : ℝ)) atTop (nhds 0) := by
  change Tendsto (fun k => egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2) atTop (nhds 0)
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0)] using
    (egbFixedChargeAGibbsFullConeAmplitude_tendsto_zero n R A B).pow 2

/-- All raw collision observations vanish along each whole-cone realization path, including the initial observation. -/
theorem egbFixedChargeAGibbsFullCone_collision_tendsto_zero (n l : ℕ) (R A B : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsCollisionExcess n l 1
      (egbFixedChargeAGibbsFullConeEnergy n k R A B)) atTop (nhds 0) := by
  have h := ((egbFixedChargeAGibbsFullConeAmplitude_tendsto_zero n R A B).pow 2).mul_const
    ((0 : ℝ) ^ l * R + (4 / 9 : ℝ) ^ l * A + (1 / 36 : ℝ) ^ l * B)
  simpa only [egbFixedChargeAGibbsFullCone_collision, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul] using h


end
end GaloisForLFunctions.HTGeometry
