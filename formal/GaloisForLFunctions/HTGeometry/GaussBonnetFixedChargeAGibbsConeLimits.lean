import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeFisherHistory

/-! # Exact attenuation limits realizing the whole cone at the zero collision boundary -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- Uniform canonical encoding control bounds the amplitude for every pair of prescribed masses. -/
theorem egbFixedChargeAGibbsConeAmplitude_bound (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsConeAmplitude n k m x y ≤
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k := by
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (egbFixedChargeAGibbsPerturbationScale_le_half n
      (egbFixedChargeAGibbsConeProfile n k m x y)) (by positivity : 0 ≤ (2 : ℝ) ^ (n + 3)))
    (show 0 ≤ egbFixedChargeAGibbsTunableAttenuation k by unfold egbFixedChargeAGibbsTunableAttenuation; positivity)
  change egbFixedChargeAGibbsConeAmplitude n k m x y ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 3) *
    egbFixedChargeAGibbsTunableAttenuation k at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- Every fixed cone point has a sequence of positive actual amplitudes tending to zero. -/
theorem egbFixedChargeAGibbsConeAmplitude_tendsto_zero (n m : ℕ) (x y : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsConeAmplitude n k m x y) atTop (nhds 0) := by
  have hu : Tendsto (fun k => (((2 : ℝ) ^ (n + 3))⁻¹ / 2) * egbFixedChargeAGibbsTunableAttenuation k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using egbFixedChargeAGibbsTunableAttenuation_limit.const_mul
      (((2 : ℝ) ^ (n + 3))⁻¹ / 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun k => (egbFixedChargeAGibbsConeAmplitude_pos n k m x y).le)
    (fun k => egbFixedChargeAGibbsConeAmplitude_bound n k m x y)

/-- The exact measure scaling factor tends to zero while remaining positive at every finite stage. -/
theorem egbFixedChargeAGibbsConeScale_tendsto_zero (n m : ℕ) (x y : NNReal) :
    Tendsto (fun k => (egbFixedChargeAGibbsConeScale n k m x y : ℝ)) atTop (nhds 0) := by
  change Tendsto (fun k => (4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2)
    atTop (nhds 0)
  have h := ((egbFixedChargeAGibbsConeAmplitude_tendsto_zero n m x y).pow 2).const_mul ((4 / 9 : ℝ) ^ (m + 1))
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero] using h

/-- All raw collision observations vanish along each whole-cone realization path, including the initial observation. -/
theorem egbFixedChargeAGibbsCone_collision_tendsto_zero (n m l : ℕ) (x y : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsCollisionExcess n l 1
      (egbFixedChargeAGibbsConeEnergy n k m x y)) atTop (nhds 0) := by
  have h := ((egbFixedChargeAGibbsConeAmplitude_tendsto_zero n m x y).pow 2).mul_const
    ((4 / 9 : ℝ) ^ l * x + (1 / 36 : ℝ) ^ l * (16 : ℝ) ^ (m + 1) * y)
  simpa only [egbFixedChargeAGibbsCone_collision, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul] using h

/-- Despite raw collision collapse, every prescribed source retains its exact normalized Fisher readout along the path. -/
theorem egbFixedChargeAGibbsCone_fisher_tendsto_shape (n m : ℕ) (x y : NNReal) :
    Tendsto (fun k => egbFixedChargeAGibbsCollisionFisherValue n m 1
      (egbFixedChargeAGibbsConeEnergy n k m x y)) atTop
      (nhds (egbFixedChargeAGibbsCollisionFisherShape x y)) := by
  simp only [egbFixedChargeAGibbsCone_fisher_formula]
  exact tendsto_const_nhds

end
end GaloisForLFunctions.HTGeometry
