import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMixedModes
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPerturbationDynamics
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsSpikeDimensionalLimits

/-! # Actual Gibbs states with arbitrary retained-mode ratio -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter

/-- A strictly positive attenuation with an already verified geometric zero limit. -/
def egbFixedChargeAGibbsTunableAttenuation (k : ℕ) : ℝ := ((2 : ℝ) ^ (k + 3))⁻¹

/-- Compensation for the different rates makes the observation-time mass ratio equal to t squared. -/
def egbFixedChargeAGibbsTunableProfile (n k m : ℕ) (t : ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeACriticalMixedProfile n (egbFixedChargeAGibbsTunableAttenuation k)
    (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1) * t)

/-- An explicit real energy landscape for each attenuation, offset, and signed mode ratio. -/
def egbFixedChargeAGibbsTunableEnergy (n k m : ℕ) (t : ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeAGibbsPerturbationEnergy n (egbFixedChargeAGibbsTunableProfile n k m t)

/-- Common positive amplitude of the two collision sectors. -/
def egbFixedChargeAGibbsTunableAmplitude (n k m : ℕ) (t : ℝ) : ℝ :=
  egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeAGibbsTunableProfile n k m t) /
    (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k

/-- Every attenuated state retains a strictly positive common spectral amplitude. -/
theorem egbFixedChargeAGibbsTunableAmplitude_pos (n k m : ℕ) (t : ℝ) :
    0 < egbFixedChargeAGibbsTunableAmplitude n k m t := by
  exact mul_pos (div_pos (egbFixedChargeAGibbsPerturbationScale_pos n _)
    (pow_pos (by norm_num) _)) (inv_pos.mpr (pow_pos (by norm_num) _))

/-- The tunable state is exactly the existing strictly positive perturbation probability. -/
theorem egbFixedChargeAGibbsTunable_realization (n k m : ℕ) (t : ℝ) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsPerturbationProbability n (egbFixedChargeAGibbsTunableProfile n k m t) := by
  exact egbFixedChargeAGibbsPerturbation_realization n _

/-- Every member of the tunable family has full support, including the pure slow endpoint. -/
theorem egbFixedChargeAGibbsTunable_probability_pos (n k m : ℕ) (t : ℝ) (i : Fin (2 ^ (n + 3))) :
    0 < _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsTunableEnergy n k m t) i := by
  rw [egbFixedChargeAGibbsTunable_realization]
  exact egbFixedChargeAGibbsPerturbationProbability_pos n _ i

/-- The complete collision history is an exact two-rate expression with a common positive amplitude. -/
theorem egbFixedChargeAGibbsTunable_collision (n k m l : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsCollisionExcess n l 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableAmplitude n k m t ^ 2 *
        ((4 / 9 : ℝ) ^ l + (1 / 36 : ℝ) ^ l * (16 : ℝ) ^ (m + 1) * t ^ 2) := by
  unfold egbFixedChargeAGibbsTunableEnergy
  rw [egbFixedChargeAGibbsPerturbation_collision_identity]
  unfold egbFixedChargeAGibbsTunableProfile
  rw [egbFixedChargeACriticalMixedProfile_evolved_energy]
  have hp : ((4 : ℝ) ^ (m + 1)) ^ 2 = (16 : ℝ) ^ (m + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  change _ = (egbFixedChargeAGibbsPerturbationScale n
    (egbFixedChargeACriticalMixedProfile n (egbFixedChargeAGibbsTunableAttenuation k)
      (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1) * t)) /
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k) ^ 2 * _
  rw [mul_pow (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1)) t 2,
    mul_pow (egbFixedChargeAGibbsTunableAttenuation k) ((4 : ℝ) ^ (m + 1)) 2, hp]
  ring

/-- The attenuation tends to zero while remaining positive at every finite stage. -/
theorem egbFixedChargeAGibbsTunableAttenuation_limit :
    Tendsto egbFixedChargeAGibbsTunableAttenuation atTop (nhds 0) :=
  egbFixedChargeAGibbsSpike_inverse_grid_tendsto_zero

end
end GaloisForLFunctions.HTGeometry
