import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableLimits

/-! # Full-support Gibbs realizations of the entire positive collision-source cone
The two rates come from the critical Gauss--Bonnet kernel. Independent square-root
mode coefficients prescribe both source masses, including either pure endpoint. -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Independent nonnegative masses determine an exact real two-mode profile. -/
def egbFixedChargeAGibbsConeProfile (n k m : ℕ) (x y : NNReal) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeACriticalMixedProfile n
    (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt x)
    (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1) * Real.sqrt y)

/-- Canonical real Gibbs energies for every point of the nonnegative mass cone. -/
def egbFixedChargeAGibbsConeEnergy (n k m : ℕ) (x y : NNReal) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeAGibbsPerturbationEnergy n (egbFixedChargeAGibbsConeProfile n k m x y)

/-- The common positive amplitude is independent of which source sectors vanish. -/
def egbFixedChargeAGibbsConeAmplitude (n k m : ℕ) (x y : NNReal) : ℝ :=
  egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeAGibbsConeProfile n k m x y) /
    (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k

/-- The common amplitude stays positive even at either pure ray and the cone vertex. -/
theorem egbFixedChargeAGibbsConeAmplitude_pos (n k m : ℕ) (x y : NNReal) :
    0 < egbFixedChargeAGibbsConeAmplitude n k m x y := by
  exact mul_pos (div_pos (egbFixedChargeAGibbsPerturbationScale_pos n _)
    (pow_pos (by norm_num) _)) (inv_pos.mpr (pow_pos (by norm_num) _))

/-- This scalar converts each prescribed source mass into its actual observed Gibbs mass. -/
def egbFixedChargeAGibbsConeScale (n k m : ℕ) (x y : NNReal) : NNReal :=
  ⟨(4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2,
    mul_nonneg (by positivity) (sq_nonneg _)⟩

/-- Exact source normalization never requires division by a vanishing scalar. -/
theorem egbFixedChargeAGibbsConeScale_pos (n k m : ℕ) (x y : NNReal) :
    0 < (egbFixedChargeAGibbsConeScale n k m x y : ℝ) := by
  exact mul_pos (pow_pos (by norm_num) _) (sq_pos_of_pos (egbFixedChargeAGibbsConeAmplitude_pos n k m x y))

/-- The canonical energy realizes the existing positive perturbation probability exactly. -/
theorem egbFixedChargeAGibbsCone_realization (n k m : ℕ) (x y : NNReal) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsPerturbationProbability n (egbFixedChargeAGibbsConeProfile n k m x y) :=
  egbFixedChargeAGibbsPerturbation_realization n _

/-- Every cone point is realized by a full-support Gibbs law, including zero and both pure rays. -/
theorem egbFixedChargeAGibbsCone_probability_pos (n k m : ℕ) (x y : NNReal)
    (i : Fin (2 ^ (n + 3))) :
    0 < _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsConeEnergy n k m x y) i := by
  rw [egbFixedChargeAGibbsCone_realization]
  exact egbFixedChargeAGibbsPerturbationProbability_pos n _ i

/-- Independent source masses appear linearly in the complete actual collision history. -/
theorem egbFixedChargeAGibbsCone_collision (n k m l : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionExcess n l 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 *
        ((4 / 9 : ℝ) ^ l * x + (1 / 36 : ℝ) ^ l * (16 : ℝ) ^ (m + 1) * y) := by
  unfold egbFixedChargeAGibbsConeEnergy
  rw [egbFixedChargeAGibbsPerturbation_collision_identity]
  unfold egbFixedChargeAGibbsConeProfile
  rw [egbFixedChargeACriticalMixedProfile_evolved_energy]
  have hp : ((4 : ℝ) ^ (m + 1)) ^ 2 = (16 : ℝ) ^ (m + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  change _ = (egbFixedChargeAGibbsPerturbationScale n
    (egbFixedChargeACriticalMixedProfile n
      (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt x)
      (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1) * Real.sqrt y)) /
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k) ^ 2 * _
  rw [mul_pow (egbFixedChargeAGibbsTunableAttenuation k) (Real.sqrt x) 2,
    mul_pow (egbFixedChargeAGibbsTunableAttenuation k * (4 : ℝ) ^ (m + 1)) (Real.sqrt y) 2,
    mul_pow (egbFixedChargeAGibbsTunableAttenuation k) ((4 : ℝ) ^ (m + 1)) 2,
    Real.sq_sqrt (x := (x : ℝ)) x.property, Real.sq_sqrt (x := (y : ℝ)) y.property, hp]
  ring

end
end GaloisForLFunctions.HTGeometry
