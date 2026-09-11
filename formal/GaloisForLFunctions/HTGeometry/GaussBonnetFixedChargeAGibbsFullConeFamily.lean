import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalFullMixedModes
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableLimits

/-! # Full-support Gibbs states with independently prescribed erased, slow, and fast masses -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Independent square-root coefficients prescribe all three nonnegative energy sectors. -/
def egbFixedChargeAGibbsFullConeProfile (n k : ℕ) (R A B : NNReal) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeACriticalFullMixedProfile n
    (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt R)
    (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt A)
    (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt B)

/-- Canonical actual Gibbs energies on the entire three-mass cone. -/
def egbFixedChargeAGibbsFullConeEnergy (n k : ℕ) (R A B : NNReal) : Fin (2 ^ (n + 3)) → ℝ :=
  egbFixedChargeAGibbsPerturbationEnergy n (egbFixedChargeAGibbsFullConeProfile n k R A B)

/-- Common strictly positive amplitude for all three independent sectors. -/
def egbFixedChargeAGibbsFullConeAmplitude (n k : ℕ) (R A B : NNReal) : ℝ :=
  egbFixedChargeAGibbsPerturbationScale n (egbFixedChargeAGibbsFullConeProfile n k R A B) /
    (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k

/-- No sector-zero case makes the common amplitude vanish. -/
theorem egbFixedChargeAGibbsFullConeAmplitude_pos (n k : ℕ) (R A B : NNReal) :
    0 < egbFixedChargeAGibbsFullConeAmplitude n k R A B := by
  exact mul_pos (div_pos (egbFixedChargeAGibbsPerturbationScale_pos n _)
    (pow_pos (by norm_num) _)) (inv_pos.mpr (pow_pos (by norm_num) _))

/-- This common positive scalar converts prescribed masses into actual full-history source masses. -/
def egbFixedChargeAGibbsFullConeScale (n k : ℕ) (R A B : NNReal) : NNReal :=
  ⟨egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2, sq_nonneg _⟩

/-- Positive normalization is defined at every finite stage, including every boundary face of the cone. -/
theorem egbFixedChargeAGibbsFullConeScale_pos (n k : ℕ) (R A B : NNReal) :
    0 < (egbFixedChargeAGibbsFullConeScale n k R A B : ℝ) :=
  sq_pos_of_pos (egbFixedChargeAGibbsFullConeAmplitude_pos n k R A B)

/-- The energy realizes the canonical positive perturbation probability exactly. -/
theorem egbFixedChargeAGibbsFullCone_realization (n k : ℕ) (R A B : NNReal) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsPerturbationProbability n (egbFixedChargeAGibbsFullConeProfile n k R A B) :=
  egbFixedChargeAGibbsPerturbation_realization n _

/-- Every three-mass cone point is realized by an actual full-support Gibbs law. -/
theorem egbFixedChargeAGibbsFullCone_probability_pos (n k : ℕ) (R A B : NNReal)
    (i : Fin (2 ^ (n + 3))) :
    0 < _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) i := by
  rw [egbFixedChargeAGibbsFullCone_realization]
  exact egbFixedChargeAGibbsPerturbationProbability_pos n _ i

/-- The complete actual collision history has three independently prescribed nonnegative coefficients. -/
theorem egbFixedChargeAGibbsFullCone_collision (n k m : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 *
        ((0 : ℝ) ^ m * R + (4 / 9 : ℝ) ^ m * A + (1 / 36 : ℝ) ^ m * B) := by
  unfold egbFixedChargeAGibbsFullConeEnergy
  rw [egbFixedChargeAGibbsPerturbation_collision_identity]
  unfold egbFixedChargeAGibbsFullConeProfile
  rw [egbFixedChargeACriticalFullMixedProfile_evolved_energy]
  change _ = (egbFixedChargeAGibbsPerturbationScale n
    (egbFixedChargeACriticalFullMixedProfile n
      (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt R)
      (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt A)
      (egbFixedChargeAGibbsTunableAttenuation k * Real.sqrt B)) /
        (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsTunableAttenuation k) ^ 2 * _
  rw [mul_pow (egbFixedChargeAGibbsTunableAttenuation k) (Real.sqrt R) 2,
    mul_pow (egbFixedChargeAGibbsTunableAttenuation k) (Real.sqrt A) 2,
    mul_pow (egbFixedChargeAGibbsTunableAttenuation k) (Real.sqrt B) 2,
    Real.sq_sqrt (x := (R : ℝ)) R.property, Real.sq_sqrt (x := (A : ℝ)) A.property,
    Real.sq_sqrt (x := (B : ℝ)) B.property]
  ring

end
end GaloisForLFunctions.HTGeometry
