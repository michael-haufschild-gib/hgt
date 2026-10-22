import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceHorizonFactor
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalTimeActionContinuation

/-! The full projected source cancels the extra horizon denominator in the original temporal Einstein contact. -/
namespace RHTower.D4BMJointSource
open Complex Set D4BMModularCore D4BMLaplaceRadial D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The exact frequency-dependent source polynomial after removal of its horizon zero. -/
def reducedHorizonQuotient (s w u : ℂ) : ℂ :=
  (reducedHorizonPolynomial s u+w*(s*(s-1)/2*u^(2 : ℕ)*((2*s+3)*u+3)))/(1+u)

/-- Both frequency coefficients supply the same genuine horizon factor. -/
theorem reducedPolynomial_eq_horizonQuotient (s w u : ℂ) (hu : 1+u ≠ 0) :
    reducedPolynomial s w u=(1-u^(2 : ℕ))*reducedHorizonQuotient s w u := by
  rw [reducedPolynomial_affine,reducedPolynomial_horizon,reducedSlope_horizon]
  dsimp [reducedHorizonQuotient]
  field_simp [hu]
  ring

/-- The complete projected source after extracting its actual horizon zero, with every cutoff channel retained. -/
def horizonRegularAngularSourceProjection (q : XiZeroCopy) (branch : Bool) (u a w : ℂ)
    (t : ℝ) : ℂ :=
  sourceAmplitude (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
    reducedHorizonQuotient (physicalRate q branch) w (radialUnit t)*scalarResidualPeriod q u+
    ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*scalarCutoffPeriod u (principalExponent q i)

/-- The actual angular integral, including all three differential cutoff commutators, has an exact horizon zero. -/
theorem continuedAngularSourceProjection_horizon_factor (q : XiZeroCopy) (branch : Bool)
    (u a w : ℂ) (t : ℝ) :
    continuedAngularSourceProjection q branch u a w t=
      (horizonCoordinate t:ℂ)*horizonRegularAngularSourceProjection q branch u a w t := by
  have hu : 1+(radialUnit t:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (radialUnit_add_one_pos t))
  rw [continuedAngularSourceProjection_eq,reducedCoefficient,
    reducedPolynomial_eq_horizonQuotient _ _ _ hu]
  simp only [continuedCutoffRadialCoefficient,horizonRegularAngularSourceProjection,
    mul_add,Finset.mul_sum]
  have hz : (horizonCoordinate t:ℂ)=1-(radialUnit t:ℂ)^(2 : ℕ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
  rw [hz]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The original exterior radius converts the source's exact horizon zero into its contact denominator. -/
theorem radius_sq_mul_horizonCoordinate (t : ℝ) (ht : t < 0) :
    (tortoiseRadius t:ℂ)^(2 : ℕ)*(horizonCoordinate t:ℂ)=(tortoiseRadius t:ℂ)^(2 : ℕ)-1 := by
  have hr : (tortoiseRadius t:ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : (0:ℝ)<1) (tortoiseRadius_exterior t ht)))
  have hu : (radialUnit t:ℂ)=(tortoiseRadius t:ℂ)⁻¹ := by
    exact_mod_cast radialUnit_inverse_radius t
  simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,hu]
  field_simp [hr]

end
end RHTower.D4BMJointSource

namespace RHTower.D4BMPhysicalModeAction
open Complex Set D4BMModularCore D4BMLaplaceRadial D4BMJointSource D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The full original temporal current has no extra horizon pole from its retained source contact. -/
theorem continuedPhysicalTimeAction_radial_density (q : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (outer : Bool) (t : ℝ) (ht : t < 0) (z : D4BMHorizon.Point) :
    ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*continuedPhysicalTimeAction q branch w a outer t z=
      (-2*w*(physicalAngularParameter q^(2 : ℕ)-1/4-2)*continuedPhysicalSelfResponse q branch w a t*
          tortoiseMode outer w (physicalRadialFrequency q) t-
        w*tortoiseMode outer w (physicalRadialFrequency q) t*
          horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t)*
        modeAngularSquare (physicalModeAngularJet q z) := by
  have hR : (tortoiseRadius t:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (show tortoiseRadius t^(2 : ℕ)-1 ≠ 0 by nlinarith [tortoiseRadius_exterior t ht])
  have hz := radius_sq_mul_horizonCoordinate t ht
  have hsource : w*(tortoiseRadius t:ℂ)^(2 : ℕ)*tortoiseMode outer w (physicalRadialFrequency q) t*
      ((horizonCoordinate t:ℂ)*horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t)=
      w*tortoiseMode outer w (physicalRadialFrequency q) t*
        horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t*
        ((tortoiseRadius t:ℂ)^(2 : ℕ)-1) := by
    calc
      _ = w*tortoiseMode outer w (physicalRadialFrequency q) t*
          horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t*
          ((tortoiseRadius t:ℂ)^(2 : ℕ)*(horizonCoordinate t:ℂ)) := by ring
      _ = _ := by rw [hz]
  rw [continuedPhysicalTimeAction,continuedAngularSourceProjection_horizon_factor]
  rw [hsource]
  field_simp [hR]

end
end RHTower.D4BMPhysicalModeAction
