import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonJet

/-! Exact identification of the full temporal current with its uniform horizon profile. -/
namespace RHTower.D4BMJointSource
open Complex Set D4BMLaplaceRadial D4BMModularCore D4BMJointWave D4BMPhysicalModeAction
noncomputable section
set_option autoImplicit false

/-- All principal cutoff channels and the reduced self response recover the original response. -/
theorem selfPart_eq_physicalResponse (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (ht : t < 0) (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0) :
    (horizonCoordinate t : ℂ) ^ (w / 2) * selfPart q branch a w (horizonCoordinate t) =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        continuedPhysicalSelfResponse q branch w a t := by
  have hp : (horizonCoordinate t : ℂ) ^ (w / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (horizonCoordinate_interior t ht).1.ne'))
  rw [continuedPhysicalSelfResponse_decomposition]
  simp only [selfPart, selfClearedProfile, principalProfile, physicalSelfPrincipalResponse,
    tortoiseOf_horizonCoordinate ht, Fin.sum_univ_three]
  rw [clearedReducedGreen_eq w (physicalRadialFrequency q) (physicalRate q branch) a hs hc t]
  field_simp [hp]

/-- The profile retains the complete projected source contact. -/
theorem contactPart_eq_sourceProjection (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (ht : t < 0) :
    (horizonCoordinate t : ℂ) ^ (w / 2) * contactPart q branch a w (horizonCoordinate t) =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t := by
  have hp : (horizonCoordinate t : ℂ) ^ (w / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (horizonCoordinate_interior t ht).1.ne'))
  rw [horizonRegularAngularSourceProjection,
    sourceAmplitude_eq_profile (physicalRate q branch) a
      (continuedOnset (physicalRate q branch)) w t ht]
  simp only [contactPart, quotientProfile, principalProfile, tortoiseOf_horizonCoordinate ht,
    ← radialUnit_eq_sqrt t ht, Fin.sum_univ_three]
  field_simp [hp]

/-- The two indicial factors reconstruct the cleared, original temporal Einstein current. -/
theorem clearedDensityCore_eq_physicalCurrent (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (ht : t < 0) (zang : D4BMHorizon.Point)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0) :
    (horizonCoordinate t : ℂ) ^ w * clearedDensityCore q branch a zang w (horizonCoordinate t) =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        (((tortoiseRadius t : ℂ) ^ (2 : ℕ) - 1) *
          continuedPhysicalTimeAction q branch w a false t zang) := by
  have hself := selfPart_eq_physicalResponse q branch a w t ht hs hc
  have hcontact := contactPart_eq_sourceProjection q branch a w t ht
  have hz0 : (horizonCoordinate t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior t ht).1.ne'
  have hpow : (horizonCoordinate t : ℂ) ^ w =
      (horizonCoordinate t : ℂ) ^ (w / 2) * (horizonCoordinate t : ℂ) ^ (w / 2) := by
    rw [← Complex.cpow_add _ _ hz0, show w / 2 + w / 2 = w by ring]
  rw [continuedPhysicalTimeAction_radial_density q branch w a false t ht zang]
  simp only [tortoiseMode, radialMode, Bool.false_eq_true, if_false, horizon_eq_pow_mul]
  rw [hpow]
  unfold clearedDensityCore gaussProfile
  linear_combination
    (modeAngularSquare (physicalModeAngularJet q zang) *
      (-2 * w * (physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2)) *
      (horizonCoordinate t : ℂ) ^ (w / 2) *
      gaussFactor w (physicalRadialFrequency q) false (horizonCoordinate t : ℂ)) * hself -
    (modeAngularSquare (physicalModeAngularJet q zang) * w *
      (horizonCoordinate t : ℂ) ^ (w / 2) *
      gaussFactor w (physicalRadialFrequency q) false (horizonCoordinate t : ℂ)) * hcontact

/-- Restoring the Jacobian identifies the Mellin density with the original physical current. -/
theorem clearedDensityProfile_eq_physicalCurrent (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (ht : t < 0) (zang : D4BMHorizon.Point)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0) :
    (horizonCoordinate t : ℂ) ^ (w - 1) *
        clearedDensityProfile q branch a zang w (horizonCoordinate t) =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        (((tortoiseRadius t : ℂ) ^ (2 : ℕ) - 1) *
          continuedPhysicalTimeAction q branch w a false t zang) /
        (2 * (horizonCoordinate t : ℂ) * (Real.sqrt (1 - horizonCoordinate t) : ℂ)) := by
  have hz0 : (horizonCoordinate t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (horizonCoordinate_interior t ht).1.ne'
  rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one, clearedDensityProfile]
  calc
    _ = ((horizonCoordinate t : ℂ) ^ w *
        clearedDensityCore q branch a zang w (horizonCoordinate t)) /
        (2 * (horizonCoordinate t : ℂ) * (Real.sqrt (1 - horizonCoordinate t) : ℂ)) := by
      ring
    _ = _ := by rw [clearedDensityCore_eq_physicalCurrent q branch a w t ht zang hs hc]

/-- On the physical Laplace band the same density is the actual Einstein action component. -/
theorem clearedDensityProfile_eq_actualAction (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : Iio (0:ℝ)) (zang : D4BMHorizon.Point) (hzang : 0 < zang 1)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0) :
    (horizonCoordinate t : ℂ) ^ (w - 1) *
        clearedDensityProfile q branch a zang w (horizonCoordinate t) =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        (((tortoiseRadius t : ℂ) ^ (2 : ℕ) - 1) *
          physicalProjectedModeAction q q branch w a hw hd hwi hwr false t zang hzang 0) /
        (2 * (horizonCoordinate t : ℂ) * (Real.sqrt (1 - horizonCoordinate t) : ℂ)) := by
  rw [clearedDensityProfile_eq_physicalCurrent q branch a w t t.property zang hs hc,
    continuedPhysicalTimeAction_eq_actual q branch w a hw hd hwi hwr false t zang hzang]

end
end RHTower.D4BMJointSource
