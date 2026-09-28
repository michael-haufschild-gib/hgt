import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction

/-! # Finite-cutoff two-leg action transgression

Adding the radial source contact to the literal projected Einstein current gives a
contact-renormalized current `R_o = J_o + K_o N` whose increment over a finite radial interval is
exactly the mode/source integral, `R_o(t) - R_o(s) = -c I_o N` with
`c = ν_r² - 1/4 - 2`.  The difference of two outer legs is antisymmetric in the legs and has
increment `-c (I_{o₁} - I_{o₂}) N`. -/

open Set

namespace RHTower.D4BMPhysicalModeAction
open D4BMJointWave D4BMJointSource D4BMLaplaceRadial

set_option autoImplicit false

variable (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
  (hw : 0 < w.re) (hd : 3 / 2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)

/-- The contact-renormalized current `R_o(u) = J_o(u) + K_o(u) N`. -/
noncomputable def contactRenormalizedCurrent (outer : Bool) (u : Iio (0 : ℝ))
    (z : D4BMHorizon.Point) (hz : 0 < z 1) : ℂ :=
  physicalProjectedModeAction q r branch w a hw hd hwi hwr outer u z hz 1 +
    physicalModeSourceContact q r branch w a outer u *
      modeAngularSquare (physicalModeAngularJet r z)

/-- The mode/source integral `I_o = ∫_s^t tortoiseMode_o · (angular source projection)`. -/
noncomputable def modeSourceIntegral (outer : Bool) (s t : ℝ) : ℂ :=
  ∫ x in s..t, tortoiseMode outer w (physicalRadialFrequency r) x *
    continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x

/-- **One-leg transgression**: the contact is an exact endpoint renormalization,
`R_o(t) - R_o(s) = -c I_o N`. -/
theorem contactRenormalizedCurrent_transport (outer : Bool) (s t : Iio (0 : ℝ))
    (hst : (s : ℝ) ≤ t) (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    contactRenormalizedCurrent q r branch w a hw hd hwi hwr outer t z hz -
      contactRenormalizedCurrent q r branch w a hw hd hwi hwr outer s z hz =
      -(physicalAngularParameter r ^ 2 - 1 / 4 - 2) *
        modeSourceIntegral q r branch w a outer s t *
        modeAngularSquare (physicalModeAngularJet r z) := by
  have h := physicalProjectedModeAction_transport q r branch w a hw hd hwi hwr outer s t hst z hz
  simp only [contactRenormalizedCurrent, modeSourceIntegral]
  linear_combination h

/-- The finite two-leg functional `R_{o₁} - R_{o₂}`. -/
noncomputable def twoLegCurrent (o₁ o₂ : Bool) (u : Iio (0 : ℝ)) (z : D4BMHorizon.Point)
    (hz : 0 < z 1) : ℂ :=
  contactRenormalizedCurrent q r branch w a hw hd hwi hwr o₁ u z hz -
    contactRenormalizedCurrent q r branch w a hw hd hwi hwr o₂ u z hz

/-- **Two-leg transgression**: the increment of `R_{o₁} - R_{o₂}` is `-c (I_{o₁} - I_{o₂}) N`. -/
theorem twoLegCurrent_transport (o₁ o₂ : Bool) (s t : Iio (0 : ℝ)) (hst : (s : ℝ) ≤ t)
    (z : D4BMHorizon.Point) (hz : 0 < z 1) :
    twoLegCurrent q r branch w a hw hd hwi hwr o₁ o₂ t z hz -
      twoLegCurrent q r branch w a hw hd hwi hwr o₁ o₂ s z hz =
      -(physicalAngularParameter r ^ 2 - 1 / 4 - 2) *
        (modeSourceIntegral q r branch w a o₁ s t - modeSourceIntegral q r branch w a o₂ s t) *
        modeAngularSquare (physicalModeAngularJet r z) := by
  have h₁ := contactRenormalizedCurrent_transport q r branch w a hw hd hwi hwr o₁ s t hst z hz
  have h₂ := contactRenormalizedCurrent_transport q r branch w a hw hd hwi hwr o₂ s t hst z hz
  simp only [twoLegCurrent]
  linear_combination h₁ - h₂

/-- Interchanging the legs negates the two-leg functional. -/
theorem twoLegCurrent_swap (o₁ o₂ : Bool) (u : Iio (0 : ℝ)) (z : D4BMHorizon.Point)
    (hz : 0 < z 1) :
    twoLegCurrent q r branch w a hw hd hwi hwr o₂ o₁ u z hz =
      -twoLegCurrent q r branch w a hw hd hwi hwr o₁ o₂ u z hz := by
  simp only [twoLegCurrent]
  ring

end RHTower.D4BMPhysicalModeAction
