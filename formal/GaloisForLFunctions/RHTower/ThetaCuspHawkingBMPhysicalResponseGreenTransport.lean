import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialModeMatching

/-! Actual physical mode currents and complete-source Green transport on the original radial interior. -/
open Complex Set Filter MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original mode paired with the actual physical response and its proved classical derivative. -/
def physicalCuspModeCurrent (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : ℝ) : ℂ :=
  tortoiseModeFirst outer w (physicalRadialFrequency r) t*physicalCuspProfile q r branch w a hw hd hwi hwr t-
    tortoiseMode outer w (physicalRadialFrequency r) t*deriv (physicalCuspProfile q r branch w a hw hd hwi hwr) t

/-- The actual physical current differentiates to its literal complete-source pairing. -/
theorem physicalCuspModeCurrent_hasDerivAt (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (t : ℝ) (ht : t < 0) :
    HasDerivAt (physicalCuspModeCurrent q r branch w a hw hd hwi hwr outer)
      (tortoiseMode outer w (physicalRadialFrequency r) t*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t) t := by
  have hp := physicalCuspProfile_hasDerivAt q r branch w a hw hd hwi hwr t ht
  have hm := physicalTortoiseMode_hasDerivAt r w (by linarith) outer t ht
  apply ((hm.2.mul hp.1).sub (hm.1.mul hp.2)).congr_deriv
  unfold physicalCuspSecond
  ring

/-- Finite physical current differences equal integrals of the full projected source, with no omitted cutoff channel. -/
theorem physicalCuspModeCurrent_integral (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (outer : Bool) (s t : ℝ) (hst : s ≤ t) (ht : t < 0) :
    (∫ x in s..t, tortoiseMode outer w (physicalRadialFrequency r) x*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) =
      physicalCuspModeCurrent q r branch w a hw hd hwi hwr outer t-
        physicalCuspModeCurrent q r branch w a hw hd hwi hwr outer s := by
  have hs : uIcc s t ⊆ Iio (0:ℝ) := by
    rw [uIcc_of_le hst]
    exact fun _ hx => hx.2.trans_lt ht
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => physicalCuspModeCurrent_hasDerivAt q r branch w a hw hd hwi hwr outer x (hs hx))
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hm := (physicalTortoiseMode_hasDerivAt r w (by linarith) outer x (hs hx)).1.continuousAt
  have hF := continuedAngularSourceProjection_continuousOn q branch (physicalAngularParameter r) a w hwi
    (abs_lt.mp hwr).1
  exact hm.continuousWithinAt.mul ((hF x (hs hx)).mono hs)

/-- The original Wronskian reconstructs the actual physical profile from its two actual currents. -/
theorem physicalCuspProfile_modeCurrents (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    connection w (physicalRadialFrequency r)*physicalCuspProfile q r branch w a hw hd hwi hwr t =
      tortoiseMode true w (physicalRadialFrequency r) t*physicalCuspModeCurrent q r branch w a hw hd hwi hwr false t-
        tortoiseMode false w (physicalRadialFrequency r) t*physicalCuspModeCurrent q r branch w a hw hd hwi hwr true t := by
  have hW := tortoiseMode_wronskian (physicalRadialFrequency_chamber r w (by linarith)) t ht
  unfold physicalCuspModeCurrent
  linear_combination (physicalCuspProfile q r branch w a hw hd hwi hwr t)*hW

/-- The actual physical response has complete-source Green transport from every interior base point.
Both constants are extracted from its original physical jets; neither is supplied as a boundary hypothesis. -/
theorem physicalCuspProfile_green_transport (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (s t : ℝ) (hst : s ≤ t) (ht : t < 0) :
    connection w (physicalRadialFrequency r)*physicalCuspProfile q r branch w a hw hd hwi hwr t =
      tortoiseMode true w (physicalRadialFrequency r) t*
        (physicalCuspModeCurrent q r branch w a hw hd hwi hwr false s+
          ∫ x in s..t, tortoiseMode false w (physicalRadialFrequency r) x*
            continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x)-
      tortoiseMode false w (physicalRadialFrequency r) t*
        (physicalCuspModeCurrent q r branch w a hw hd hwi hwr true s+
          ∫ x in s..t, tortoiseMode true w (physicalRadialFrequency r) x*
            continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) := by
  rw [physicalCuspModeCurrent_integral q r branch w a hw hd hwi hwr false s t hst ht,
    physicalCuspModeCurrent_integral q r branch w a hw hd hwi hwr true s t hst ht]
  simpa only [← add_sub_assoc,add_sub_cancel_left] using
    physicalCuspProfile_modeCurrents q r branch w a hw hd hwi hwr t ht

end
end RHTower.D4BMJointSource
