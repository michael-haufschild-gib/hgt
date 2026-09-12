import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalOppositeCurrentProfile
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonRestoration
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRegularOuterPairing

/-! The opposite profile is the missing part of the original normalizable temporal current. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction
noncomputable section
set_option autoImplicit false

/-- The original temporal current with the normalizable left mode and the original radial Jacobian. -/
def normalizableTemporalRadialDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (w : ℂ) (z : ℝ) : ℂ :=
  (((tortoiseRadius (tortoiseOf z) : ℂ) ^ 2 - 1) *
    continuedPhysicalTimeAction q branch w a true (tortoiseOf z) zang) /
    (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ))

/-- The actual omitted part of the normalizable current, before any endpoint subtraction. -/
def oppositeTemporalRadialDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (w : ℂ) (z : ℝ) : ℂ :=
  normalizableTemporalRadialDensity q branch a zang w z -
    horizonRegularCoefficient w (physicalRadialFrequency q) (normalizable w (physicalRadialFrequency q))
      (normalizableFirst w (physicalRadialFrequency q)) * continuedTemporalRadialDensity q branch a zang w z

/-- The retained physical response and source contact multiplying the left mode. -/
def temporalCurrentSourceFactor (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (zang : D4BMHorizon.Point) : ℂ :=
  (-2 * w * (physicalAngularParameter q ^ 2 - 1 / 4 - 2) *
    continuedPhysicalSelfResponse q branch w a t -
    w * horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a w t) *
      modeAngularSquare (physicalModeAngularJet q zang)

private theorem incoming_density_source (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    continuedTemporalRadialDensity q branch a zang w z =
      temporalCurrentSourceFactor q branch a w (tortoiseOf z) zang *
        horizon w (physicalRadialFrequency q) z /
        (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ)) := by
  rw [continuedTemporalRadialDensity,
    continuedPhysicalTimeAction_radial_density q branch w a false (tortoiseOf z) (tortoiseOf_neg hz) zang]
  simp only [tortoiseMode, radialMode, Bool.false_eq_true, if_false, horizonCoordinate_tortoiseOf hz]
  unfold temporalCurrentSourceFactor
  ring

private theorem normalizable_density_source (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    normalizableTemporalRadialDensity q branch a zang w z =
      temporalCurrentSourceFactor q branch a w (tortoiseOf z) zang *
        normalizable w (physicalRadialFrequency q) z /
        (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ)) := by
  rw [normalizableTemporalRadialDensity,
    continuedPhysicalTimeAction_radial_density q branch w a true (tortoiseOf z) (tortoiseOf_neg hz) zang]
  simp only [tortoiseMode, radialMode, if_true, horizonCoordinate_tortoiseOf hz]
  unfold temporalCurrentSourceFactor
  ring

/-- The exact original left-mode decomposition identifies the opposite contribution. -/
theorem oppositeTemporalRadialDensity_eq_mode (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) (hw : w.im ≠ 0) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    oppositeTemporalRadialDensity q branch a zang w z =
      (connection w (physicalRadialFrequency q) / (2 * w)) *
        temporalCurrentSourceFactor q branch a w (tortoiseOf z) zang *
        horizon (-w) (physicalRadialFrequency q) z /
        (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ)) := by
  have hn := (original_homogeneous_horizon_representation w (physicalRadialFrequency q) hw
    (fun t ht => (normalizable_derivatives_continued ht).1)
    (fun t ht => (normalizable_derivatives_continued ht).2)
    (fun t ht => normalizable_equation_continued ht) hz).1
  rw [normalizable_opposite_coefficient w (physicalRadialFrequency q) hw] at hn
  rw [oppositeTemporalRadialDensity, incoming_density_source q branch a w zang hz,
    normalizable_density_source q branch a w zang hz, hn]
  ring

/-- The original opposite current equals the pole-free profile divided by its logarithmic coordinate. -/
theorem oppositeTemporalRadialDensity_eq_profile (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) (hw : w.im ≠ 0)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    oppositeTemporalRadialDensity q branch a zang w z =
      oppositeTemporalProfile q branch a zang w z / (z : ℂ) := by
  let E := modeAngularSquare (physicalModeAngularJet q zang) *
    (-2 * w * (physicalAngularParameter q ^ 2 - 1 / 4 - 2) * selfPart q branch a w z -
      w * contactPart q branch a w z)
  have hself := selfPart_eq_physicalResponse q branch a w (tortoiseOf z) (tortoiseOf_neg hz) hs hc
  have hcontact := contactPart_eq_sourceProjection q branch a w (tortoiseOf z) (tortoiseOf_neg hz)
  rw [horizonCoordinate_tortoiseOf hz] at hself hcontact
  have hsource : reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
      temporalCurrentSourceFactor q branch a w (tortoiseOf z) zang = (z : ℂ) ^ (w / 2) * E := by
    dsimp only [temporalCurrentSourceFactor, E]
    linear_combination
      -(modeAngularSquare (physicalModeAngularJet q zang) *
        (-2 * w * (physicalAngularParameter q ^ 2 - 1 / 4 - 2))) * hself +
      (modeAngularSquare (physicalModeAngularJet q zang) * w) * hcontact
  have hp : (z : ℂ) ^ (w / 2) * (z : ℂ) ^ (-w / 2) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.1.ne'),
      show w / 2 + -w / 2 = 0 by ring, Complex.cpow_zero]
  rw [oppositeTemporalRadialDensity_eq_mode q branch a w zang hw hz,
    ← oppositeCurrentRatio_mul_clearing q branch w hs, horizon_eq_pow_mul]
  calc
    _ = oppositeCurrentRatio q branch w *
        (reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
          temporalCurrentSourceFactor q branch a w (tortoiseOf z) zang) *
        ((z : ℂ) ^ (-w / 2) * gaussProfile q (-w) z) /
        (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ)) := by
      simp only [gaussProfile, mul_assoc]
    _ = oppositeCurrentRatio q branch w * ((z : ℂ) ^ (w / 2) * (z : ℂ) ^ (-w / 2)) *
        E * gaussProfile q (-w) z / (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ)) := by
      rw [hsource]
      ring
    _ = oppositeTemporalProfile q branch a zang w z / (z : ℂ) := by
      rw [hp]
      dsimp only [oppositeTemporalProfile, E]
      ring

/-- Spatial regularity of the original incoming current follows from its actual cleared profile. -/
theorem continuedTemporalRadialDensity_continuousAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (continuedTemporalRadialDensity q branch a zang w) z := by
  have hD : reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hs) hc
  have hF := clearedDensityProfile_continuousAt q branch a w zang hw hwr hz
  have hp := (power_derivatives (w - 1) hz.1).1.continuousAt
  have hquot : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (w - 1) *
      clearedDensityProfile q branch a zang w x /
        reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch)) z :=
    (hp.mul hF).div_const _
  apply hquot.congr
  filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
  rw [clearedDensityProfile_eq_radialDensity q branch a w zang hs hc hx, mul_div_cancel_left₀ _ hD]

theorem oppositeTemporalRadialDensity_continuousAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) (hg : gaussProfile q w z ≠ 0) :
    ContinuousAt (oppositeTemporalRadialDensity q branch a zang w) z := by
  have hquot : ContinuousAt (fun x : ℝ => oppositeTemporalProfile q branch a zang w x / (x : ℂ)) z :=
    (oppositeTemporalProfile_continuousAt q branch a w zang hw hwr hz hg).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hz.1.ne')
  apply hquot.congr
  filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
  exact (oppositeTemporalRadialDensity_eq_profile q branch a w zang hw hs hc hx).symm

/-- Both terms are genuinely integrable before the single original current integral is split. -/
theorem normalizableTemporalRadialDensity_integral_decomposition
    (q : XiZeroCopy) (branch : Bool) (a w : ℂ) (zang : D4BMHorizon.Point)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0)
    {e b : ℝ} (he : 0 < e) (heb : e ≤ b) (hb : b < 1)
    (hg : ∀ z ∈ Icc e b, gaussProfile q w z ≠ 0) :
    (∫ z in e..b, normalizableTemporalRadialDensity q branch a zang w z) =
      horizonRegularCoefficient w (physicalRadialFrequency q) (normalizable w (physicalRadialFrequency q))
        (normalizableFirst w (physicalRadialFrequency q)) *
        (∫ z in e..b, continuedTemporalRadialDensity q branch a zang w z) +
      (∫ z in e..b, oppositeTemporalRadialDensity q branch a zang w z) := by
  have hI : IntervalIntegrable (continuedTemporalRadialDensity q branch a zang w) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro z hz
    rw [uIcc_of_le heb] at hz
    exact (continuedTemporalRadialDensity_continuousAt q branch a w zang hw hwr hs hc
      ⟨he.trans_le hz.1, hz.2.trans_lt hb⟩).continuousWithinAt
  have hO : IntervalIntegrable (oppositeTemporalRadialDensity q branch a zang w) volume e b := by
    apply ContinuousOn.intervalIntegrable
    intro z hz
    rw [uIcc_of_le heb] at hz
    exact (oppositeTemporalRadialDensity_continuousAt q branch a w zang hw hwr hs hc
      ⟨he.trans_le hz.1, hz.2.trans_lt hb⟩ (hg z hz)).continuousWithinAt
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hI.const_mul _) hO]
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only [oppositeTemporalRadialDensity]
  ring

end
end RHTower.D4BMJointSource
