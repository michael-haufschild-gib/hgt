import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentHorizonJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMHorizonModeOuterUniformBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenUniformBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedOuterPairing
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSourceCoefficient
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalPrincipalRegularity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalPrincipalNoncollision

/-!
# The cleared temporal current density in the tortoise variable

Multiplying the radial density of the horizon-mode temporal current by the self-channel clearing
factor `-(u-2s)·connection(u)` removes the fundamental pole.  In the tortoise variable the result
is `z_t^u` times the cleared density core of the horizon-jet module, and it equals an explicit
expression in the cleared reduced Green function, the principal differences, the source amplitude
and the horizon mode.  From that expression we read off spatial continuity, analyticity in the
frequency at every fixed radius, and one uniform bound on every half-line `[T, 0)` for a whole
frequency neighbourhood of the fundamental quasinormal frequency, up to spatial infinity.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore D4BMJointWave
  D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## Definitions -/

/-- The cleared temporal density in the tortoise variable. -/
def clearedTemporalDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (u : ℂ) (t : ℝ) : ℂ :=
  (horizonCoordinate t : ℂ) ^ u * clearedDensityCore q branch a zang u (horizonCoordinate t)

/-- The self part of the cleared current: cleared reduced Green plus cleared principal channels. -/
def selfExpression (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (t : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q *
      clearedReducedGreen u (physicalRadialFrequency q) (physicalRate q branch) a t +
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
      ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
        physicalAngularGap q q i * continuedPrincipalDifference q branch u a i t

/-- The contact part of the cleared current. -/
def contactExpression (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (t : ℝ) : ℂ :=
  reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
    (sourceAmplitude (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u) t *
        reducedHorizonQuotient (physicalRate q branch) u (radialUnit t) *
        scalarResidualPeriod q (physicalAngularParameter q) +
      ∑ i : Fin 3, continuedPrincipalDifference q branch u a i t *
        scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i))

/-- The cleared current in the tortoise variable, written through the original objects. -/
def clearedTemporalExpression (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (t : ℝ) : ℂ :=
  modeAngularSquare (physicalModeAngularJet q zang) *
    ((-2 * u * (physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2) * selfExpression q branch a u t -
      u * contactExpression q branch a u t) * tortoiseMode false u (physicalRadialFrequency q) t)

/-! ## The two identities -/

theorem tortoiseMode_false_eq_gaussProfile (q : XiZeroCopy) (u : ℂ) (t : ℝ) :
    tortoiseMode false u (physicalRadialFrequency q) t =
      (horizonCoordinate t : ℂ) ^ (u / 2) * gaussProfile q u (horizonCoordinate t) := by
  simp only [tortoiseMode, radialMode_false, gaussProfile]
  exact horizon_eq_pow_mul _ _ _

/-- The dressed density core is the explicit cleared expression. -/
theorem clearedTemporalDensity_eq_expression (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (t : ℝ) (ht : t < 0) :
    clearedTemporalDensity q branch a zang u t = clearedTemporalExpression q branch a zang u t := by
  have hz := horizonCoordinate_interior t ht
  have hz0 : (horizonCoordinate t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hp0 : (horizonCoordinate t : ℂ) ^ (u / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hpow : (horizonCoordinate t : ℂ) ^ u =
      (horizonCoordinate t : ℂ) ^ (u / 2) * (horizonCoordinate t : ℂ) ^ (u / 2) := by
    rw [← Complex.cpow_add _ _ hz0]
    congr 1
    ring
  have hamp := sourceAmplitude_eq_profile (physicalRate q branch) a
    (continuedOnset (physicalRate q branch)) u t ht
  have hquot : reducedHorizonQuotient (physicalRate q branch) u (radialUnit t) =
      quotientProfile q branch u (horizonCoordinate t) := by
    unfold quotientProfile
    rw [← radialUnit_eq_sqrt t ht]
  unfold clearedTemporalDensity clearedDensityCore selfPart contactPart clearedTemporalExpression
    selfExpression contactExpression selfClearedProfile principalProfile
  rw [tortoiseOf_horizonCoordinate ht, tortoiseMode_false_eq_gaussProfile, hamp, hquot, hpow]
  simp only [Fin.sum_univ_three]
  field_simp
  try ring

/-- The cleared temporal current is the dressed density core. -/
theorem clearedTemporalDensity_eq_current (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (hs : u - 2 * physicalRate q branch ≠ 0)
    (hc : connection u (physicalRadialFrequency q) ≠ 0) (t : ℝ) (ht : t < 0) :
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
      (((tortoiseRadius t : ℂ) ^ (2 : ℕ) - 1) * continuedPhysicalTimeAction q branch u a false t zang) =
      clearedTemporalDensity q branch a zang u t := by
  rw [clearedTemporalDensity_eq_expression q branch a zang u t ht,
    continuedPhysicalTimeAction_radial_density q branch u a false t ht zang,
    continuedPhysicalSelfResponse_decomposition]
  unfold clearedTemporalExpression selfExpression contactExpression
    horizonRegularAngularSourceProjection physicalSelfPrincipalResponse
  rw [clearedReducedGreen_eq u (physicalRadialFrequency q) (physicalRate q branch) a hs hc]
  simp only [Fin.sum_univ_three]
  ring

/-! ## Spatial continuity -/

theorem reducedHorizonQuotient_radialUnit_continuousAt (s u : ℂ) (t : ℝ) :
    ContinuousAt (fun r => reducedHorizonQuotient s u (radialUnit r)) t := by
  have hr : ContinuousAt (fun r : ℝ => (radialUnit r : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp (radialUnit_hasDerivAt t).continuousAt
  have hne : (1 : ℂ) + (radialUnit t : ℂ) ≠ 0 := by
    exact_mod_cast (radialUnit_add_one_pos t).ne'
  unfold reducedHorizonQuotient reducedHorizonPolynomial
  fun_prop (disch := exact hne)

theorem selfExpression_continuousAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ)
    (hu : u.im ≠ 0) (hur : -2 < u.re) (t : ℝ) (ht : t < 0) :
    ContinuousAt (selfExpression q branch a u) t := by
  have hG := clearedReducedGreen_continuousAt_thetaCuspHawkingBMReducedOuterPairing u (physicalRadialFrequency q) (physicalRate q branch)
    a hu hur t ht
  have hP0 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 0 t ht).1.continuousAt
  have hP1 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 1 t ht).1.continuousAt
  have hP2 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 2 t ht).1.continuousAt
  unfold selfExpression
  simp only [Fin.sum_univ_three]
  exact (continuousAt_const.mul hG).add (continuousAt_const.mul
    (((continuousAt_const.mul hP0).add (continuousAt_const.mul hP1)).add
      (continuousAt_const.mul hP2)))

theorem contactExpression_continuousAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ)
    (hu : u.im ≠ 0) (hur : -2 < u.re) (t : ℝ) (ht : t < 0) :
    ContinuousAt (contactExpression q branch a u) t := by
  have hP0 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 0 t ht).1.continuousAt
  have hP1 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 1 t ht).1.continuousAt
  have hP2 := (continuedPrincipalDifference_hasDerivAt q branch u a hu hur 2 t ht).1.continuousAt
  have hA := (sourceAmplitude_hasDerivAt (physicalRate q branch) u a
    (continuedOnset (physicalRate q branch) u) t).continuousAt
  have hQ := reducedHorizonQuotient_radialUnit_continuousAt (physicalRate q branch) u t
  unfold contactExpression
  simp only [Fin.sum_univ_three]
  exact continuousAt_const.mul (((hA.mul hQ).mul continuousAt_const).add
    (((hP0.mul continuousAt_const).add (hP1.mul continuousAt_const)).add
      (hP2.mul continuousAt_const)))

theorem clearedTemporalExpression_continuousAt (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (hu : u.im ≠ 0) (hur : -2 < u.re) (t : ℝ) (ht : t < 0) :
    ContinuousAt (clearedTemporalExpression q branch a zang u) t := by
  have hS := selfExpression_continuousAt q branch a u hu hur t ht
  have hK := contactExpression_continuousAt q branch a u hu hur t ht
  have hH := (tortoiseMode_hasDerivAt_continued u (physicalRadialFrequency q) t ht).1.continuousAt
  unfold clearedTemporalExpression
  exact continuousAt_const.mul (((continuousAt_const.mul hS).sub (continuousAt_const.mul hK)).mul hH)

/-- The cleared temporal density is continuous on the exterior tortoise half-line. -/
theorem clearedTemporalDensity_continuousOn (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (hu : u.im ≠ 0) (hur : -2 < u.re) :
    ContinuousOn (clearedTemporalDensity q branch a zang u) (Iio 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  refine (clearedTemporalExpression_continuousAt q branch a zang u hu hur t ht).congr ?_
  filter_upwards [Iio_mem_nhds ht] with r hr
  exact (clearedTemporalDensity_eq_expression q branch a zang u r hr).symm

/-! ## Frequency analyticity at fixed radius -/

theorem reducedGreenClearingFactor_analyticAt (u chi s : ℂ) (hu : u.im ≠ 0) :
    AnalyticAt ℂ (fun v => reducedGreenClearingFactor v chi s) u := by
  unfold reducedGreenClearingFactor
  exact (analyticAt_id.sub analyticAt_const).neg.mul (connection_frequency_analyticAt u chi hu)

theorem sourceAmplitude_onset_analyticAt (s a u : ℂ) (hs : u - 2 * s ≠ 0) (t : ℝ) :
    AnalyticAt ℂ (fun v => sourceAmplitude s v a (continuedOnset s v) t) u := by
  have honset := continuedOnset_analyticAt s u hs
  unfold sourceAmplitude
  fun_prop

theorem reducedHorizonQuotient_frequency_analyticAt (s u : ℂ) (r : ℝ) :
    AnalyticAt ℂ (fun v => reducedHorizonQuotient s v r) u := by
  unfold reducedHorizonQuotient reducedHorizonPolynomial
  fun_prop

theorem selfExpression_frequency_analyticAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ)
    (hu : u.im ≠ 0) (hur : -2 < u.re) (hs : u - 2 * physicalRate q branch ≠ 0)
    (hcp : ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => selfExpression q branch a v t) u := by
  have hG := clearedReducedGreen_analyticAt u (physicalRadialFrequency q) (physicalRate q branch)
    a hu hur t ht
  have hP0 := continuedPrincipalDifference_analyticAt q branch u a hu hur 0 hs (hcp 0) t ht
  have hP1 := continuedPrincipalDifference_analyticAt q branch u a hu hur 1 hs (hcp 1) t ht
  have hP2 := continuedPrincipalDifference_analyticAt q branch u a hu hur 2 hs (hcp 2) t ht
  have hcF := reducedGreenClearingFactor_analyticAt u (physicalRadialFrequency q)
    (physicalRate q branch) hu
  unfold selfExpression
  simp only [Fin.sum_univ_three]
  exact (analyticAt_const.mul hG).add (hcF.mul
    (((analyticAt_const.mul hP0).add (analyticAt_const.mul hP1)).add
      (analyticAt_const.mul hP2)))

theorem contactExpression_frequency_analyticAt (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ)
    (hu : u.im ≠ 0) (hur : -2 < u.re) (hs : u - 2 * physicalRate q branch ≠ 0)
    (hcp : ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => contactExpression q branch a v t) u := by
  have hP0 := continuedPrincipalDifference_analyticAt q branch u a hu hur 0 hs (hcp 0) t ht
  have hP1 := continuedPrincipalDifference_analyticAt q branch u a hu hur 1 hs (hcp 1) t ht
  have hP2 := continuedPrincipalDifference_analyticAt q branch u a hu hur 2 hs (hcp 2) t ht
  have hA := sourceAmplitude_onset_analyticAt (physicalRate q branch) a u hs t
  have hQ := reducedHorizonQuotient_frequency_analyticAt (physicalRate q branch) u (radialUnit t)
  have hcF := reducedGreenClearingFactor_analyticAt u (physicalRadialFrequency q)
    (physicalRate q branch) hu
  unfold contactExpression
  simp only [Fin.sum_univ_three]
  exact hcF.mul (((hA.mul hQ).mul analyticAt_const).add
    (((hP0.mul analyticAt_const).add (hP1.mul analyticAt_const)).add
      (hP2.mul analyticAt_const)))

/-- At every exterior radius the cleared density is analytic in the frequency, including at the
fundamental quasinormal frequency. -/
theorem clearedTemporalDensity_frequency_analyticAt (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (hu : u.im ≠ 0) (hur : -2 < u.re)
    (hs : u - 2 * physicalRate q branch ≠ 0)
    (hcp : ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) (t : ℝ) (ht : t < 0) :
    AnalyticAt ℂ (fun v => clearedTemporalDensity q branch a zang v t) u := by
  have he : (fun v => clearedTemporalDensity q branch a zang v t) =
      fun v => clearedTemporalExpression q branch a zang v t :=
    funext (fun v => clearedTemporalDensity_eq_expression q branch a zang v t ht)
  rw [he]
  have hS := selfExpression_frequency_analyticAt q branch a u hu hur hs hcp t ht
  have hK := contactExpression_frequency_analyticAt q branch a u hu hur hs hcp t ht
  have hH : AnalyticAt ℂ (fun v => tortoiseMode false v (physicalRadialFrequency q) t) u := by
    simp only [tortoiseMode, radialMode_false]
    exact horizon_frequency_analyticAt u (physicalRadialFrequency q) hu
      (horizonCoordinate_interior t ht)
  unfold clearedTemporalExpression
  exact analyticAt_const.mul (((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hS).sub
    (analyticAt_id.mul hK)).mul hH)

end
end RHTower.D4BMJointSource
