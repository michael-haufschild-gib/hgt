import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedRadialAdmission

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore D4BMJointWave
noncomputable section
set_option autoImplicit false

/-- Spatial regularity of the undivided self numerator, including connection zeros. -/
theorem clearedReducedGreen_continuousAt (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hwr : -2 < w.re) (t : ℝ) (ht : t < 0) :
    ContinuousAt (clearedReducedGreen w chi s a) t := by
  let K := reducedGreenGradient chi s 1
  have hb := horizonCoordinate_interior t ht
  have hM := (horizonFirstMoment_hasDerivAt s chi a 1 K w hw hwr hb).continuousAt
  have hO := (outerSourceIntegral_hasDerivAt s chi a 1 K w hb).continuousAt
  have hN := (normalizable_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have hH := (horizon_derivatives_continued (w := w) (chi := chi) hb).1.continuousAt
  have h := ((hN.mul hM).add (hH.mul hO)).comp_of_eq
    (horizonCoordinate_hasDerivAt t).continuousAt rfl
  exact (h.mul continuousAt_const).add
    (continuousAt_const.mul (radialLift_hasDerivAt s w a (clearedOnset s w) t).continuousAt)

theorem tortoiseOf_continuousAt {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt tortoiseOf z := by
  unfold tortoiseOf
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz.1
  fun_prop (disch := positivity)

theorem selfClearedProfile_continuousAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (selfClearedProfile q branch a w) z := by
  have hn := (clearedReducedGreen_continuousAt w (physicalRadialFrequency q)
    (physicalRate q branch) a hw hwr (tortoiseOf z) (tortoiseOf_neg hz)).comp
      (tortoiseOf_continuousAt hz)
  exact hn.div (power_derivatives (w / 2) hz.1).1.continuousAt
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne')))

theorem principalProfile_continuousAt (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (i : Fin 3)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (principalProfile q branch a i w) z := by
  have hn := (continuedPrincipalDifference_hasDerivAt q branch w a hw hwr i
    (tortoiseOf z) (tortoiseOf_neg hz)).1.continuousAt.comp (tortoiseOf_continuousAt hz)
  exact hn.div (power_derivatives (w / 2) hz.1).1.continuousAt
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne')))

theorem amplitudeProfile_continuousAt (s a : ℂ) (T : ℂ → ℂ) (w : ℂ) (z : ℝ) :
    ContinuousAt (amplitudeProfile s a T w) z := by
  have h := (power_derivatives (2 * s - w)
    (show 0 < 1 + Real.sqrt (1 - z) by positivity)).1.continuousAt
  have hi : ContinuousAt (fun x : ℝ => 1 + Real.sqrt (1 - x)) z := by fun_prop
  have hp := h.comp_of_eq hi rfl
  exact hp.mul continuousAt_const

theorem quotientProfile_continuousAt (q : XiZeroCopy) (branch : Bool) (w : ℂ) (z : ℝ) :
    ContinuousAt (quotientProfile q branch w) z := by
  have hr : ContinuousAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp
      (show ContinuousAt (fun x : ℝ => Real.sqrt (1 - x)) z by fun_prop)
  have hB := (horizonQuotientBase (physicalRate q branch)).continuousAt.comp hr
  have hL := (horizonQuotientSlopePoly (physicalRate q branch)).continuousAt.comp hr
  have hn : (1 : ℂ) + (Real.sqrt (1 - z) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + Real.sqrt (1 - z) by positivity))
  simpa only [horizonQuotientBase_eval, horizonQuotientSlopePoly_eval, Function.comp_def,
    Pi.add_apply, Pi.mul_apply, Pi.div_apply, quotientProfile, reducedHorizonQuotient] using!
    (hB.add (continuousAt_const.mul hL)).div (continuousAt_const.add hr) hn

theorem gaussProfile_continuousAt (q : XiZeroCopy) (w : ℂ)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) : ContinuousAt (gaussProfile q w) z :=
  (gaussFactor_derivatives_continued (w := w) (chi := physicalRadialFrequency q) false
    (enorm_ofReal_lt_one hz.1 hz.2)).1.comp_ofReal.continuousAt

/-- The full cleared physical profile remains spatially continuous at its QNM. -/
theorem clearedDensityProfile_continuousAt (q : XiZeroCopy) (branch : Bool)
    (a w : ℂ) (zang : D4BMHorizon.Point) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (clearedDensityProfile q branch a zang w) z := by
  have hS := selfClearedProfile_continuousAt q branch a w hw hwr hz
  have hY0 := principalProfile_continuousAt q branch a w hw hwr 0 hz
  have hY1 := principalProfile_continuousAt q branch a w hw hwr 1 hz
  have hY2 := principalProfile_continuousAt q branch a w hw hwr 2 hz
  have hA := amplitudeProfile_continuousAt (physicalRate q branch) a
    (continuedOnset (physicalRate q branch)) w z
  have hQ := quotientProfile_continuousAt q branch w z
  have hG := gaussProfile_continuousAt q w hz
  have hs : 0 < Real.sqrt (1 - z) := Real.sqrt_pos.mpr (by linarith [hz.2])
  have hr : ContinuousAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ)) z :=
    Complex.continuous_ofReal.continuousAt.comp
      (show ContinuousAt (fun x : ℝ => Real.sqrt (1 - x)) z by fun_prop)
  have hn : (Real.sqrt (1 - z) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hself : ContinuousAt (fun x => selfPart q branch a w x) z := by
    dsimp only [selfPart]
    simp only [Fin.sum_univ_three]
    exact (continuousAt_const.mul hS).add (continuousAt_const.mul
      (((continuousAt_const.mul hY0).add (continuousAt_const.mul hY1)).add
        (continuousAt_const.mul hY2)))
  have hcontact : ContinuousAt (fun x => contactPart q branch a w x) z := by
    dsimp only [contactPart]
    simp only [Fin.sum_univ_three]
    exact continuousAt_const.mul (((hA.mul hQ).mul continuousAt_const).add
      (((hY0.mul continuousAt_const).add (hY1.mul continuousAt_const)).add
        (hY2.mul continuousAt_const)))
  exact (continuousAt_const.mul
    (((continuousAt_const.mul hself).sub (continuousAt_const.mul hcontact)).mul hG)).mul
      (hr.inv₀ hn) |>.div_const 2


/-- Frequency regularity of the complete profile uses the analytic self numerator at its pole. -/
theorem clearedDensityProfile_analyticAt (q : XiZeroCopy) (branch : Bool)
    (a w : ℂ) (zang : D4BMHorizon.Point) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : ∀ i : Fin 3, connection w (principalFrequency q i) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => clearedDensityProfile q branch a zang u z) w := by
  have hz0 : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hp0 : (z : ℂ) ^ (w / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  have hp : AnalyticAt ℂ (fun u : ℂ => (z : ℂ) ^ (u / 2)) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_id.div_const 2).const_cpow (Or.inl hz0))) w (mem_univ _)
  have hS : AnalyticAt ℂ (fun u => selfClearedProfile q branch a u z) w :=
    (clearedReducedGreen_analyticAt w (physicalRadialFrequency q) (physicalRate q branch) a
      hw hwr (tortoiseOf z) (tortoiseOf_neg hz)).div hp hp0
  have hY (i : Fin 3) : AnalyticAt ℂ (fun u => principalProfile q branch a i u z) w :=
    (continuedPrincipalDifference_analyticAt q branch w a hw hwr i hs (hc i)
      (tortoiseOf z) (tortoiseOf_neg hz)).div hp hp0
  have hT := continuedOnset_analyticAt (physicalRate q branch) w hs
  have hbase : ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + Real.sqrt (1 - z) by positivity))
  have hpow : AnalyticAt ℂ (fun u : ℂ =>
      ((1 + Real.sqrt (1 - z) : ℝ) : ℂ) ^ (2 * physicalRate q branch - u)) w :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((differentiable_const _ |>.sub differentiable_id).const_cpow (Or.inl hbase))) w (mem_univ _)
  have hA : AnalyticAt ℂ (fun u =>
      amplitudeProfile (physicalRate q branch) a (continuedOnset (physicalRate q branch)) u z) w :=
    hpow.mul (analyticAt_const.mul hT)
  have hden : (1 : ℂ) + (Real.sqrt (1 - z) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + Real.sqrt (1 - z) by positivity))
  have hQ : AnalyticAt ℂ (fun u => quotientProfile q branch u z) w :=
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).div analyticAt_const hden
  have hG : AnalyticAt ℂ (fun u => gaussProfile q u z) w := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw] with u hu
    exact horizonGauss_frequency_differentiableAt u (physicalRadialFrequency q) (z : ℂ) hu
      (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.1] using hz.2)
  have hD : AnalyticAt ℂ (fun u =>
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)) w :=
    (analyticAt_id.sub analyticAt_const).neg.mul
      (connection_frequency_analyticAt w (physicalRadialFrequency q) hw)
  have hY0 := hY 0
  have hY1 := hY 1
  have hY2 := hY 2
  have hself : AnalyticAt ℂ (fun u => selfPart q branch a u z) w := by
    dsimp only [selfPart]
    simp only [Fin.sum_univ_three]
    exact (analyticAt_const.mul hS).add (hD.mul
      (((analyticAt_const.mul hY0).add (analyticAt_const.mul hY1)).add
        (analyticAt_const.mul hY2)))
  have hcontact : AnalyticAt ℂ (fun u => contactPart q branch a u z) w := by
    dsimp only [contactPart]
    simp only [Fin.sum_univ_three]
    exact hD.mul (((hA.mul hQ).mul analyticAt_const).add
      (((hY0.mul analyticAt_const).add (hY1.mul analyticAt_const)).add
        (hY2.mul analyticAt_const)))
  have hscale : AnalyticAt ℂ
      (fun u => -2 * u * (physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2)) w :=
    (analyticAt_const.mul analyticAt_id).mul analyticAt_const
  exact ((analyticAt_const.mul (((hscale.mul hself).sub
    (analyticAt_id.mul hcontact)).mul hG)).mul analyticAt_const).div
      analyticAt_const (by norm_num)

end
end RHTower.D4BMJointSource
