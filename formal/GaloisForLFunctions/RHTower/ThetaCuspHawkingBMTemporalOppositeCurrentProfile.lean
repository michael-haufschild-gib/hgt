import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonRegularity

/-! The complete opposite-current profile after cancellation of its physical connection factor. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore D4BMJointWave
  D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Ratio of the actual opposite-mode coefficient to the cleared Green denominator. -/
def oppositeCurrentRatio (q : XiZeroCopy) (branch : Bool) (u : ℂ) : ℂ :=
  -1 / (2 * u * (u - 2 * physicalRate q branch))

/-- Full opposite-current profile, including every self, principal and source-contact term. -/
def oppositeTemporalProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (z : ℝ) : ℂ :=
  oppositeCurrentRatio q branch u *
    (modeAngularSquare (physicalModeAngularJet q zang) *
      ((-2 * u * (physicalAngularParameter q ^ 2 - 1 / 4 - 2) * selfPart q branch a u z -
        u * contactPart q branch a u z) * gaussProfile q (-u) z) *
      ((Real.sqrt (1 - z))⁻¹ : ℂ) / 2)

theorem oppositeCurrentRatio_analyticAt (q : XiZeroCopy) (branch : Bool) (u : ℂ)
    (hu : u ≠ 0) (hs : u - 2 * physicalRate q branch ≠ 0) :
    AnalyticAt ℂ (oppositeCurrentRatio q branch) u :=
  analyticAt_const.div
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.sub analyticAt_const))
    (mul_ne_zero (mul_ne_zero (by norm_num) hu) hs)

theorem oppositeCurrentRatio_mul_clearing (q : XiZeroCopy) (branch : Bool) (u : ℂ)
    (hs : u - 2 * physicalRate q branch ≠ 0) :
    oppositeCurrentRatio q branch u *
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) =
        connection u (physicalRadialFrequency q) / (2 * u) := by
  unfold oppositeCurrentRatio reducedGreenClearingFactor
  field_simp [hs]

/-- Reflection of the Gauss parameter preserves the common quadratic horizon estimate. -/
theorem negativeGaussProfile_germ (q : XiZeroCopy) (side : Bool) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (fun u z => gaussProfile q (-u) z) := by
  let w := physicalFundamentalFrequency q side
  have hw : (-w).im ≠ 0 := by
    simpa only [Complex.neg_im, neg_ne_zero] using (physicalFundamentalFrequency_strip q side).1
  obtain ⟨R, C, L, hR, _, _, hg⟩ := horizonGauss_uniform_second_bound
    (-w) (physicalRadialFrequency q) hw (b := 1 / 2) (by norm_num) (by norm_num)
  have hj : HasUniformJet2 (closedBall w (R / 2)) (1 / 2)
      (fun u z => gaussProfile q (-u) z) (fun _ => 1)
      (fun u => horizonGaussFirstCoefficient (-u) (physicalRadialFrequency q)) C := by
    intro u hu z hz
    have hu' : -u ∈ ball (-w) R := by
      have hd := mem_closedBall.mp hu
      rw [mem_ball, dist_neg_neg]
      linarith
    exact (hg (-u) hu').2 z ⟨hz.1.le, hz.2⟩
  exact AnalyticJet2At.of_jet (half_pos hR) (by norm_num) le_rfl analyticAt_const
    ((horizonGaussFirstCoefficient_analyticAt (-w) (physicalRadialFrequency q) hw).comp
      analyticAt_id.neg) hj

/-- Every retained term admits one uniform horizon jet after the original connection cancels. -/
theorem oppositeTemporalProfile_germ (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) :
    AnalyticJet2At (physicalFundamentalFrequency q side) (oppositeTemporalProfile q branch a zang) := by
  let w := physicalFundamentalFrequency q side
  have hw : w.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hw0 : w ≠ 0 := by intro h; apply hw; simp [h]
  have hs : w - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hX := selfClearedProfile_germ q branch side a
  have hY0 := principalProfile_germ q branch side a 0
  have hY1 := principalProfile_germ q branch side a 1
  have hY2 := principalProfile_germ q branch side a 2
  have hA := amplitudeProfile_germ (physicalRate q branch) a (continuedOnset (physicalRate q branch))
    (continuedOnset_analyticAt _ _ hs)
  have hQ := quotientProfile_germ q branch w
  have hD : AnalyticAt ℂ
      (fun u => reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)) w :=
    (analyticAt_id.sub analyticAt_const).neg.mul (connection_frequency_analyticAt w _ hw)
  have hself : AnalyticJet2At w (selfPart q branch a) := by
    have h1 := hX.const_mul (k := fun _ => physicalSelfSourceCoefficient q) analyticAt_const
    have h2 := hY0.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 0) / physicalAngularGap q q 0) analyticAt_const
    have h3 := hY1.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 1) / physicalAngularGap q q 1) analyticAt_const
    have h4 := hY2.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 2) / physicalAngularGap q q 2) analyticAt_const
    refine (h1.add (((h2.add h3).add h4).const_mul hD)).congr (fun u z => ?_)
    simp only [selfPart, Fin.sum_univ_three]
  have hcontact : AnalyticJet2At w (contactPart q branch a) := by
    have h1 := (hA.mul hQ).const_mul
      (k := fun _ => scalarResidualPeriod q (physicalAngularParameter q)) analyticAt_const
    have h2 := hY0.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 0)) analyticAt_const
    have h3 := hY1.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 1)) analyticAt_const
    have h4 := hY2.const_mul (k := fun _ => scalarCutoffPeriod (physicalAngularParameter q)
      (principalExponent q 2)) analyticAt_const
    refine ((h1.add ((h2.add h3).add h4)).const_mul hD).congr (fun u z => ?_)
    simp only [contactPart, Fin.sum_univ_three]
    ring
  have h1 := hself.const_mul
    (k := fun u => -2 * u * (physicalAngularParameter q ^ 2 - 1 / 4 - 2))
    ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)
  have h2 := hcontact.const_mul (k := fun u => u) analyticAt_id
  have hcore := ((h1.sub h2).mul (negativeGaussProfile_germ q side)).const_mul
    (k := fun _ => modeAngularSquare (physicalModeAngularJet q zang)) analyticAt_const
  exact (((hcore.mul (AnalyticJet2At.inv_sqrt_one_sub w)).div_const 2).const_mul
    (oppositeCurrentRatio_analyticAt q branch w hw0 hs)).congr (fun _ _ => rfl)

/-- The opposite profile can also be recovered from the complete incoming profile locally. -/
theorem oppositeTemporalProfile_eq_ratio (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (z : ℝ) (hg : gaussProfile q u z ≠ 0) :
    oppositeTemporalProfile q branch a zang u z =
      oppositeCurrentRatio q branch u * clearedDensityProfile q branch a zang u z *
        gaussProfile q (-u) z / gaussProfile q u z := by
  unfold oppositeTemporalProfile clearedDensityProfile clearedDensityCore
  field_simp [hg]

/-- The spatial Gauss factor is analytic in the independent frequency off the real axis. -/
theorem gaussProfile_analyticAt (q : XiZeroCopy) (u : ℂ) (hu : u.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun v => gaussProfile q v z) u := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hu] with v hv
  exact horizonGauss_frequency_differentiableAt v (physicalRadialFrequency q) (z : ℂ) hv
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.1] using hz.2)

theorem oppositeTemporalProfile_continuousAt (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (hu : u.im ≠ 0) (hur : -2 < u.re)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) (hg : gaussProfile q u z ≠ 0) :
    ContinuousAt (oppositeTemporalProfile q branch a zang u) z := by
  have hF := clearedDensityProfile_continuousAt q branch a u zang hu hur hz
  have hgp := gaussProfile_continuousAt q u hz
  have hgm := gaussProfile_continuousAt q (-u) hz
  have hquot : ContinuousAt (fun x => oppositeCurrentRatio q branch u *
      clearedDensityProfile q branch a zang u x * gaussProfile q (-u) x / gaussProfile q u x) z :=
    ((continuousAt_const.mul hF).mul hgm).div hgp hg
  apply hquot.congr
  filter_upwards [hgp.eventually_ne hg] with x hx
  exact (oppositeTemporalProfile_eq_ratio q branch a u zang x hx).symm

theorem oppositeTemporalProfile_analyticAt (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (hu : u.im ≠ 0) (hur : -2 < u.re)
    (hs : u - 2 * physicalRate q branch ≠ 0)
    (hc : ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) (hg : gaussProfile q u z ≠ 0) :
    AnalyticAt ℂ (fun v => oppositeTemporalProfile q branch a zang v z) u := by
  have hu0 : u ≠ 0 := by intro h; apply hu; simp [h]
  have hF := clearedDensityProfile_analyticAt q branch a u zang hu hur hs hc hz
  have hgp := gaussProfile_analyticAt q u hu hz
  have hgm := (gaussProfile_analyticAt q (-u)
    (by simpa only [Complex.neg_im, neg_ne_zero] using hu) hz).comp analyticAt_id.neg
  have hquot : AnalyticAt ℂ (fun v => oppositeCurrentRatio q branch v *
      clearedDensityProfile q branch a zang v z * gaussProfile q (-v) z / gaussProfile q v z) u :=
    (((oppositeCurrentRatio_analyticAt q branch u hu0 hs).mul hF).mul hgm).div hgp hg
  apply hquot.congr
  filter_upwards [hgp.continuousAt.eventually_ne hg] with v hv
  exact (oppositeTemporalProfile_eq_ratio q branch a v zang z hv).symm

end
end RHTower.D4BMJointSource
