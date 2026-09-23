import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalOppositeOuterCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentRadialCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentFundamentalFactor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalNormJoin

/-! The original complete normalizable temporal current over the outer radial interval. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Original outer temporal-current integral with the complete normalizable left mode. -/
def normalizableTemporalOuterIntegral (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (T : ℝ) (u : ℂ) : ℂ :=
  ∫ t in Ioo T 0, ((tortoiseRadius t:ℂ)^(2 : ℕ)-1) *
    continuedPhysicalTimeAction q branch u a true t zang

/-- The original outer normalizable current is integrable and equals its two actual left-mode
components near the physical QNM. -/
theorem normalizableTemporalOuterIntegral_decomposition (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) (T : ℝ) (hT : T < 0) :
    ∀ᶠ u in 𝓝[≠] (physicalFundamentalFrequency q side),
      IntegrableOn (fun t => ((tortoiseRadius t:ℂ)^(2 : ℕ)-1) *
        continuedPhysicalTimeAction q branch u a true t zang) (Ioo T 0) ∧
      normalizableTemporalOuterIntegral q branch a zang T u =
        horizonRegularCoefficient u (physicalRadialFrequency q) (normalizable u (physicalRadialFrequency q))
          (normalizableFirst u (physicalRadialFrequency q)) *
          (compactPart q branch a zang (horizonCoordinate T) u /
            reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)) +
        oppositeTemporalOuterIntegral q branch a zang T u := by
  have hw := physicalFundamentalFrequency_strip q side
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RI, CI, hRI, _, hI⟩ := clearedTemporalDensity_outer_uniform_bound q branch side a zang T
  obtain ⟨RO, CO, hRO, _, hO⟩ := oppositeTemporalOuterDensity_outer_uniform_bound q branch side a zang T
  have hreal : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), -2 < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (abs_lt.mp hw.2).1
  have hsource : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), u-2*physicalRate q branch ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hs
  have hballI : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), u ∈ ball (physicalFundamentalFrequency q side) RI :=
    ball_mem_nhds _ hRI
  have hballO : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), u ∈ ball (physicalFundamentalFrequency q side) RO :=
    ball_mem_nhds _ hRO
  filter_upwards [(Complex.continuous_im.continuousAt.eventually_ne hw.1).filter_mono nhdsWithin_le_nhds,
    hreal.filter_mono nhdsWithin_le_nhds, hsource.filter_mono nhdsWithin_le_nhds,
    hballI.filter_mono nhdsWithin_le_nhds,
    hballO.filter_mono nhdsWithin_le_nhds,
    connection_eventually_ne_zero _ (physicalRadialFrequency q) hw.1] with u hui hur hus huI huO hcu
  let D := reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)
  let A := horizonRegularCoefficient u (physicalRadialFrequency q) (normalizable u (physicalRadialFrequency q))
    (normalizableFirst u (physicalRadialFrequency q))
  have hD : D ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hus) hcu
  have hci : IntegrableOn (clearedTemporalDensity q branch a zang u) (Ioo T 0) := by
    have hcont := (clearedTemporalDensity_continuousOn q branch a zang u hui hur).mono
      (show Ioo T 0 ⊆ Iio 0 from fun _ ht => ht.2)
    have hd : Integrable (fun _ : ℝ => CI) (volume.restrict (Ioo T 0)) := integrable_const _
    refine hd.mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hI u huI t ⟨ht.1.le, ht.2⟩
  have hco : IntegrableOn (oppositeTemporalOuterDensity q branch a zang u) (Ioo T 0) := by
    have hcont : ContinuousOn (oppositeTemporalOuterDensity q branch a zang u) (Ioo T 0) :=
      fun t ht => (oppositeTemporalOuterDensity_continuousAt q branch a u zang hui hur ht.2).continuousWithinAt
    have hd : Integrable (fun _ : ℝ => CO) (volume.restrict (Ioo T 0)) := integrable_const _
    refine hd.mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hO u huO t ⟨ht.1.le, ht.2⟩
  have he (t : ℝ) (ht : t ∈ Ioo T 0) :
      ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*continuedPhysicalTimeAction q branch u a true t zang =
        A*(clearedTemporalDensity q branch a zang u t / D) +
          oppositeTemporalOuterDensity q branch a zang u t := by
    have hi := clearedTemporalDensity_eq_current q branch a zang u hus hcu t ht.2
    have hji : ((tortoiseRadius t:ℂ)^(2 : ℕ)-1)*continuedPhysicalTimeAction q branch u a false t zang =
        clearedTemporalDensity q branch a zang u t / D := by
      apply (eq_div_iff hD).mpr
      simpa only [mul_comm] using hi
    have ho := oppositeTemporalOuterDensity_eq_original q branch a u zang hui hus hcu t ht.2
    rw [hji] at ho
    linear_combination ho
  have hsum := ((hci.div_const D).const_mul A).add hco
  refine ⟨hsum.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (he t ht).symm
  unfold normalizableTemporalOuterIntegral
  calc
    _ = ∫ t in Ioo T 0, A*(clearedTemporalDensity q branch a zang u t/D) +
        oppositeTemporalOuterDensity q branch a zang u t :=
      setIntegral_congr_fun measurableSet_Ioo he
    _ = _ := by
      rw [integral_add ((hci.div_const D).const_mul A) hco, integral_const_mul]
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const]
      dsimp only [compactPart, oppositeTemporalOuterIntegral]
      rw [tortoiseOf_horizonCoordinate hT]


/-- The original complete normalizable outer integral has the incoming cleared residue; the
opposite contribution was analytically integrated, with the source contact retained. -/
theorem normalizableTemporalOuterIntegral_residue (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) (T : ℝ) (hT : T < 0) :
    Tendsto (fun u => (u - physicalFundamentalFrequency q side) *
      normalizableTemporalOuterIntegral q branch a zang T u)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (compactPart q branch a zang (horizonCoordinate T) (physicalFundamentalFrequency q side) /
        physicalFundamentalDenominatorSlope q branch side)) := by
  let w₀ := physicalFundamentalFrequency q side
  let chi := physicalRadialFrequency q
  have hw : w₀.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hA := normalizable_horizonRegularCoefficient_analyticAt w₀ chi hw
  have hf : w₀ = -3/2 - Complex.I*chi ∨ w₀ = -3/2 + Complex.I*chi := by
    dsimp only [w₀, chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hAv := fundamental_horizonRegularCoefficient w₀ chi hw hf
  have hAlim := hA.continuousAt.tendsto.mono_left
    (show 𝓝[≠] w₀ ≤ 𝓝 w₀ from nhdsWithin_le_nhds)
  rw [hAv] at hAlim
  have hP := compactPart_analyticAt q branch side a zang (horizonCoordinate T)
  have hD := physicalFundamental_clearingFactor_hasDerivAt q branch side
  have hquot := (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
    hD.tendsto_slope (physicalFundamental_denominatorSlope_ne_zero q branch side)
  have hI : Tendsto (fun u => (u-w₀) *
      (compactPart q branch a zang (horizonCoordinate T) u /
        reducedGreenClearingFactor u chi (physicalRate q branch)))
      (𝓝[≠] w₀) (𝓝 (compactPart q branch a zang (horizonCoordinate T) w₀ /
        physicalFundamentalDenominatorSlope q branch side)) := by
    apply hquot.congr'
    filter_upwards [] with u
    simp only [Pi.div_apply, slope_def_field, physicalFundamental_clearingFactor_zero,
      sub_zero, div_div_eq_mul_div]
    ring
  have hX : Tendsto (fun u : ℂ => u-w₀) (𝓝[≠] w₀) (𝓝 0) := by
    have hi : Tendsto (fun u : ℂ => u) (𝓝[≠] w₀) (𝓝 w₀) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hi.sub_const w₀
  have hO := hX.mul ((oppositeTemporalOuterIntegral_analyticAt q branch side a zang T).continuousAt.tendsto.mono_left
    (show 𝓝[≠] w₀ ≤ 𝓝 w₀ from nhdsWithin_le_nhds))
  have hlim := (hAlim.mul hI).add hO
  simp only [one_mul, zero_mul, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [normalizableTemporalOuterIntegral_decomposition q branch side a zang T hT] with u hu
  rw [hu.2]
  ring

/-- The complete cleared current has its original fundamental norm density throughout the exterior. -/
theorem clearedTemporalDensity_fundamental_factor (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (t : ℝ) (ht : t < 0) :
    clearedTemporalDensity q branch a zang (physicalFundamentalFrequency q side) t =
      physicalTemporalFundamentalAmplitude q branch side a zang *
        normalizable (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
          (horizonCoordinate t)^(2 : ℕ) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hf : physicalFundamentalFrequency q side = -3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side = -3/2+Complex.I*physicalRadialFrequency q := by
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  rw [clearedTemporalDensity_eq_expression q branch a zang _ t ht]
  simp only [clearedTemporalExpression, selfExpression, contactExpression,
    physicalFundamental_clearingFactor_zero, zero_mul, mul_zero, add_zero, sub_zero]
  rw [clearedReducedGreen_fundamental_factor _ _ _ _ hw.1 (abs_lt.mp hw.2).1 hf t ht]
  simp only [tortoiseMode, radialMode_false]
  rw [horizon_eq_normalizable_fundamental _ _ hw.1 hf (horizonCoordinate_interior t ht),
    normalizable_fundamental_value _ _ hf]
  dsimp only [physicalTemporalFundamentalAmplitude]
  ring

/-- The original outer current retains precisely the same source scalar as the horizon numerator. -/
theorem compactPart_fundamental_factor (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (b : ℝ) :
    compactPart q branch a zang b (physicalFundamentalFrequency q side) =
      physicalTemporalFundamentalAmplitude q branch side a zang *
        (∫ t in Ioo (tortoiseOf b) 0,
          normalizable (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
            (horizonCoordinate t)^(2 : ℕ)) := by
  rw [compactPart, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact clearedTemporalDensity_fundamental_factor q branch side a zang t ht.2

/-- Source-evaluated full radial residue with the original norm and denominator. -/
def physicalTemporalFundamentalRadialResidue (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) : ℂ :=
  physicalTemporalFundamentalAmplitude q branch side a zang *
    D4BMFundamentalNorm.normFinitePart (physicalFundamentalFrequency q side) /
    physicalFundamentalDenominatorSlope q branch side

/-- The norm and denominator introduce no additional zero into the actual source amplitude. -/
theorem physicalTemporalFundamentalRadialResidue_ne_zero_iff (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    physicalTemporalFundamentalRadialResidue q branch side a zang ≠ 0 ↔
      physicalTemporalFundamentalAmplitude q branch side a zang ≠ 0 := by
  have hw := physicalFundamentalFrequency_strip q side
  have hn := D4BMFundamentalNorm.normFinitePart_ne_zero _ (abs_lt.mp hw.2).1 hw.1
  have hd := physicalFundamental_denominatorSlope_ne_zero q branch side
  unfold physicalTemporalFundamentalRadialResidue
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp (div_ne_zero_iff.mp h).1).1
  · intro h
    exact div_ne_zero (mul_ne_zero h hn) hd

end
end RHTower.D4BMJointSource
