import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentHorizonIdentification
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentHorizonRegularity
import GaloisForLFunctions.HTGeometry.QuadraticEndpointMellin
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalSlope

/-! Two-counterterm restoration of the complete original temporal current near its horizon. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The original temporal current, with the exterior radial Jacobian expressed in the horizon coordinate. -/
def continuedTemporalRadialDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (w : ℂ) (z : ℝ) : ℂ :=
  (((tortoiseRadius (tortoiseOf z) : ℂ) ^ (2 : ℕ) - 1) *
    continuedPhysicalTimeAction q branch w a false (tortoiseOf z) zang) /
    (2 * (z : ℂ) * (Real.sqrt (1 - z) : ℂ))

/-- The cleared profile is the actual current multiplied by its original clearing factor. -/
theorem clearedDensityProfile_eq_radialDensity (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (zang : D4BMHorizon.Point) (hs : w - 2 * physicalRate q branch ≠ 0)
    (hc : connection w (physicalRadialFrequency q) ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    (z : ℂ) ^ (w - 1) * clearedDensityProfile q branch a zang w z =
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) *
        continuedTemporalRadialDensity q branch a zang w z := by
  have h := clearedDensityProfile_eq_physicalCurrent q branch a w
    (tortoiseOf z) (tortoiseOf_neg hz) zang hs hc
  rw [horizonCoordinate_tortoiseOf hz] at h
  simpa only [continuedTemporalRadialDensity, mul_div_assoc] using h

/-- Every sufficiently small common cutoff restores the full horizon current. The restored
numerator is analytic through the QNM; the physical denominator remains the original one. -/
theorem physicalTemporalCurrent_horizon_restoration_data (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ R B : ℝ, ∃ c₀ c₁ : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1 / 2 ∧
      (∃ C : ℝ, 0 ≤ C ∧ HasUniformJet2 (closedBall (physicalFundamentalFrequency q side) R) B
        (clearedDensityProfile q branch a zang) c₀ c₁ C) ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
          (clearedDensityProfile q branch a zang) c₀ c₁ b)
          (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w - physicalFundamentalFrequency q side) *
          (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b w /
            reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch)))
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) / physicalFundamentalDenominatorSlope q branch side)) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          connection w (physicalRadialFrequency q) ≠ 0 →
          Tendsto (fun e : ℝ =>
            (∫ z in e..b, continuedTemporalRadialDensity q branch a zang w z) +
            (c₀ w * (e : ℂ) ^ w / w + c₁ w * (e : ℂ) ^ (w + 1) / (w + 1)) /
              reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch))
            (𝓝[>] (0:ℝ))
            (𝓝 (QuadraticEndpointMellin.finitePart
              (clearedDensityProfile q branch a zang) c₀ c₁ b w /
              reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch))) := by
  let w₀ := physicalFundamentalFrequency q side
  have hw : w₀.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w₀.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w₀ - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RJ, B, hRJ, hB, hBh, c₀, c₁, C, hC, ha₀, ha₁, hjet⟩ :=
    clearedDensityProfile_germ q branch side a zang
  let β := (w₀.re - 2) / 2
  have hβ : -2 < β := by dsimp [β]; linarith
  have hr : ∀ᶠ u : ℂ in 𝓝 w₀, β < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt
      (by dsimp [β]; linarith)
  have hsource : ∀ᶠ u : ℂ in 𝓝 w₀, u - 2 * physicalRate q branch ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hs
  have hprincipal : ∀ᶠ u : ℂ in 𝓝 w₀,
      ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0 :=
    Filter.eventually_all.mpr (fun i =>
      (connection_frequency_analyticAt w₀ (principalFrequency q i) hw).continuousAt.eventually_ne
        (physicalFundamental_principal_connection_ne_zero q side i))
  obtain ⟨RA, hRA, hdata⟩ := Metric.eventually_nhds_iff.mp
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and
      (hr.and (hsource.and (hprincipal.and (ha₀.eventually_analyticAt.and ha₁.eventually_analyticAt)))))
  let R := min RJ RA
  have hR : 0 < R := lt_min hRJ hRA
  have hd (u : ℂ) (hu : u ∈ ball w₀ R) :=
    hdata (mem_ball.mp (ball_subset_ball (min_le_right RJ RA) hu))
  have hJ (u : ℂ) (hu : u ∈ ball w₀ R) : u ∈ closedBall w₀ RJ :=
    ball_subset_closedBall (ball_subset_ball (min_le_left RJ RA) hu)
  refine ⟨R, B, c₀, c₁, hR, hB, hBh,
    ⟨C, hC, hjet.mono (closedBall_subset_closedBall (min_le_left RJ RA))⟩, ?_⟩
  intro b hb hbB
  have hb1 : b < 1 := by linarith
  have hsp (u : ℂ) (hu : u ∈ ball w₀ R) :
      ContinuousOn (clearedDensityProfile q branch a zang u) (Ioc (0:ℝ) b) := by
    intro z hz
    exact (clearedDensityProfile_continuousAt q branch a u zang (hd u hu).1
      (hβ.trans (hd u hu).2.1) ⟨hz.1, hz.2.trans_lt hb1⟩).continuousWithinAt
  have hbound (u : ℂ) (hu : u ∈ ball w₀ R) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) b) :=
    hjet u (hJ u hu) z ⟨hz.1, hz.2.trans hbB⟩
  have hnonzero (u : ℂ) (hui : u.im ≠ 0) : u ≠ 0 ∧ u + 1 ≠ 0 := by
    constructor
    · intro h; apply hui; simp [h]
    · intro h; apply hui; have := congrArg Complex.im h; simpa using this
  have hA : AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
      (clearedDensityProfile q branch a zang) c₀ c₁ b) w₀ :=
    QuadraticEndpointMellin.finitePart_analyticAt hb hb1.le hR hC hβ
    (hnonzero w₀ hw).1 (hnonzero w₀ hw).2
    (fun u hu => (hd u hu).2.1.le) hsp
    (fun u hu => (hd u hu).2.2.2.2)
    (fun z hz u hu => clearedDensityProfile_analyticAt q branch a u zang (hd u hu).1
      (hβ.trans (hd u hu).2.1) (hd u hu).2.2.1 (hd u hu).2.2.2.1
      ⟨hz.1, hz.2.trans_lt hb1⟩) hbound
  refine ⟨hA, ?_, ?_⟩
  · have hD := physicalFundamental_clearingFactor_hasDerivAt q branch side
    have hlim := (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
      hD.tendsto_slope (physicalFundamental_denominatorSlope_ne_zero q branch side)
    apply hlim.congr'
    filter_upwards [] with u
    simp only [Pi.div_apply, slope_def_field, physicalFundamental_clearingFactor_zero,
      sub_zero, div_div_eq_mul_div]
    ring
  intro u hu hc
  have hu0 := hnonzero u (hd u hu).1
  have hD : reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (hd u hu).2.2.1) hc
  have hlim := (QuadraticEndpointMellin.cutoff_tendsto hb (hβ.trans (hd u hu).2.1)
    hu0.1 hu0.2 (hsp u hu) (hbound u hu)).div_const
      (reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
  apply hlim.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, heb] with e he heb
  have heq : (∫ z in e..b, continuedTemporalRadialDensity q branch a zang u z) =
      (∫ z in e..b, (z : ℂ) ^ (u - 1) * clearedDensityProfile q branch a zang u z) /
        reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le heb.le] at hz
    change continuedTemporalRadialDensity q branch a zang u z =
      ((z : ℂ) ^ (u - 1) * clearedDensityProfile q branch a zang u z) /
        reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)
    rw [clearedDensityProfile_eq_radialDensity q branch a u zang (hd u hu).2.2.1 hc
      ⟨he.trans_le hz.1, hz.2.trans_lt hb1⟩, mul_div_cancel_left₀ _ hD]
  rw [heq]
  ring

/-- Restoration and residue of the original horizon current. -/
theorem physicalTemporalCurrent_horizon_restoration_and_residue (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ R B : ℝ, ∃ c₀ c₁ : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1 / 2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        AnalyticAt ℂ (QuadraticEndpointMellin.finitePart
          (clearedDensityProfile q branch a zang) c₀ c₁ b)
          (physicalFundamentalFrequency q side) ∧
        Tendsto (fun w => (w - physicalFundamentalFrequency q side) *
          (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b w /
            reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch)))
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) / physicalFundamentalDenominatorSlope q branch side)) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          connection w (physicalRadialFrequency q) ≠ 0 →
          Tendsto (fun e : ℝ =>
            (∫ z in e..b, continuedTemporalRadialDensity q branch a zang w z) +
            (c₀ w * (e : ℂ) ^ w / w + c₁ w * (e : ℂ) ^ (w + 1) / (w + 1)) /
              reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch))
            (𝓝[>] (0:ℝ))
            (𝓝 (QuadraticEndpointMellin.finitePart
              (clearedDensityProfile q branch a zang) c₀ c₁ b w /
              reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch))) := by
  obtain ⟨R, B, c₀, c₁, hR, hB, hBh, _, hrest⟩ :=
    physicalTemporalCurrent_horizon_restoration_data q branch side a zang
  exact ⟨R, B, c₀, c₁, hR, hB, hBh, hrest⟩

end
end RHTower.D4BMJointSource
