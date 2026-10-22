import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalOppositeCurrentRestoration

/-! The complete original normalizable temporal current has one common restored horizon integral. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Both source-derived horizon finite parts with the actual normalizable-mode coefficients. -/
def normalizableTemporalHorizonFinitePart (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (c₀ c₁ d : ℂ → ℂ) (b : ℝ) (w : ℂ) : ℂ :=
  horizonRegularCoefficient w (physicalRadialFrequency q) (normalizable w (physicalRadialFrequency q))
    (normalizableFirst w (physicalRadialFrequency q)) *
    (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b w /
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch)) +
  LogarithmicEndpoint.finitePart (oppositeTemporalProfile q branch a zang) d b w

/-- One original normalizable current integral with both power terms and its logarithmic term. -/
def normalizableTemporalHorizonCutoff (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (c₀ c₁ d : ℂ → ℂ) (b : ℝ) (w : ℂ) (e : ℝ) : ℂ :=
  (∫ z in e..b, normalizableTemporalRadialDensity q branch a zang w z) +
  horizonRegularCoefficient w (physicalRadialFrequency q) (normalizable w (physicalRadialFrequency q))
    (normalizableFirst w (physicalRadialFrequency q)) *
    (c₀ w * (e : ℂ) ^ w / w + c₁ w * (e : ℂ) ^ (w + 1) / (w + 1)) /
      reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch) +
  d w * (Real.log e : ℂ)

/-- The full normalizable left-mode current is restored before its QNM residue is taken.
All source channels, the explicit lift and temporal source contact share the same cutoff. -/
theorem physicalNormalizableTemporalCurrent_horizon_restoration_data
    (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ R B : ℝ, ∃ c₀ c₁ d : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1 / 2 ∧
      (∃ C : ℝ, 0 ≤ C ∧ HasUniformJet2 (closedBall (physicalFundamentalFrequency q side) R) B
        (clearedDensityProfile q branch a zang) c₀ c₁ C) ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        Tendsto (fun w => (w - physicalFundamentalFrequency q side) *
          normalizableTemporalHorizonFinitePart q branch a zang c₀ c₁ d b w)
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) / physicalFundamentalDenominatorSlope q branch side)) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          connection w (physicalRadialFrequency q) ≠ 0 →
          Tendsto (normalizableTemporalHorizonCutoff q branch a zang c₀ c₁ d b w)
            (𝓝[>] (0:ℝ)) (𝓝 (normalizableTemporalHorizonFinitePart q branch a zang c₀ c₁ d b w)) := by
  let w₀ := physicalFundamentalFrequency q side
  let chi := physicalRadialFrequency q
  have hw : w₀.im ≠ 0 := (physicalFundamentalFrequency_strip q side).1
  have hwr : -2 < w₀.re := (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
  have hs : w₀ - 2 * physicalRate q branch ≠ 0 :=
    physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RI, BI, c₀, c₁, hRI, hBI, hBIh, hJ, hI⟩ :=
    physicalTemporalCurrent_horizon_restoration_data q branch side a zang
  obtain ⟨RO, BO, d, hRO, hBO, _, hO⟩ :=
    physicalOppositeTemporalCurrent_horizon_restoration q branch side a zang
  obtain ⟨RG, BG, CG, hRG, hBG, _, _, hG⟩ := horizonGauss_uniform_nonzero w₀ chi hw
  have hr : ∀ᶠ u : ℂ in 𝓝 w₀, -2 < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt hwr
  have hsource : ∀ᶠ u : ℂ in 𝓝 w₀, u - 2 * physicalRate q branch ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hs
  obtain ⟨RV, hRV, hvalid⟩ := Metric.eventually_nhds_iff.mp
    ((Complex.continuous_im.continuousAt.eventually_ne hw).and (hr.and hsource))
  let R := min RI (min RO (min RG RV))
  let B := min BI (min BO BG)
  have hR : 0 < R := lt_min hRI (lt_min hRO (lt_min hRG hRV))
  have hB : 0 < B := lt_min hBI (lt_min hBO hBG)
  have hRI' : R ≤ RI := min_le_left _ _
  have hRO' : R ≤ RO := (min_le_right _ _).trans (min_le_left _ _)
  have hRG' : R ≤ RG := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRV' : R ≤ RV := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBI' : B ≤ BI := min_le_left _ _
  have hBO' : B ≤ BO := (min_le_right _ _).trans (min_le_left _ _)
  have hBG' : B ≤ BG := (min_le_right _ _).trans (min_le_right _ _)
  have hA := normalizable_horizonRegularCoefficient_analyticAt w₀ chi hw
  have hf : w₀ = -3/2 - Complex.I * chi ∨ w₀ = -3/2 + Complex.I * chi := by
    dsimp only [w₀, chi]
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  have hAv := fundamental_horizonRegularCoefficient w₀ chi hw hf
  have hAlim := hA.continuousAt.tendsto.mono_left
    (show 𝓝[≠] w₀ ≤ 𝓝 w₀ from nhdsWithin_le_nhds)
  rw [hAv] at hAlim
  obtain ⟨C, hC, hJ⟩ := hJ
  refine ⟨R, B, c₀, c₁, d, hR, hB, hBI'.trans hBIh,
    ⟨C, hC, (hJ.mono (closedBall_subset_closedBall hRI')).mono_radius hBI'⟩, ?_⟩
  intro b hb hbB
  have hi := hI b hb (hbB.trans hBI')
  have ho := hO b hb (hbB.trans hBO')
  refine ⟨?_, ?_⟩
  · have hlim := (hAlim.mul hi.2.1).add ho.2.1
    simp only [one_mul, add_zero] at hlim
    apply hlim.congr'
    filter_upwards [] with u
    dsimp only [normalizableTemporalHorizonFinitePart]
    ring
  intro u hu hc
  have hudi := hi.2.2 u (ball_subset_ball hRI' hu) hc
  have hudo := ho.2.2 u (ball_subset_ball hRO' hu) hc
  let A := horizonRegularCoefficient u chi (normalizable u chi) (normalizableFirst u chi)
  have hlim := (hudi.const_mul A).add hudo
  apply hlim.congr'
  have heb : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e < b :=
    (show ∀ᶠ e : ℝ in 𝓝 (0:ℝ), e < b from Iio_mem_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, heb] with e he heb
  have huv := hvalid (mem_ball.mp (ball_subset_ball hRV' hu))
  have hb1 : b < 1 := by linarith [hbB.trans hBI', hBIh]
  have hg : ∀ z ∈ Icc e b, gaussProfile q u z ≠ 0 := by
    intro z hz
    have hn := (hG u (ball_subset_ball hRG' hu) z
      ⟨he.le.trans hz.1, hz.2.trans (hbB.trans hBG')⟩).2.1
    change (1/2 : ℝ) ≤ ‖gaussProfile q u z‖ at hn
    intro hzero
    rw [hzero, norm_zero] at hn
    linarith
  have hsplit := normalizableTemporalRadialDensity_integral_decomposition q branch a u zang
    huv.1 huv.2.1 huv.2.2 hc he heb.le hb1 hg
  dsimp only [normalizableTemporalHorizonCutoff]
  rw [hsplit]
  dsimp only [A, chi]
  ring

/-- Restoration and residue of the complete normalizable horizon current. -/
theorem physicalNormalizableTemporalCurrent_horizon_restoration_and_residue
    (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ R B : ℝ, ∃ c₀ c₁ d : ℂ → ℂ, 0 < R ∧ 0 < B ∧ B ≤ 1 / 2 ∧
      ∀ b : ℝ, 0 < b → b ≤ B →
        Tendsto (fun w => (w - physicalFundamentalFrequency q side) *
          normalizableTemporalHorizonFinitePart q branch a zang c₀ c₁ d b w)
          (𝓝[≠] physicalFundamentalFrequency q side)
          (𝓝 (QuadraticEndpointMellin.finitePart (clearedDensityProfile q branch a zang) c₀ c₁ b
            (physicalFundamentalFrequency q side) / physicalFundamentalDenominatorSlope q branch side)) ∧
        ∀ w ∈ ball (physicalFundamentalFrequency q side) R,
          connection w (physicalRadialFrequency q) ≠ 0 →
          Tendsto (normalizableTemporalHorizonCutoff q branch a zang c₀ c₁ d b w)
            (𝓝[>] (0:ℝ)) (𝓝 (normalizableTemporalHorizonFinitePart q branch a zang c₀ c₁ d b w)) := by
  obtain ⟨R, B, c₀, c₁, d, hR, hB, hBh, _, hrest⟩ :=
    physicalNormalizableTemporalCurrent_horizon_restoration_data q branch side a zang
  exact ⟨R, B, c₀, c₁, d, hR, hB, hBh, hrest⟩

end
end RHTower.D4BMJointSource
