import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentRadialPackage
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalSlope
import GaloisForLFunctions.HTGeometry.JetCoefficientUniqueness
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Laurent extraction through the renormalized radial finite part

The renormalized radial finite part of the horizon-mode temporal current is meromorphic at the
fundamental quasinormal frequency with a simple pole, and its residue is exactly the radial
finite part of the temporal residue: the order `-1` Laurent coefficient of the renormalized
radial integral equals `physicalRadialResidueFinitePart`.  The identification passes through the
value of the cleared density at the quasinormal frequency, which is the clearing slope times the
residue density; the horizon jet of that density then fixes the counterterm coefficients, and
the two-counterterm Mellin transform is evaluated against the corpus's horizon-subtracted mode
square.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction D4BMFundamentalNorm GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## The clearing slope -/

/-- The difference quotient of the clearing factor at the fundamental quasinormal frequency. -/
def clearingSlope (q : XiZeroCopy) (branch side : Bool) : ℂ → ℂ :=
  dslope (fun u => reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
    (physicalFundamentalFrequency q side)

theorem clearingSlope_analyticAt (q : XiZeroCopy) (branch side : Bool) :
    AnalyticAt ℂ (clearingSlope q branch side) (physicalFundamentalFrequency q side) := by
  obtain ⟨p, hp⟩ := reducedGreenClearingFactor_analyticAt (physicalFundamentalFrequency q side)
    (physicalRadialFrequency q) (physicalRate q branch) (physicalFundamentalFrequency_strip q side).1
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem clearingFactor_fundamental_zero (q : XiZeroCopy) (branch side : Bool) :
    reducedGreenClearingFactor (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
      (physicalRate q branch) = 0 := by
  unfold reducedGreenClearingFactor
  rw [physicalFundamentalFrequency_connection_zero, mul_zero]

theorem clearingFactor_eq_slope_mul (q : XiZeroCopy) (branch side : Bool) (u : ℂ)
    (hu : u ≠ physicalFundamentalFrequency q side) :
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) =
      clearingSlope q branch side u * (u - physicalFundamentalFrequency q side) := by
  unfold clearingSlope
  rw [dslope_of_ne _ hu, slope_def_field, clearingFactor_fundamental_zero, sub_zero]
  field_simp [sub_ne_zero.mpr hu]

theorem clearingSlope_fundamental (q : XiZeroCopy) (branch side : Bool) :
    clearingSlope q branch side (physicalFundamentalFrequency q side) =
      physicalFundamentalDenominatorSlope q branch side := by
  unfold clearingSlope
  rw [dslope_same]
  have hd : HasDerivAt (fun u => reducedGreenClearingFactor u (physicalRadialFrequency q)
      (physicalRate q branch))
      (-1 * connection (physicalFundamentalFrequency q side) (physicalRadialFrequency q) +
        -(physicalFundamentalFrequency q side - 2 * physicalRate q branch) *
          connectionSimpleSlope (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side)
      (physicalFundamentalFrequency q side) := by
    unfold reducedGreenClearingFactor
    exact (((hasDerivAt_id' _).sub_const (2 * physicalRate q branch)).neg).mul
      (physicalFundamental_connection_hasDerivAt q side)
  rw [hd.deriv, physicalFundamentalFrequency_connection_zero]
  unfold physicalFundamentalDenominatorSlope
  ring

/-! ## The cleared density at the quasinormal frequency -/

/-- At the quasinormal frequency the cleared density is the clearing slope times the radial
residue density. -/
theorem clearedTemporalDensity_fundamental (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (t : ℝ) (ht : t < 0) :
    clearedTemporalDensity q branch a zang (physicalFundamentalFrequency q side) t =
      clearingSlope q branch side (physicalFundamentalFrequency q side) *
        (physicalRadialResidueFactor q branch side a zang *
          mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ)) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < (physicalFundamentalFrequency q side).re := (abs_lt.mp hw.2).1
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hcp0 := physicalFundamental_principal_connection_ne_zero q side
  have hκ := clearingSlope_analyticAt q branch side
  have hres := continuedPhysicalTimeAction_residue q branch side a false t ht zang
  have h1 : Tendsto (fun u => clearingSlope q branch side u *
      (((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) * ((u - physicalFundamentalFrequency q side) *
        continuedPhysicalTimeAction q branch u a false t zang)))
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (clearingSlope q branch side (physicalFundamentalFrequency q side) *
        (((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) * physicalTimeResidue q branch side a false t zang))) :=
    (hκ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (hres.const_mul _)
  have hsev : ∀ᶠ u in 𝓝[≠] physicalFundamentalFrequency q side,
      u - 2 * physicalRate q branch ≠ 0 :=
    ((continuous_id.sub continuous_const).continuousAt.eventually_ne hs0).filter_mono
      nhdsWithin_le_nhds
  have h2 : ∀ᶠ u in 𝓝[≠] physicalFundamentalFrequency q side,
      clearingSlope q branch side u * (((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) *
        ((u - physicalFundamentalFrequency q side) *
          continuedPhysicalTimeAction q branch u a false t zang)) =
        clearedTemporalDensity q branch a zang u t := by
    filter_upwards [self_mem_nhdsWithin,
      connection_eventually_ne_zero _ (physicalRadialFrequency q) hw.1, hsev] with u hu hcu hsu
    rw [← clearedTemporalDensity_eq_current q branch a zang u hsu hcu t ht,
      clearingFactor_eq_slope_mul q branch side u (mem_compl_singleton_iff.mp hu)]
    ring
  have h3 : Tendsto (fun u => clearedTemporalDensity q branch a zang u t)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (clearedTemporalDensity q branch a zang (physicalFundamentalFrequency q side) t)) :=
    (clearedTemporalDensity_frequency_analyticAt q branch a zang _ hw.1 hwr hs0 hcp0 t
      ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [tendsto_nhds_unique h3 (h1.congr' h2),
    physicalTimeResidue_radial_density q branch side a false t ht zang]

/-- At the quasinormal frequency the cleared density profile is a multiple of `√(1-z)/2`. -/
theorem clearedDensityProfile_fundamental (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z =
      clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang * ((Real.sqrt (1 - z) : ℂ) / 2) := by
  have ht := tortoiseOf_neg hz
  have hz0 : (z:ℂ) ^ physicalFundamentalFrequency q side ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
  have hsq : (Real.sqrt (1 - z) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by linarith [hz.2])).ne'
  unfold clearedDensityProfile
  rw [clearedDensityCore_eq_density q branch a zang _ hz,
    clearedTemporalDensity_fundamental q branch side a zang _ ht, mode_square _ _ ht,
    radialUnit_eq_sqrt _ ht, horizonCoordinate_tortoiseOf hz]
  field_simp
  try ring

/-! ## The horizon jet coefficients at the quasinormal frequency -/

theorem jet_coefficients_fundamental (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) {b C : ℝ} (hb : 0 < b) (hbh : b ≤ 1 / 2) {c₀ c₁ : ℂ}
    (hjet : ∀ z ∈ Ioc (0:ℝ) b,
      ‖clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z - c₀ - c₁ * z‖ ≤
        C * z ^ (2 : ℕ)) :
    c₀ = clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang / 2 ∧
      c₁ = -(clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang) / 4 := by
  have hK := eq_zero_of_norm_add_mul_le_mul_sq
    (α := clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang / 2 - c₀)
    (β := -(clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang) / 4 - c₁)
    (C := C + ‖clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang / 2‖ / 4) hb (fun z hz => ?_)
  · exact ⟨(sub_eq_zero.mp hK.1).symm, (sub_eq_zero.mp hK.2).symm⟩
  have hzI : z ∈ Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2]⟩
  have hP := clearedDensityProfile_fundamental q branch side a zang hzI
  have hsq := abs_sqrt_one_sub_sub_le hz.1.le (hz.2.trans hbh)
  have hcast : ((Real.sqrt (1 - z) : ℂ) - (1 - (z:ℂ) / 2)) =
      ((Real.sqrt (1 - z) - (1 - z / 2) : ℝ) : ℂ) := by push_cast; ring
  have hsqn : ‖(Real.sqrt (1 - z) : ℂ) - (1 - (z:ℂ) / 2)‖ ≤ z ^ (2 : ℕ) / 4 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hsq
  have hj := hjet z hz
  rw [hP] at hj
  have hid : (clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang / 2 - c₀) +
      (-(clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang) / 4 - c₁) * z =
      (clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang * ((Real.sqrt (1 - z) : ℂ) / 2) - c₀ - c₁ * z) -
      (clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang / 2) *
        ((Real.sqrt (1 - z) : ℂ) - (1 - (z:ℂ) / 2)) := by ring
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  calc _ ≤ C * z ^ (2 : ℕ) + ‖clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang / 2‖ * (z ^ (2 : ℕ) / 4) :=
        add_le_add hj (mul_le_mul_of_nonneg_left hsqn (norm_nonneg _))
    _ = _ := by ring

/-! ## The Mellin part at the quasinormal frequency -/

theorem mode_square_weight_continuousOn (w : ℂ) {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun z : ℝ => (z:ℂ) ^ (w - 1) * (Real.sqrt (1 - z) : ℂ)) (Icc c 1) := by
  intro z hz
  have hz0 : z ≠ 0 := (hc.trans_le hz.1).ne'
  refine ContinuousAt.continuousWithinAt ?_
  exact (Complex.continuousAt_ofReal_cpow_const z (w - 1) (Or.inr hz0)).mul
    (Complex.continuous_ofReal.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub continuousAt_id)))

/-- The horizon-mode square integrated from `L` to the tortoise time of `b`. -/
theorem mode_square_integral_upto (w : ℂ) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) {L : ℝ}
    (hL : L < tortoiseOf b) :
    (∫ t in L..tortoiseOf b, mode w t ^ (2 : ℕ)) =
      (1 / 2 : ℂ) * ∫ z in Ioc (horizonCoordinate L) b, (z:ℂ) ^ (w - 1) * (Real.sqrt (1 - z) : ℂ) := by
  have hTb : tortoiseOf b < 0 := tortoiseOf_neg hb
  have hL0 : L < 0 := hL.trans hTb
  have hzL : horizonCoordinate L < b := by
    have := horizonCoordinate_strictMonoOn (show L ∈ Iio (0:ℝ) from hL0)
      (show tortoiseOf b ∈ Iio (0:ℝ) from hTb) hL
    rwa [horizonCoordinate_tortoiseOf hb] at this
  have hzL0 : 0 < horizonCoordinate L := (horizonCoordinate_interior L hL0).1
  have h1 := mode_square_integral w L hL0
  have h2 := mode_square_integral w (tortoiseOf b) hTb
  rw [horizonCoordinate_tortoiseOf hb] at h2
  have hsplit : (∫ t in L..0, mode w t ^ (2 : ℕ)) =
      (∫ t in L..tortoiseOf b, mode w t ^ (2 : ℕ)) + ∫ t in tortoiseOf b..0, mode w t ^ (2 : ℕ) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (mode_square_intervalIntegrable w L hL0).mono_set
        (uIcc_subset_uIcc_left (by rw [uIcc_of_le hL0.le]; exact ⟨hL.le, hTb.le⟩))
    · exact (mode_square_intervalIntegrable w (tortoiseOf b) hTb)
  have hzsplit : (∫ z in horizonCoordinate L..1, (z:ℂ) ^ (w - 1) * (Real.sqrt (1 - z) : ℂ)) =
      (∫ z in horizonCoordinate L..b, (z:ℂ) ^ (w - 1) * (Real.sqrt (1 - z) : ℂ)) +
        ∫ z in b..1, (z:ℂ) ^ (w - 1) * (Real.sqrt (1 - z) : ℂ) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hzL.le]
      exact (mode_square_weight_continuousOn w hzL0).mono
        (fun z hz => ⟨hz.1, hz.2.trans hb.2.le⟩)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hb.2.le]
      exact (mode_square_weight_continuousOn w hb.1).mono (fun z hz => hz)
  rw [← intervalIntegral.integral_of_le hzL.le]
  linear_combination h1 - h2 + (-1:ℂ) * hsplit + (1 / 2 : ℂ) * hzsplit

/-- The Mellin part at the quasinormal frequency, from the endpoint limit and the corpus's
horizon-subtracted mode square. -/
theorem mellin_fundamental (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) {c₀ c₁ Mw : ℂ}
    (hc₀ : c₀ = clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang / 2)
    (hc₁ : c₁ = -(clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang) / 4)
    (hT : Tendsto (fun ε : ℝ => (∫ z in Ioc ε b, (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) *
        clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z) +
        c₀ * (ε:ℂ) ^ (physicalFundamentalFrequency q side) / physicalFundamentalFrequency q side +
        c₁ * (ε:ℂ) ^ (physicalFundamentalFrequency q side + 1) /
          (physicalFundamentalFrequency q side + 1)) (𝓝[>] 0) (𝓝 Mw)) :
    Mw = clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang *
      (normFinitePart (physicalFundamentalFrequency q side) -
        ∫ t in tortoiseOf b..0, mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ)) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hwr : -2 < (physicalFundamentalFrequency q side).re := (abs_lt.mp hw.2).1
  have hw0 : physicalFundamentalFrequency q side ≠ 0 := by
    intro he; apply hw.1; simp [he]
  have hw1 : physicalFundamentalFrequency q side + 1 ≠ 0 := by
    intro he; apply hw.1
    have := congrArg Complex.im he
    simpa using this
  have hTb : tortoiseOf b < 0 := tortoiseOf_neg hb
  have hA := hT.comp horizonCoordinate_tendsto_positive
  have hB := ((mode_square_cutoff_tendsto (physicalFundamentalFrequency q side) hwr hw0 hw1).sub
    (tendsto_const_nhds (x := ∫ t in tortoiseOf b..0,
      mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ)))).const_mul
    (clearingSlope q branch side (physicalFundamentalFrequency q side) *
      physicalRadialResidueFactor q branch side a zang)
  refine tendsto_nhds_unique hA (hB.congr' ?_)
  filter_upwards [eventually_lt_atBot (tortoiseOf b)] with L hL
  have hL0 : L < 0 := hL.trans hTb
  have hsplit : (∫ t in L..0, mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ)) =
      (∫ t in L..tortoiseOf b, mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ)) +
        ∫ t in tortoiseOf b..0, mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ) := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (mode_square_intervalIntegrable _ L hL0).mono_set
        (uIcc_subset_uIcc_left (by rw [uIcc_of_le hL0.le]; exact ⟨hL.le, hTb.le⟩))
    · exact mode_square_intervalIntegrable _ (tortoiseOf b) hTb
  have hI : (∫ z in Ioc (horizonCoordinate L) b, (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) *
      clearedDensityProfile q branch a zang (physicalFundamentalFrequency q side) z) =
      clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang *
        ((1 / 2 : ℂ) * ∫ z in Ioc (horizonCoordinate L) b,
          (z:ℂ) ^ (physicalFundamentalFrequency q side - 1) * (Real.sqrt (1 - z) : ℂ)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    have hzI : z ∈ Ioo (0:ℝ) 1 :=
      ⟨(horizonCoordinate_interior L hL0).1.trans hz.1, hz.2.trans_lt hb.2⟩
    dsimp only
    rw [clearedDensityProfile_fundamental q branch side a zang hzI]
    ring
  simp only [Function.comp_apply, counterterm]
  rw [hI, ← mode_square_integral_upto _ hb hL, hsplit, hc₀, hc₁]
  field_simp
  ring

/-! ## The Laurent coefficient -/

/-- **Laurent extraction through the renormalized radial finite part, horizon-mode leg.**
Near the fundamental quasinormal frequency the cutoff radial integral of the horizon-mode
temporal current, with the two counterterms read off from the horizon jet of the cleared density
profile, converges to a function `Φ` of the frequency; `Φ` is meromorphic at the quasinormal
frequency and its order `-1` Laurent coefficient is the radial finite part of the temporal
residue. -/
theorem continuedPhysicalTimeAction_horizon_radial_laurent (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    ∃ (c₀ c₁ Φ : ℂ → ℂ),
      AnalyticAt ℂ c₀ (physicalFundamentalFrequency q side) ∧
      AnalyticAt ℂ c₁ (physicalFundamentalFrequency q side) ∧
      (∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ᶠ u in 𝓝 (physicalFundamentalFrequency q side),
        ∀ z ∈ Ioc (0:ℝ) b,
          ‖clearedDensityProfile q branch a zang u z - c₀ u - c₁ u * z‖ ≤ C * z ^ (2 : ℕ)) ∧
      (∀ᶠ u in 𝓝[≠] (physicalFundamentalFrequency q side), Tendsto (fun L : ℝ =>
        (∫ t in L..0, ((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) *
          continuedPhysicalTimeAction q branch u a false t zang) +
          (c₀ u * (horizonCoordinate L:ℂ) ^ u / u + c₁ u * (horizonCoordinate L:ℂ) ^ (u + 1) / (u + 1)) /
            reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
        atBot (𝓝 (Φ u))) ∧
      MeromorphicAt Φ (physicalFundamentalFrequency q side) ∧
      laurentCoeff Φ (physicalFundamentalFrequency q side) (-1) =
        physicalRadialResidueFinitePart q branch side a zang := by
  have hw := physicalFundamentalFrequency_strip q side
  obtain ⟨b, c₀, c₁, Mel, hb, hbh, h₀, h₁, hMel, hcp, ⟨C, hC, hjet⟩, hcut, hT⟩ :=
    radial_cutoff_package q branch side a zang
  have hbI : b ∈ Ioo (0:ℝ) 1 := ⟨hb, by linarith⟩
  have hTb : tortoiseOf b < 0 := tortoiseOf_neg hbI
  have hκ := clearingSlope_analyticAt q branch side
  have hκ0 : clearingSlope q branch side (physicalFundamentalFrequency q side) ≠ 0 := by
    rw [clearingSlope_fundamental]
    exact physicalFundamental_denominatorSlope_ne_zero q branch side
  have hcF := reducedGreenClearingFactor_analyticAt (physicalFundamentalFrequency q side)
    (physicalRadialFrequency q) (physicalRate q branch) hw.1
  have hΦmero : MeromorphicAt (fun u => (Mel u + compactPart q branch a zang b u) /
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch))
      (physicalFundamentalFrequency q side) :=
    (hMel.add hcp).meromorphicAt.div hcF.meromorphicAt
  refine ⟨c₀, c₁, fun u => (Mel u + compactPart q branch a zang b u) /
    reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch),
    h₀, h₁, ⟨b, C, hb, hC, hjet⟩, hcut, hΦmero, ?_⟩
  have hΨ : AnalyticAt ℂ (fun u => (Mel u + compactPart q branch a zang b u) /
      clearingSlope q branch side u) (physicalFundamentalFrequency q side) :=
    (hMel.add hcp).div hκ hκ0
  have hev : (fun u => (Mel u + compactPart q branch a zang b u) /
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)) =ᶠ[𝓝[≠]
        physicalFundamentalFrequency q side]
      fun u => (Mel u + compactPart q branch a zang b u) / clearingSlope q branch side u /
        (u - physicalFundamentalFrequency q side) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [clearingFactor_eq_slope_mul q branch side u (mem_compl_singleton_iff.mp hu), div_div]
  rw [laurentCoeff_congr hΦmero hev (-1), laurentCoeff_analytic_div_sub hΨ]
  -- evaluate the numerator at the quasinormal frequency
  obtain ⟨hc₀, hc₁⟩ := jet_coefficients_fundamental q branch side a zang hb hbh hjet.self_of_nhds
  have hM := mellin_fundamental q branch side a zang hbI hc₀ hc₁ hT
  have hcp0 : compactPart q branch a zang b (physicalFundamentalFrequency q side) =
      clearingSlope q branch side (physicalFundamentalFrequency q side) *
        physicalRadialResidueFactor q branch side a zang *
        ∫ t in tortoiseOf b..0, mode (physicalFundamentalFrequency q side) t ^ (2 : ℕ) := by
    unfold compactPart
    rw [intervalIntegral.integral_of_le hTb.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp only
    rw [clearedTemporalDensity_fundamental q branch side a zang t ht.2]
    ring
  rw [hM, hcp0]
  unfold physicalRadialResidueFinitePart
  field_simp
  ring

end
end RHTower.D4BMJointSource
