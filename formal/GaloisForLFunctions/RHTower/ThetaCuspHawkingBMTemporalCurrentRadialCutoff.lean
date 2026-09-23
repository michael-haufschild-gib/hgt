import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensityBound
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialNorm
import GaloisForLFunctions.HTGeometry.SecondEndpointMellinLaurentInterchange
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# Radial cutoff of the horizon-mode temporal current

For frequencies near the fundamental quasinormal frequency the exterior radial integral of the
temporal current, cut off at a tortoise time `L`, is split at a fixed horizon coordinate `b`.
The compact part is an analytic function of the frequency by Cauchy domination; the horizon part
is, after the change of variables to the horizon coordinate, a two-counterterm endpoint Mellin
transform of the cleared density profile.  The cutoff integral plus the profile's own
counterterms therefore converges, and the limit is an explicit quotient by the clearing factor.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## Coordinate facts -/

theorem coordinateFirst_pos (t : ℝ) (ht : t < 0) : 0 < coordinateFirst t := by
  unfold coordinateFirst
  have h1 := (radialUnit_bounds t ht).1
  have h2 := (horizonCoordinate_interior t ht).1
  positivity

theorem horizonCoordinate_strictMonoOn : StrictMonoOn horizonCoordinate (Iio 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Iio 0) horizonCoordinate_continuous.continuousOn ?_
  intro t ht
  rw [interior_Iio] at ht
  rw [(horizonCoordinate_hasDerivAt t).deriv]
  exact coordinateFirst_pos t ht

theorem tortoiseOf_continuousAt_thetaCuspHawkingBMTemporalCurrentRadialCutoff {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) : ContinuousAt tortoiseOf z := by
  unfold tortoiseOf
  have hpos : 0 < Real.sqrt z / (1 + Real.sqrt (1 - z)) :=
    div_pos (Real.sqrt_pos.mpr hz.1) (by positivity)
  have hsq : ContinuousAt (fun z : ℝ => Real.sqrt (1 - z)) z :=
    Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub continuousAt_id)
  have hden : ContinuousAt (fun z : ℝ => 1 + Real.sqrt (1 - z)) z := continuousAt_const.add hsq
  have hq : ContinuousAt (fun z : ℝ => Real.sqrt z / (1 + Real.sqrt (1 - z))) z :=
    Real.continuous_sqrt.continuousAt.div hden (by positivity)
  exact ContinuousAt.comp (f := fun z : ℝ => Real.sqrt z / (1 + Real.sqrt (1 - z)))
    (Real.continuousAt_log hpos.ne') hq

/-! ## The density profile in the horizon coordinate -/

theorem clearedDensityCore_eq_density (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    clearedDensityCore q branch a zang u z =
      clearedTemporalDensity q branch a zang u (tortoiseOf z) / (z:ℂ) ^ u := by
  have hz0 : (z:ℂ) ^ u ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
  unfold clearedTemporalDensity
  rw [horizonCoordinate_tortoiseOf hz]
  field_simp

theorem clearedDensityProfile_continuousOn (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (hu : u.im ≠ 0) (hur : -2 < u.re) :
    ContinuousOn (clearedDensityProfile q branch a zang u) (Ioo 0 1) := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  have hcore : ContinuousAt (clearedDensityCore q branch a zang u) z := by
    have h1 : ContinuousAt (fun z : ℝ => clearedTemporalDensity q branch a zang u (tortoiseOf z)) z :=
      (((clearedTemporalDensity_continuousOn q branch a zang u hu hur) (tortoiseOf z)
        (tortoiseOf_neg hz)).continuousAt (Iio_mem_nhds (tortoiseOf_neg hz))).comp
        (tortoiseOf_continuousAt_thetaCuspHawkingBMTemporalCurrentRadialCutoff hz)
    have h2 : ContinuousAt (fun z : ℝ => (z:ℂ) ^ u) z :=
      Complex.continuousAt_ofReal_cpow_const z u (Or.inr hz.1.ne')
    have h3 : (z:ℂ) ^ u ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hz.1.ne'))
    refine (h1.div h2 h3).congr ?_
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with r hr
    exact (clearedDensityCore_eq_density q branch a zang u hr).symm
  have hsq : ContinuousAt (fun z : ℝ => (((Real.sqrt (1 - z))⁻¹ : ℝ) : ℂ)) z := by
    have hne : Real.sqrt (1 - z) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [hz.2])).ne'
    have h : ContinuousAt (fun z : ℝ => Real.sqrt (1 - z)) z :=
      Real.continuous_sqrt.continuousAt.comp (continuousAt_const.sub continuousAt_id)
    exact Complex.continuous_ofReal.continuousAt.comp (h.inv₀ hne)
  unfold clearedDensityProfile
  exact ((hcore.mul hsq).div_const 2).congr
    (Filter.Eventually.of_forall (fun r => by simp only [Pi.mul_apply, Complex.ofReal_inv]))

/-! ## The patched profile -/

/-- The cleared density profile, patched by its constant horizon coefficient and frozen beyond
the horizon radius `b`. -/
def patchedProfile (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (c₀ : ℂ → ℂ) (b : ℝ) (u : ℂ) (z : ℝ) : ℂ :=
  if z ≤ 0 then c₀ u else clearedDensityProfile q branch a zang u (min z b)

theorem patchedProfile_of_mem (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (c₀ : ℂ → ℂ) (b : ℝ) (u : ℂ) {z : ℝ} (hz : z ∈ Ioc (0:ℝ) b) :
    patchedProfile q branch a zang c₀ b u z = clearedDensityProfile q branch a zang u z := by
  simp only [patchedProfile, if_neg (not_le.mpr hz.1), min_eq_left hz.2]

theorem patchedProfile_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (c₀ : ℂ → ℂ) (b : ℝ) (u : ℂ) : patchedProfile q branch a zang c₀ b u 0 = c₀ u := by
  simp [patchedProfile]

theorem patchedProfile_measurable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (c₀ : ℂ → ℂ) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) (u : ℂ)
    (hu : u.im ≠ 0) (hur : -2 < u.re) :
    Measurable (patchedProfile q branch a zang c₀ b u) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro z hz
  have hz' : z ≠ 0 := hz
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_or_gt_of_ne hz' with hneg | hpos
  · have he : (fun _ : ℝ => c₀ u) =ᶠ[𝓝 z] patchedProfile q branch a zang c₀ b u := by
      filter_upwards [Iio_mem_nhds hneg] with r hr
      simp [patchedProfile, (mem_Iio.mp hr).le]
    exact continuousAt_const.congr he
  · have hmin : ContinuousAt (fun r : ℝ => min r b) z := continuousAt_id.min continuousAt_const
    have hmem : min z b ∈ Ioo (0:ℝ) 1 := ⟨lt_min hpos hb.1, (min_le_right _ _).trans_lt hb.2⟩
    have hcont : ContinuousAt (fun r : ℝ => clearedDensityProfile q branch a zang u (min r b)) z :=
      ContinuousAt.comp (f := fun r : ℝ => min r b)
        (((clearedDensityProfile_continuousOn q branch a zang u hu hur) _ hmem).continuousAt
          (Ioo_mem_nhds hmem.1 hmem.2)) hmin
    refine hcont.congr ?_
    filter_upwards [Ioi_mem_nhds hpos] with r hr
    simp [patchedProfile, not_le.mpr (mem_Ioi.mp hr)]

/-! ## The compact part -/

/-- The exterior integral of the cleared density between the horizon radius `b` and infinity. -/
def compactPart (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point) (b : ℝ)
    (u : ℂ) : ℂ :=
  ∫ t in Ioo (tortoiseOf b) 0, clearedTemporalDensity q branch a zang u t

theorem compactPart_analyticAt (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (b : ℝ) :
    AnalyticAt ℂ (compactPart q branch a zang b) (physicalFundamentalFrequency q side) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RB, CB, hRB, -, hbound⟩ :=
    clearedTemporalDensity_outer_uniform_bound q branch side a zang (tortoiseOf b)
  have hev : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u.im ≠ 0 ∧ -2 < u.re ∧ u - 2 * physicalRate q branch ≠ 0 ∧
      (∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) ∧
      u ∈ ball (physicalFundamentalFrequency q side) RB := by
    refine Filter.Eventually.and (Complex.continuous_im.continuousAt.eventually_ne hw.1)
      (Filter.Eventually.and (continuousAt_const.eventually_lt Complex.continuous_re.continuousAt
        (abs_lt.mp hw.2).1) (Filter.Eventually.and
        ((continuous_id.sub continuous_const).continuousAt.eventually_ne hs0)
        (Filter.Eventually.and ?_ (ball_mem_nhds _ hRB))))
    have h3 : ∀ i : Fin 3, ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
        connection u (principalFrequency q i) ≠ 0 := fun i =>
      (connection_frequency_analyticAt _ (principalFrequency q i) hw.1).continuousAt.eventually_ne
        (physicalFundamental_principal_connection_ne_zero q side i)
    exact Filter.eventually_all.mpr h3
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp hev
  have hmeas : ∀ u ∈ ball (physicalFundamentalFrequency q side) r, AEStronglyMeasurable
      ((Ioo (tortoiseOf b) 0).indicator (fun t => clearedTemporalDensity q branch a zang u t))
      volume := by
    intro u hu
    obtain ⟨hui, hur, -, -, -⟩ := hall (mem_ball.mp hu)
    refine (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr ?_
    exact ((clearedTemporalDensity_continuousOn q branch a zang u hui hur).mono
      (fun t ht => ht.2)).aestronglyMeasurable measurableSet_Ioo
  have hdiff : ∀ t : ℝ, DifferentiableOn ℂ (fun u =>
      (Ioo (tortoiseOf b) 0).indicator (fun t => clearedTemporalDensity q branch a zang u t) t)
      (ball (physicalFundamentalFrequency q side) r) := by
    intro t u hu
    by_cases ht : t ∈ Ioo (tortoiseOf b) 0
    · simp only [indicator_of_mem ht]
      obtain ⟨hui, hur, hus, hcp, -⟩ := hall (mem_ball.mp hu)
      exact (clearedTemporalDensity_frequency_analyticAt q branch a zang u hui hur hus hcp t
        ht.2).differentiableAt.differentiableWithinAt
    · simp only [indicator_of_notMem ht]
      exact (differentiableAt_const _).differentiableWithinAt
  have hB : ∀ t : ℝ, ∀ u ∈ ball (physicalFundamentalFrequency q side) r,
      ‖(Ioo (tortoiseOf b) 0).indicator (fun t => clearedTemporalDensity q branch a zang u t) t‖ ≤
        (Ioo (tortoiseOf b) 0).indicator (fun _ => CB) t := by
    intro t u hu
    by_cases ht : t ∈ Ioo (tortoiseOf b) 0
    · simp only [indicator_of_mem ht]
      exact hbound u (hall (mem_ball.mp hu)).2.2.2.2 t ⟨ht.1.le, ht.2⟩
    · simp only [indicator_of_notMem ht, norm_zero, le_refl]
  have hi : Integrable ((Ioo (tortoiseOf b) 0).indicator (fun _ => CB)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have hDI : DifferentiableOn ℂ (fun u => ∫ t,
      (Ioo (tortoiseOf b) 0).indicator (fun t => clearedTemporalDensity q branch a zang u t) t)
      (ball (physicalFundamentalFrequency q side) r) := by
    intro v hv
    obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr'
      (fun u hu => hmeas u (hsub hu)) (fun t => (hdiff t).mono hsub)
      (fun t u hu => hB t u (hsub hu)) hi).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball (physicalFundamentalFrequency q side) (mem_ball_self hr)
  simpa only [compactPart, integral_indicator measurableSet_Ioo] using! hA

/-! ## The split of the cutoff integral -/

theorem cutoff_integral_split (q : XiZeroCopy) (branch : Bool) (a : ℂ) (zang : D4BMHorizon.Point)
    (c₀ : ℂ → ℂ) {b : ℝ} (hb : b ∈ Ioo (0:ℝ) 1) (u : ℂ) (hu : u.im ≠ 0) (hur : -2 < u.re)
    (hs : u - 2 * physicalRate q branch ≠ 0) (hc : connection u (physicalRadialFrequency q) ≠ 0)
    {CB : ℝ} (hbd : ∀ t ∈ Ico (tortoiseOf b) (0:ℝ), ‖clearedTemporalDensity q branch a zang u t‖ ≤ CB)
    {L : ℝ} (hL : L < tortoiseOf b) :
    (∫ t in L..0, ((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) * continuedPhysicalTimeAction q branch u a false t zang) =
      ((∫ z in Ioc (horizonCoordinate L) b, (z:ℂ) ^ (u - 1) * patchedProfile q branch a zang c₀ b u z) +
        compactPart q branch a zang b u) /
        reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) := by
  have hTb : tortoiseOf b < 0 := tortoiseOf_neg hb
  have hL0 : L < 0 := hL.trans hTb
  have hcF : reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) ≠ 0 := by
    unfold reducedGreenClearingFactor
    exact mul_ne_zero (neg_ne_zero.mpr hs) hc
  have hcont := clearedTemporalDensity_continuousOn q branch a zang u hu hur
  have h1 : (∫ t in L..0, ((tortoiseRadius t:ℂ) ^ (2 : ℕ) - 1) *
      continuedPhysicalTimeAction q branch u a false t zang) =
      (∫ t in L..0, clearedTemporalDensity q branch a zang u t) /
        reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hL0.le] at ht
    dsimp only
    rw [← clearedTemporalDensity_eq_current q branch a zang u hs hc t ht.2]
    field_simp
  have hint1 : IntervalIntegrable (clearedTemporalDensity q branch a zang u) volume L (tortoiseOf b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hL.le]
    exact hcont.mono (fun t ht => lt_of_le_of_lt ht.2 hTb)
  have hint2 : IntervalIntegrable (clearedTemporalDensity q branch a zang u) volume (tortoiseOf b) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTb.le, integrableOn_Ioc_iff_integrableOn_Ioo]
    refine (integrableOn_const (C := CB) (by simp)).mono'
      ((hcont.mono (fun t ht => ht.2)).aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ (fun t ht => hbd t ⟨ht.1.le, ht.2⟩)
  have h2 : (∫ t in L..0, clearedTemporalDensity q branch a zang u t) =
      (∫ t in L..tortoiseOf b, clearedTemporalDensity q branch a zang u t) +
        ∫ t in tortoiseOf b..0, clearedTemporalDensity q branch a zang u t :=
    (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
  have h3 : (∫ t in tortoiseOf b..0, clearedTemporalDensity q branch a zang u t) =
      compactPart q branch a zang b u := by
    rw [intervalIntegral.integral_of_le hTb.le, compactPart]
    exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
  have hzL : horizonCoordinate L < b := by
    have := horizonCoordinate_strictMonoOn (show L ∈ Iio (0:ℝ) from hL0)
      (show tortoiseOf b ∈ Iio (0:ℝ) from hTb) hL
    rwa [horizonCoordinate_tortoiseOf hb] at this
  have h4 : (∫ t in L..tortoiseOf b, clearedTemporalDensity q branch a zang u t) =
      ∫ z in Ioc (horizonCoordinate L) b, (z:ℂ) ^ (u - 1) * patchedProfile q branch a zang c₀ b u z := by
    have hcv := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (f := horizonCoordinate)
      (f' := coordinateFirst)
      (g := fun z : ℝ => (z:ℂ) ^ (u - 1) * clearedDensityProfile q branch a zang u z)
      (a := L) (b := tortoiseOf b) horizonCoordinate_continuous.continuousOn
      (fun t _ => horizonCoordinate_hasDerivAt t)
      (fun t ht => by
        have ht0 : t < 0 := by
          rw [max_eq_right hL.le] at ht
          exact ht.2.trans hTb
        exact (coordinateFirst_pos t ht0).le)
    rw [horizonCoordinate_tortoiseOf hb] at hcv
    have hlhs : (∫ t in L..tortoiseOf b, coordinateFirst t •
        ((fun z : ℝ => (z:ℂ) ^ (u - 1) * clearedDensityProfile q branch a zang u z) ∘
          horizonCoordinate) t) =
        ∫ t in L..tortoiseOf b, clearedTemporalDensity q branch a zang u t := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le hL.le] at ht
      have ht0 : t < 0 := ht.2.trans hTb
      have hz := horizonCoordinate_interior t ht0
      have hz0 : (horizonCoordinate t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
      have hr0 : (radialUnit t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (radialUnit_bounds t ht0).1.ne'
      simp only [Function.comp, Complex.real_smul, clearedDensityProfile, clearedTemporalDensity,
        coordinateFirst]
      rw [← radialUnit_eq_sqrt t ht0, Complex.cpow_sub _ _ hz0, Complex.cpow_one]
      push_cast
      field_simp
      try ring
    rw [← hlhs, hcv, intervalIntegral.integral_of_le hzL.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [patchedProfile_of_mem q branch a zang c₀ b u
      ⟨(horizonCoordinate_interior L hL0).1.trans hz.1, hz.2⟩]
  rw [h1, h2, h3, h4]

end
end RHTower.D4BMJointSource
