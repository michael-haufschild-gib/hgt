import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalNormalizableCurrentDensity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensityBound

/-! The complete opposite temporal current on the outer radial interval. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric MeasureTheory D4BMLaplaceRadial D4BMModularCore
  D4BMJointWave D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- The actual opposite coefficient after cancellation against the self-channel clearing factor,
with the complete original cleared source and the opposite homogeneous mode. -/
def oppositeTemporalOuterDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (t : ℝ) : ℂ :=
  oppositeCurrentRatio q branch u *
    (modeAngularSquare (physicalModeAngularJet q zang) *
      ((-2*u*(physicalAngularParameter q^(2 : ℕ)-1/4-2)*selfExpression q branch a u t -
        u*contactExpression q branch a u t) * tortoiseMode false (-u) (physicalRadialFrequency q) t))

/-- The analytic density is the actual omitted part of the original normalizable temporal current. -/
theorem oppositeTemporalOuterDensity_eq_original (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (hu : u.im ≠ 0) (hs : u - 2*physicalRate q branch ≠ 0)
    (hc : connection u (physicalRadialFrequency q) ≠ 0) (t : ℝ) (ht : t < 0) :
    ((tortoiseRadius t:ℂ)^(2 : ℕ)-1) * continuedPhysicalTimeAction q branch u a true t zang -
      horizonRegularCoefficient u (physicalRadialFrequency q) (normalizable u (physicalRadialFrequency q))
        (normalizableFirst u (physicalRadialFrequency q)) *
        (((tortoiseRadius t:ℂ)^(2 : ℕ)-1) * continuedPhysicalTimeAction q branch u a false t zang) =
      oppositeTemporalOuterDensity q branch a zang u t := by
  have hn := (original_homogeneous_horizon_representation u (physicalRadialFrequency q) hu
    (fun z hz => (normalizable_derivatives_continued hz).1)
    (fun z hz => (normalizable_derivatives_continued hz).2)
    (fun z hz => normalizable_equation_continued hz) (horizonCoordinate_interior t ht)).1
  rw [normalizable_opposite_coefficient u (physicalRadialFrequency q) hu] at hn
  have hS : selfExpression q branch a u t =
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
        continuedPhysicalSelfResponse q branch u a t := by
    rw [selfExpression, continuedPhysicalSelfResponse_decomposition,
      clearedReducedGreen_eq u (physicalRadialFrequency q) (physicalRate q branch) a hs hc]
    simp only [physicalSelfPrincipalResponse, Fin.sum_univ_three]
    ring
  have hK : contactExpression q branch a u t =
      reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
        horizonRegularAngularSourceProjection q branch (physicalAngularParameter q) a u t := by
    simp only [contactExpression, horizonRegularAngularSourceProjection, Fin.sum_univ_three]
  calc
    _ = (connection u (physicalRadialFrequency q)/(2*u)) *
      temporalCurrentSourceFactor q branch a u t zang *
      horizon (-u) (physicalRadialFrequency q) (horizonCoordinate t) := by
        rw [continuedPhysicalTimeAction_radial_density q branch u a true t ht zang,
          continuedPhysicalTimeAction_radial_density q branch u a false t ht zang]
        simp only [tortoiseMode, radialMode, if_true, Bool.false_eq_true, if_false]
        rw [hn]
        unfold temporalCurrentSourceFactor
        ring
    _ = oppositeCurrentRatio q branch u *
      (reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch) *
        temporalCurrentSourceFactor q branch a u t zang) *
      horizon (-u) (physicalRadialFrequency q) (horizonCoordinate t) := by
        rw [← oppositeCurrentRatio_mul_clearing q branch u hs]
        ring
    _ = _ := by
      unfold oppositeTemporalOuterDensity temporalCurrentSourceFactor
      rw [hS, hK]
      simp only [tortoiseMode, radialMode_false]
      ring

theorem oppositeTemporalOuterDensity_continuousAt (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (hu : u.im ≠ 0) (hur : -2 < u.re) {t : ℝ} (ht : t < 0) :
    ContinuousAt (oppositeTemporalOuterDensity q branch a zang u) t := by
  have hS := selfExpression_continuousAt q branch a u hu hur t ht
  have hK := contactExpression_continuousAt q branch a u hu hur t ht
  have hH := (tortoiseMode_hasDerivAt_continued (-u) (physicalRadialFrequency q) t ht).1.continuousAt
  unfold oppositeTemporalOuterDensity
  exact continuousAt_const.mul (continuousAt_const.mul
    (((continuousAt_const.mul hS).sub (continuousAt_const.mul hK)).mul hH))

theorem oppositeTemporalOuterDensity_analyticAt (q : XiZeroCopy) (branch : Bool) (a u : ℂ)
    (zang : D4BMHorizon.Point) (hu : u.im ≠ 0) (hur : -2 < u.re)
    (hs : u - 2*physicalRate q branch ≠ 0)
    (hcp : ∀ i : Fin 3, connection u (principalFrequency q i) ≠ 0) {t : ℝ} (ht : t < 0) :
    AnalyticAt ℂ (fun v => oppositeTemporalOuterDensity q branch a zang v t) u := by
  have hS := selfExpression_frequency_analyticAt q branch a u hu hur hs hcp t ht
  have hK := contactExpression_frequency_analyticAt q branch a u hu hur hs hcp t ht
  have hH : AnalyticAt ℂ (fun v => tortoiseMode false (-v) (physicalRadialFrequency q) t) u := by
    simp only [tortoiseMode, radialMode_false]
    exact (horizon_frequency_analyticAt (-u) (physicalRadialFrequency q)
      (by simpa only [Complex.neg_im] using neg_ne_zero.mpr hu)
      (horizonCoordinate_interior t ht)).comp analyticAt_id.neg
  have hu0 : u ≠ 0 := by intro h; exact hu (by simp only [h, Complex.zero_im])
  unfold oppositeTemporalOuterDensity
  exact (oppositeCurrentRatio_analyticAt q branch u hu0 hs).mul
    (analyticAt_const.mul (((((analyticAt_const.mul analyticAt_id).mul analyticAt_const).mul hS).sub
      (analyticAt_id.mul hK)).mul hH))

theorem oppositeTemporalOuterDensity_norm_le (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (t : ℝ) {BS BK CH M CZ : ℝ}
    (hS : ‖selfExpression q branch a u t‖ ≤ BS) (hK : ‖contactExpression q branch a u t‖ ≤ BK)
    (hH : ‖tortoiseMode false (-u) (physicalRadialFrequency q) t‖ ≤ CH) (hu : ‖u‖ ≤ M)
    (hBS : 0 ≤ BS) (hBK : 0 ≤ BK) (hZ : ‖oppositeCurrentRatio q branch u‖ ≤ CZ) (hCZ : 0 ≤ CZ) :
    ‖oppositeTemporalOuterDensity q branch a zang u t‖ ≤ CZ *
      (‖modeAngularSquare (physicalModeAngularJet q zang)‖ *
        ((2*M*‖physicalAngularParameter q^(2 : ℕ)-1/4-2‖*BS + M*BK)*CH)) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have h2 : ‖(-2:ℂ)‖ = 2 := by norm_num
  have hinner : ‖-2*u*(physicalAngularParameter q^(2 : ℕ)-1/4-2)*selfExpression q branch a u t -
      u*contactExpression q branch a u t‖ ≤ 2*M*‖physicalAngularParameter q^(2 : ℕ)-1/4-2‖*BS+M*BK := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul, h2]
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) le_rfl
        (norm_nonneg _) (by positivity)) hS (norm_nonneg _) (by positivity)
    · rw [norm_mul]
      exact mul_le_mul hu hK (norm_nonneg _) hM
  unfold oppositeTemporalOuterDensity
  rw [norm_mul]
  refine mul_le_mul hZ ?_ (norm_nonneg _) hCZ
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hinner hH (norm_nonneg _) (by positivity))
    (norm_nonneg _)

theorem oppositeTemporalOuterDensity_outer_uniform_bound (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball (physicalFundamentalFrequency q side) R, ∀ t ∈ Ico T (0:ℝ),
        ‖oppositeTemporalOuterDensity q branch a zang u t‖ ≤ C := by
  have hw := physicalFundamentalFrequency_strip q side
  obtain ⟨RG, CG, hRG, hCG, hG⟩ := physicalClearedReducedGreen_outer_uniform_bound q branch side a T
  obtain ⟨RH, CH, hRH, hCH, hH⟩ :=
    tortoiseMode_outer_uniform_bound (-physicalFundamentalFrequency q side)
      (physicalRadialFrequency q) (by simpa only [Complex.neg_im] using neg_ne_zero.mpr hw.1) T
  obtain ⟨R0, C0, hR0, hC0, hP0⟩ := principal_outer_uniform_bound q branch side a 0 T
  obtain ⟨R1, C1, hR1, hC1, hP1⟩ := principal_outer_uniform_bound q branch side a 1 T
  obtain ⟨R2, C2, hR2, hC2, hP2⟩ := principal_outer_uniform_bound q branch side a 2 T
  obtain ⟨RA, CA, hRA, hCA, hA⟩ := contactFactor_outer_uniform_bound q branch side a T
  obtain ⟨rF, hrF, hF⟩ := exists_closedBall_norm_le_of_continuousAt
    (reducedGreenClearingFactor_analyticAt (physicalFundamentalFrequency q side)
      (physicalRadialFrequency q) (physicalRate q branch) hw.1).continuousAt
  have hw0 : physicalFundamentalFrequency q side ≠ 0 := by
    intro h; exact hw.1 (by simp only [h, Complex.zero_im])
  obtain ⟨rZ, hrZ, hZ⟩ := exists_closedBall_norm_le_of_continuousAt
    (oppositeCurrentRatio_analyticAt q branch _ hw0
      (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side)).continuousAt
  let CZ := ‖oppositeCurrentRatio q branch (physicalFundamentalFrequency q side)‖ + 1
  have hCZ : 0 ≤ CZ := by positivity
  have hev : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u ∈ ball (physicalFundamentalFrequency q side) RG ∧
      u ∈ ball (physicalFundamentalFrequency q side) RH ∧
      u ∈ ball (physicalFundamentalFrequency q side) R0 ∧
      u ∈ ball (physicalFundamentalFrequency q side) R1 ∧
      u ∈ ball (physicalFundamentalFrequency q side) R2 ∧
      u ∈ ball (physicalFundamentalFrequency q side) RA ∧
      u ∈ closedBall (physicalFundamentalFrequency q side) rF ∧
      u ∈ ball (physicalFundamentalFrequency q side) 1 :=
    Filter.Eventually.and (ball_mem_nhds _ hRG) (Filter.Eventually.and (ball_mem_nhds _ hRH)
      (Filter.Eventually.and (ball_mem_nhds _ hR0) (Filter.Eventually.and (ball_mem_nhds _ hR1)
        (Filter.Eventually.and (ball_mem_nhds _ hR2) (Filter.Eventually.and (ball_mem_nhds _ hRA)
          (Filter.Eventually.and (closedBall_mem_nhds _ hrF) (ball_mem_nhds _ one_pos)))))))
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp (hev.and (closedBall_mem_nhds _ hrZ))
  let CP : ℝ := max C0 (max C1 C2)
  have hCP : 0 ≤ CP := hC0.trans (le_max_left _ _)
  let CF : ℝ := ‖reducedGreenClearingFactor (physicalFundamentalFrequency q side)
    (physicalRadialFrequency q) (physicalRate q branch)‖ + 1
  have hCF : 0 ≤ CF := by positivity
  let M : ℝ := ‖physicalFundamentalFrequency q side‖ + 1
  have hM : 0 ≤ M := by positivity
  let BS : ℝ := ‖physicalSelfSourceCoefficient q‖ * CG +
    CF * ((∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
      physicalAngularGap q q i‖) * CP)
  have hBS : 0 ≤ BS := by
    have : 0 ≤ ∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
      physicalAngularGap q q i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    positivity
  let BK : ℝ := CF * (CA * ‖scalarResidualPeriod q (physicalAngularParameter q)‖ +
    CP * ∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)‖)
  have hBK : 0 ≤ BK := by
    have : 0 ≤ ∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    positivity
  refine ⟨r, CZ * (‖modeAngularSquare (physicalModeAngularJet q zang)‖ *
    ((2 * M * ‖physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2‖ * BS + M * BK) * CH)), hr,
    by positivity, ?_⟩
  intro u hu t ht
  obtain ⟨huG, huH, hu0, hu1, hu2, huA, huF, hu1'⟩ := (hall (mem_ball.mp hu)).1
  have hP : ∀ i : Fin 3, ‖continuedPrincipalDifference q branch u a i t‖ ≤ CP := by
    intro i
    fin_cases i
    · exact (hP0 u hu0 t ht).trans (le_max_left _ _)
    · exact (hP1 u hu1 t ht).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hP2 u hu2 t ht).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFu : ‖reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)‖ ≤ CF :=
    hF u huF
  have hun : ‖u‖ ≤ M := by
    have hd : ‖u - physicalFundamentalFrequency q side‖ < 1 := by
      have := mem_ball.mp hu1'
      rwa [dist_eq_norm] at this
    have := norm_sub_norm_le u (physicalFundamentalFrequency q side)
    simp only [M]
    linarith
  have hS := selfExpression_norm_le q branch a u t (hG u huG t ht) hP hFu hCF
  have hK := contactExpression_norm_le q branch a u t (hA u huA t ⟨ht.1, ht.2.le⟩) hP hFu hCF
  have huH' : -u ∈ ball (-physicalFundamentalFrequency q side) RH := by
    simpa only [mem_ball, dist_neg_neg] using huH
  exact oppositeTemporalOuterDensity_norm_le q branch a zang u t hS hK
    (hH (-u) huH' t ht) hun hBS hBK (hZ u (hall (mem_ball.mp hu)).2) hCZ


/-- The restored opposite current over the original outer radial interval. -/
def oppositeTemporalOuterIntegral (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (T : ℝ) (u : ℂ) : ℂ :=
  ∫ t in Ioo T 0, oppositeTemporalOuterDensity q branch a zang u t

theorem oppositeTemporalOuterIntegral_analyticAt (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (T : ℝ) :
    AnalyticAt ℂ (oppositeTemporalOuterIntegral q branch a zang T) (physicalFundamentalFrequency q side) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  obtain ⟨RB, CB, hRB, -, hbound⟩ :=
    oppositeTemporalOuterDensity_outer_uniform_bound q branch side a zang T
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
      ((Ioo T 0).indicator (fun t => oppositeTemporalOuterDensity q branch a zang u t))
      volume := by
    intro u hu
    obtain ⟨hui, hur, -, -, -⟩ := hall (mem_ball.mp hu)
    refine (aestronglyMeasurable_indicator_iff measurableSet_Ioo).mpr ?_
    have hcont : ContinuousOn (oppositeTemporalOuterDensity q branch a zang u) (Ioo T 0) :=
      fun t ht => (oppositeTemporalOuterDensity_continuousAt q branch a u zang hui hur ht.2).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have hdiff : ∀ t : ℝ, DifferentiableOn ℂ (fun u =>
      (Ioo T 0).indicator (fun t => oppositeTemporalOuterDensity q branch a zang u t) t)
      (ball (physicalFundamentalFrequency q side) r) := by
    intro t u hu
    by_cases ht : t ∈ Ioo T 0
    · simp only [indicator_of_mem ht]
      obtain ⟨hui, hur, hus, hcp, -⟩ := hall (mem_ball.mp hu)
      exact (oppositeTemporalOuterDensity_analyticAt q branch a u zang hui hur hus hcp ht.2).differentiableAt.differentiableWithinAt
    · simp only [indicator_of_notMem ht]
      exact (differentiableAt_const _).differentiableWithinAt
  have hB : ∀ t : ℝ, ∀ u ∈ ball (physicalFundamentalFrequency q side) r,
      ‖(Ioo T 0).indicator (fun t => oppositeTemporalOuterDensity q branch a zang u t) t‖ ≤
        (Ioo T 0).indicator (fun _ => CB) t := by
    intro t u hu
    by_cases ht : t ∈ Ioo T 0
    · simp only [indicator_of_mem ht]
      exact hbound u (hall (mem_ball.mp hu)).2.2.2.2 t ⟨ht.1.le, ht.2⟩
    · simp only [indicator_of_notMem ht, norm_zero, le_refl]
  have hi : Integrable ((Ioo T 0).indicator (fun _ => CB)) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have hDI : DifferentiableOn ℂ (fun u => ∫ t,
      (Ioo T 0).indicator (fun t => oppositeTemporalOuterDensity q branch a zang u t) t)
      (ball (physicalFundamentalFrequency q side) r) := by
    intro v hv
    obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hv)
    exact (differentiableAt_integral_of_cauchy_dominated hr'
      (fun u hu => hmeas u (hsub hu)) (fun t => (hdiff t).mono hsub)
      (fun t u hu => hB t u (hsub hu)) hi).differentiableWithinAt
  have hA := hDI.analyticOnNhd isOpen_ball (physicalFundamentalFrequency q side) (mem_ball_self hr)
  simpa only [oppositeTemporalOuterIntegral, integral_indicator measurableSet_Ioo] using! hA

end
end RHTower.D4BMJointSource
