import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalCurrentClearedDensity

/-!
# Uniform outer bound of the cleared temporal density

One constant bounds the cleared temporal density on a frequency neighbourhood of the fundamental
quasinormal frequency and on every half-line `[T, 0)`, up to spatial infinity.  The self channel
and the horizon mode come with their own Grönwall bounds; each principal channel is the
denominator-cleared principal difference divided by a clearing factor that is nonzero at the
quasinormal frequency; the contact factor is jointly continuous on a compact set.
-/

namespace RHTower.D4BMJointSource
open Complex Set Filter Topology Metric D4BMLaplaceRadial D4BMModularCore D4BMJointWave
  D4BMPhysicalModeAction GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ## Factor bounds -/

/-- Each continued principal channel is uniformly bounded near the fundamental frequency, up to
spatial infinity. -/
theorem principal_outer_uniform_bound (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (i : Fin 3)
    (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball (physicalFundamentalFrequency q side) R, ∀ t ∈ Ico T (0:ℝ),
        ‖continuedPrincipalDifference q branch u a i t‖ ≤ C := by
  have hw := physicalFundamentalFrequency_strip q side
  have hc0 := physicalFundamental_principal_connection_ne_zero q side i
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hpcf0 : principalClearingFactor q branch (physicalFundamentalFrequency q side) i ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hs0) hc0
  have hpcfc : ContinuousAt (fun u => principalClearingFactor q branch u i)
      (physicalFundamentalFrequency q side) := by
    unfold principalClearingFactor
    exact ((continuousAt_id.sub continuousAt_const).neg.mul
      (connection_frequency_analyticAt _ (principalFrequency q i) hw.1).continuousAt)
  have hm : 0 < ‖principalClearingFactor q branch (physicalFundamentalFrequency q side) i‖ / 2 :=
    half_pos (norm_pos_iff.mpr hpcf0)
  have hev1 : ∀ᶠ u in 𝓝 (physicalFundamentalFrequency q side),
      ‖principalClearingFactor q branch (physicalFundamentalFrequency q side) i‖ / 2 <
        ‖principalClearingFactor q branch u i‖ :=
    continuousAt_const.eventually_lt hpcfc.norm (by linarith [norm_pos_iff.mpr hpcf0])
  have hev2 : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), u.im ≠ 0 :=
    Complex.continuous_im.continuousAt.eventually_ne hw.1
  have hev3 : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side), -2 < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (abs_lt.mp hw.2).1
  have hev4 : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u - 2 * physicalRate q branch ≠ 0 :=
    (continuous_id.sub continuous_const).continuousAt.eventually_ne hs0
  have hev5 : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      connection u (principalFrequency q i) ≠ 0 :=
    (connection_frequency_analyticAt _ (principalFrequency q i) hw.1).continuousAt.eventually_ne hc0
  have hev6 : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u ∈ ball (physicalFundamentalFrequency q side) 1 := ball_mem_nhds _ one_pos
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp
    (hev1.and (hev2.and (hev3.and (hev4.and (hev5.and hev6)))))
  have hstrip : ∀ u ∈ closedBall (physicalFundamentalFrequency q side) (r / 2),
      u.im ≠ 0 ∧ -2 < u.re := fun u hu =>
    let h := hall (lt_of_le_of_lt (mem_closedBall.mp hu) (half_lt_self hr))
    ⟨h.2.1, h.2.2.1⟩
  obtain ⟨C, hC, hbound⟩ := clearedPrincipalDifference_compact_bound q branch a i
    (closedBall (physicalFundamentalFrequency q side) (r / 2)) (isCompact_closedBall _ _) hstrip
  refine ⟨r / 2, C * Real.exp ((‖physicalFundamentalFrequency q side‖ + 1) * |T|) /
    (‖principalClearingFactor q branch (physicalFundamentalFrequency q side) i‖ / 2),
    half_pos hr, by positivity, ?_⟩
  intro u hu t ht
  obtain ⟨hmu, -, -, hus, huc, hu1⟩ :=
    hall (lt_of_lt_of_le (mem_ball.mp hu) (half_le_self hr.le))
  have hint : u ∈ interior (closedBall (physicalFundamentalFrequency q side) (r / 2)) :=
    ball_subset_interior_closedBall hu
  have hb := hbound u hint t ht.2
  have hun : |u.re| ≤ ‖physicalFundamentalFrequency q side‖ + 1 := by
    have hd : ‖u - physicalFundamentalFrequency q side‖ < 1 := by
      have := mem_ball.mp hu1
      rwa [dist_eq_norm] at this
    have := norm_sub_norm_le u (physicalFundamentalFrequency q side)
    exact (Complex.abs_re_le_norm u).trans (by linarith)
  have htT : -t ≤ |T| := (neg_le_neg ht.1).trans (neg_le_abs T)
  have hexp : Real.exp (-|u.re| * t) ≤
      Real.exp ((‖physicalFundamentalFrequency q side‖ + 1) * |T|) := by
    apply Real.exp_le_exp.mpr
    calc -|u.re| * t = |u.re| * (-t) := by ring
      _ ≤ (‖physicalFundamentalFrequency q side‖ + 1) * |T| :=
        mul_le_mul hun htT (by linarith [ht.2]) (by positivity)
  have hb' : ‖clearedPrincipalDifference q branch u a i t‖ ≤
      C * Real.exp ((‖physicalFundamentalFrequency q side‖ + 1) * |T|) :=
    hb.trans (mul_le_mul_of_nonneg_left hexp hC)
  rw [clearedPrincipalDifference_eq q branch u a i hus huc t, norm_mul] at hb'
  rw [le_div_iff₀ hm]
  calc ‖continuedPrincipalDifference q branch u a i t‖ *
        (‖principalClearingFactor q branch (physicalFundamentalFrequency q side) i‖ / 2)
      ≤ ‖continuedPrincipalDifference q branch u a i t‖ * ‖principalClearingFactor q branch u i‖ :=
        mul_le_mul_of_nonneg_left hmu.le (norm_nonneg _)
    _ = ‖principalClearingFactor q branch u i‖ * ‖continuedPrincipalDifference q branch u a i t‖ := by
        ring
    _ ≤ _ := hb'

/-- The contact factor is jointly continuous, hence bounded on a compact frequency–radius set. -/
theorem contactFactor_outer_uniform_bound (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball (physicalFundamentalFrequency q side) R, ∀ t ∈ Icc T (0:ℝ),
        ‖sourceAmplitude (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u) t *
          reducedHorizonQuotient (physicalRate q branch) u (radialUnit t)‖ ≤ C := by
  have hs0 := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  have hev : ∀ᶠ u : ℂ in 𝓝 (physicalFundamentalFrequency q side),
      u - 2 * physicalRate q branch ≠ 0 :=
    (continuous_id.sub continuous_const).continuousAt.eventually_ne hs0
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp hev
  have hK : IsCompact (closedBall (physicalFundamentalFrequency q side) (r / 2) ×ˢ Icc T (0:ℝ)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hF : ContinuousOn (fun p : ℂ × ℝ =>
      sourceAmplitude (physicalRate q branch) p.1 a (continuedOnset (physicalRate q branch) p.1) p.2 *
        reducedHorizonQuotient (physicalRate q branch) p.1 (radialUnit p.2))
      (closedBall (physicalFundamentalFrequency q side) (r / 2) ×ˢ Icc T (0:ℝ)) := by
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    have hps : p.1 - 2 * physicalRate q branch ≠ 0 :=
      hall (lt_of_le_of_lt (mem_closedBall.mp hp.1) (half_lt_self hr))
    have hr1 : ContinuousAt (fun p : ℂ × ℝ => radialUnit p.2) p :=
      (radialUnit_hasDerivAt p.2).continuousAt.comp continuousAt_snd
    have hr2 : ContinuousAt (fun p : ℂ × ℝ => (radialUnit p.2 : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp hr1
    have hne : (1:ℂ) + (radialUnit p.2 : ℂ) ≠ 0 := by
      exact_mod_cast (radialUnit_add_one_pos p.2).ne'
    have hpow : ContinuousAt (fun p : ℂ × ℝ =>
        power (2 * physicalRate q branch) (1 + radialUnit p.2)) p := by
      have h1 : ContinuousAt (fun p : ℂ × ℝ => 1 + radialUnit p.2) p := continuousAt_const.add hr1
      have h2 := Complex.continuousAt_ofReal_cpow_const (1 + radialUnit p.2)
        (2 * physicalRate q branch) (Or.inr (radialUnit_add_one_pos p.2).ne')
      exact ContinuousAt.comp (g := fun x : ℝ => (x:ℂ) ^ (2 * physicalRate q branch)) h2 h1
    have hexp : ContinuousAt (fun p : ℂ × ℝ => Complex.exp (p.1 * (p.2:ℂ))) p :=
      (continuousAt_fst.mul (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd)).cexp
    have honset : ContinuousAt (fun p : ℂ × ℝ => continuedOnset (physicalRate q branch) p.1) p :=
      (continuedOnset_analyticAt (physicalRate q branch) p.1 hps).continuousAt.comp continuousAt_fst
    have hQ : ContinuousAt (fun p : ℂ × ℝ =>
        reducedHorizonQuotient (physicalRate q branch) p.1 (radialUnit p.2)) p := by
      unfold reducedHorizonQuotient reducedHorizonPolynomial
      fun_prop (disch := exact hne)
    unfold sourceAmplitude
    exact (((hexp.mul hpow).mul continuousAt_const).mul honset).mul hQ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨r / 2, max C 0, half_pos hr, le_max_right _ _, fun u hu t ht => ?_⟩
  exact (hC (u, t) ⟨ball_subset_closedBall hu, ht⟩).trans (le_max_left _ _)

/-! ## Algebraic bounds of the expression -/

theorem selfExpression_norm_le (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (t : ℝ)
    {CG CP CF : ℝ}
    (hG : ‖clearedReducedGreen u (physicalRadialFrequency q) (physicalRate q branch) a t‖ ≤ CG)
    (hP : ∀ i : Fin 3, ‖continuedPrincipalDifference q branch u a i t‖ ≤ CP)
    (hF : ‖reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)‖ ≤ CF)
    (hCF : 0 ≤ CF) :
    ‖selfExpression q branch a u t‖ ≤ ‖physicalSelfSourceCoefficient q‖ * CG +
      CF * ((∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
        physicalAngularGap q q i‖) * CP) := by
  have hsum : ‖∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
      physicalAngularGap q q i * continuedPrincipalDifference q branch u a i t‖ ≤
      (∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i) /
        physicalAngularGap q q i‖) * CP := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hP i) (norm_nonneg _)
  unfold selfExpression
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  refine add_le_add (mul_le_mul_of_nonneg_left hG (norm_nonneg _)) ?_
  exact mul_le_mul hF hsum (norm_nonneg _) hCF

theorem contactExpression_norm_le (q : XiZeroCopy) (branch : Bool) (a : ℂ) (u : ℂ) (t : ℝ)
    {CA CP CF : ℝ}
    (hA : ‖sourceAmplitude (physicalRate q branch) u a (continuedOnset (physicalRate q branch) u) t *
      reducedHorizonQuotient (physicalRate q branch) u (radialUnit t)‖ ≤ CA)
    (hP : ∀ i : Fin 3, ‖continuedPrincipalDifference q branch u a i t‖ ≤ CP)
    (hF : ‖reducedGreenClearingFactor u (physicalRadialFrequency q) (physicalRate q branch)‖ ≤ CF)
    (hCF : 0 ≤ CF) :
    ‖contactExpression q branch a u t‖ ≤ CF *
      (CA * ‖scalarResidualPeriod q (physicalAngularParameter q)‖ +
        CP * ∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)‖) := by
  have hsum : ‖∑ i : Fin 3, continuedPrincipalDifference q branch u a i t *
      scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)‖ ≤
      CP * ∑ i : Fin 3, ‖scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)‖ := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hP i) (norm_nonneg _)
  unfold contactExpression
  rw [norm_mul]
  refine mul_le_mul hF ?_ (norm_nonneg _) hCF
  refine (norm_add_le _ _).trans (add_le_add ?_ hsum)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)

theorem clearedTemporalExpression_norm_le (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (u : ℂ) (t : ℝ) {BS BK CH M : ℝ}
    (hS : ‖selfExpression q branch a u t‖ ≤ BS) (hK : ‖contactExpression q branch a u t‖ ≤ BK)
    (hH : ‖tortoiseMode false u (physicalRadialFrequency q) t‖ ≤ CH) (hu : ‖u‖ ≤ M)
    (hBS : 0 ≤ BS) (hBK : 0 ≤ BK) :
    ‖clearedTemporalExpression q branch a zang u t‖ ≤
      ‖modeAngularSquare (physicalModeAngularJet q zang)‖ *
        ((2 * M * ‖physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2‖ * BS + M * BK) * CH) := by
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  have h2 : ‖(-2:ℂ)‖ = 2 := by norm_num
  have hinner : ‖-2 * u * (physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2) * selfExpression q branch a u t -
      u * contactExpression q branch a u t‖ ≤
      2 * M * ‖physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2‖ * BS + M * BK := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, norm_mul, h2]
      refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) le_rfl
        (norm_nonneg _) (by positivity)) hS (norm_nonneg _) (by positivity)
    · rw [norm_mul]
      exact mul_le_mul hu hK (norm_nonneg _) hM
  unfold clearedTemporalExpression
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left (mul_le_mul hinner hH (norm_nonneg _) (by positivity))
    (norm_nonneg _)

/-! ## The uniform outer bound -/

/-- One constant bounds the cleared temporal density near the fundamental quasinormal frequency on
every half-line `[T, 0)`. -/
theorem clearedTemporalDensity_outer_uniform_bound (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (zang : D4BMHorizon.Point) (T : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ u ∈ ball (physicalFundamentalFrequency q side) R, ∀ t ∈ Ico T (0:ℝ),
        ‖clearedTemporalDensity q branch a zang u t‖ ≤ C := by
  have hw := physicalFundamentalFrequency_strip q side
  obtain ⟨RG, CG, hRG, hCG, hG⟩ := physicalClearedReducedGreen_outer_uniform_bound q branch side a T
  obtain ⟨RH, CH, hRH, hCH, hH⟩ :=
    tortoiseMode_outer_uniform_bound (physicalFundamentalFrequency q side)
      (physicalRadialFrequency q) hw.1 T
  obtain ⟨R0, C0, hR0, hC0, hP0⟩ := principal_outer_uniform_bound q branch side a 0 T
  obtain ⟨R1, C1, hR1, hC1, hP1⟩ := principal_outer_uniform_bound q branch side a 1 T
  obtain ⟨R2, C2, hR2, hC2, hP2⟩ := principal_outer_uniform_bound q branch side a 2 T
  obtain ⟨RA, CA, hRA, hCA, hA⟩ := contactFactor_outer_uniform_bound q branch side a T
  obtain ⟨rF, hrF, hF⟩ := exists_closedBall_norm_le_of_continuousAt
    (reducedGreenClearingFactor_analyticAt (physicalFundamentalFrequency q side)
      (physicalRadialFrequency q) (physicalRate q branch) hw.1).continuousAt
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
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp hev
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
  refine ⟨r, ‖modeAngularSquare (physicalModeAngularJet q zang)‖ *
    ((2 * M * ‖physicalAngularParameter q ^ (2 : ℕ) - 1 / 4 - 2‖ * BS + M * BK) * CH), hr,
    by positivity, ?_⟩
  intro u hu t ht
  obtain ⟨huG, huH, hu0, hu1, hu2, huA, huF, hu1'⟩ := hall (mem_ball.mp hu)
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
  rw [clearedTemporalDensity_eq_expression q branch a zang u t ht.2]
  exact clearedTemporalExpression_norm_le q branch a zang u t hS hK (hH u huH t ht) hun hBS hBK

end
end RHTower.D4BMJointSource
