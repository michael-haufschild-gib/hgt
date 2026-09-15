import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricTemporalDiagonal

/-!
# Literal source reduction of the original Green metric and temporal action

Derives a whole-exterior Cauchy bound for independent source and reader
frequencies, admits the actual source derivative integral, and identifies
it with the complete original Green finite part plus its temporal corner.
The final formula keeps the original tortoise coordinate and fixes every
angular coefficient. QNM continuation and native forcing are separate.
-/
open Set Filter Topology MeasureTheory Metric
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore D4BMJointSource
noncomputable section
set_option autoImplicit false

private theorem literalOnset_analyticAt (s w : ℂ) (hs : w-2*s≠0) :
    AnalyticAt ℂ (continuedOnset s) w :=
  (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
    ((onsetCorrection_entire (2*s)).analyticAt w)

/-- Only the original source frequency varies; all angular and source
coefficients remain fixed. -/
theorem continuedSourceProfile_frequency_analyticAt (s amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : 0<z) :
    AnalyticAt ℂ (fun u => continuedSourceProfile s amp J K u z) w := by
  have h := ((sourceProfile_frequency_entire s amp J K 1 hz).analyticAt w).mul
    (literalOnset_analyticAt s w hs)
  have he : ((fun u : ℂ => sourceProfile s u amp J K 1 z)*continuedOnset s)=
      (fun u => continuedSourceProfile s amp J K u z) := by
    funext u
    dsimp only [Pi.mul_apply,continuedSourceProfile,sourceProfile,sourceRemainder,continuedOnset]
    ring
  simpa only [he] using! h

private theorem reader_coefficients_continuousAt (w chi : ℂ) (hw : w.im≠0) :
    ContinuousAt (fun v => horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)) w ∧
    ContinuousAt (fun v => connection v chi/(2*v)) w := by
  have hw0 : w≠0 := by intro he; exact hw (by simp [he])
  have hz : (1/2:ℝ)∈Ioo (0:ℝ) 1 := by constructor <;> norm_num
  have hm : (-w).im≠0 := by simpa only [Complex.neg_im,neg_ne_zero] using hw
  have hH := ((horizon_frequency_analyticAt (-w) chi hm hz).comp analyticAt_id.neg).continuousAt
  have hD := ((horizonFirst_frequency_analyticAt (-w) chi hm hz).comp analyticAt_id.neg).continuousAt
  have hN := (normalizable_frequency_entire chi hz w).continuousAt
  have hN1 := (normalizableFirst_frequency_entire chi hz w).continuousAt
  refine ⟨?_,?_⟩
  · simpa only [horizonRegularCoefficient,radialBracket,Function.comp_def] using!
      (((hN.mul hD).sub (hN1.mul hH)).const_mul (integratingFactor (1/2))).div
        (show ContinuousAt (fun v : ℂ => -v) w by fun_prop) (neg_ne_zero.mpr hw0)
  · exact (connection_frequency_analyticAt w chi hw).continuousAt.div
      (show ContinuousAt (fun v : ℂ => 2*v) w by fun_prop) (mul_ne_zero (by norm_num) hw0)

/-- A single integrable power bounds the literal mixed source product over
the whole exterior, uniformly in both independent frequencies. -/
theorem mixedSource_uniform_bound (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) :
    ∃ R C : ℝ, 0<R ∧ 0≤C ∧
      (∀ u∈ball w R, u-2*s≠0) ∧
      ∀ u∈ball w R, ∀ v∈ball w R, ∀ z∈Ioo (0:ℝ) 1,
        ‖normalizable v chi z*continuedSourceProfile s amp J K u z‖≤C*z^(-(1/2:ℝ)) := by
  let A := fun v => horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)
  let beta := fun v => connection v chi/(2*v)
  let MA := ‖A w‖+1
  let MB := ‖beta w‖+1
  let MT := ‖continuedOnset s w‖+1
  have hMA : 0≤MA := by dsimp [MA]; positivity
  have hMB : 0≤MB := by dsimp [MB]; positivity
  have hMT : 0≤MT := by dsimp [MT]; positivity
  obtain ⟨hAc,hBc⟩ := reader_coefficients_continuousAt w chi hw
  have hTc := (literalOnset_analyticAt s w hs).continuousAt
  have hnear : ∀ᶠ u : ℂ in 𝓝 w,
      u.im≠0 ∧ u-2*s≠0 ∧ ‖A u‖≤MA ∧ ‖beta u‖≤MB ∧ ‖continuedOnset s u‖≤MT := by
    filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw,
      (show ContinuousAt (fun u : ℂ => u-2*s) w by fun_prop).eventually_ne hs,
      hAc.norm.eventually_lt continuousAt_const (lt_add_one ‖A w‖),
      hBc.norm.eventually_lt continuousAt_const (lt_add_one ‖beta w‖),
      hTc.norm.eventually_lt continuousAt_const (lt_add_one ‖continuedOnset s w‖)] with u hui hus huA huB huT
    exact ⟨hui,hus,huA.le,huB.le,huT.le⟩
  obtain ⟨R0,hR0,h0⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨RP,CP,hRP,hCP,hGP⟩ := horizonGauss_uniform_first_bound w chi hw
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨RM,CM,hRM,hCM,hGM⟩ := horizonGauss_uniform_first_bound (-w) chi
    (by simpa only [Complex.neg_im,neg_ne_zero] using hw)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let R := min R0 (min RP (min RM (1/4)))
  have hR : 0<R := lt_min hR0 (lt_min hRP (lt_min hRM (by norm_num)))
  have hR0' : R≤R0 := min_le_left _ _
  have hRP' : R≤RP := (min_le_right _ _).trans (min_le_left _ _)
  have hRM' : R≤RM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRq : R≤1/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hR1 : R≤1 := by linarith
  have hsmall (u : ℂ) (hu : u∈ball w R) := h0 ((mem_ball.mp hu).trans_le hR0')
  obtain ⟨M0,hM0⟩ := ((isCompact_closedBall w 1).prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).exists_bound_of_continuousOn
    (sourceRemainder_joint_continuous s amp J K 1).continuousOn
  let M := max M0 0
  have hM : 0≤M := le_max_right _ _
  have hsource (u : ℂ) (hu : u∈ball w R) (z : ℝ) (hz : z∈Icc (0:ℝ) 1) :
      ‖sourceRemainder s u amp J K 1 z‖≤M :=
    (hM0 (u,z) ⟨ball_subset_closedBall (ball_subset_ball hR1 hu),hz⟩).trans (le_max_left _ _)
  have hpowcont : ContinuousOn (fun p : ℂ×ℝ => power (p.1/2) p.2)
      (closedBall w 1 ×ˢ Icc (1/2:ℝ) 1) := by
    intro p hp
    have hz : 0<p.2 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hp.2.1
    exact ((Complex.continuousAt_ofReal_cpow p.2 (p.1/2) (Or.inr hz.ne')).comp_of_eq
      (show ContinuousAt (fun q : ℂ×ℝ => (q.2,q.1/2)) p by fun_prop) rfl).continuousWithinAt
  obtain ⟨P0,hP0⟩ := ((isCompact_closedBall w 1).prod isCompact_Icc).exists_bound_of_continuousOn hpowcont
  let P := max P0 0
  have hP : 0≤P := le_max_right _ _
  have hpower (u : ℂ) (hu : u∈ball w R) (z : ℝ) (hz : z∈Icc (1/2:ℝ) 1) : ‖power (u/2) z‖≤P :=
    (hP0 (u,z) ⟨ball_subset_closedBall (ball_subset_ball hR1 hu),hz⟩).trans (le_max_left _ _)
  obtain ⟨CG,hCG,hGO⟩ := outerGauss_uniform_bound w chi
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let CH := (MA*(CP+1)+MB*(CM+1))*M*MT
  let CO := P*P*CG*M*MT
  have hCH : 0≤CH := by dsimp [CH]; positivity
  have hCO : 0≤CO := by dsimp [CO]; positivity
  refine ⟨R,CH+CO,hR,add_nonneg hCH hCO,(fun u hu => (hsmall u hu).2.1),?_⟩
  intro u hu v hv z hz
  have hS := hsource u hu z ⟨hz.1.le,hz.2.le⟩
  have hT := (hsmall u hu).2.2.2.2
  have hA := (hsmall v hv).2.2.1
  have hB := (hsmall v hv).2.2.2.1
  have hSrc : continuedSourceProfile s amp J K u z=
      power (u/2) z*sourceRemainder s u amp J K 1 z*continuedOnset s u := by
    dsimp only [continuedSourceProfile,sourceProfile,sourceRemainder,continuedOnset]
    ring
  have hweight : 0≤z^(-(1/2:ℝ)) := Real.rpow_nonneg hz.1.le _
  by_cases hzh : z≤1/2
  · have hpG := hGP v (ball_subset_ball hRP' hv) z ⟨hz.1.le,hzh⟩
    have hmG := hGM (-v) (by simpa only [mem_ball,dist_neg_neg] using
      (ball_subset_ball hRM' hv)) z ⟨hz.1.le,hzh⟩
    have hgp : ‖gaussFactor v chi false (z:ℂ)‖≤CP+1 := by
      have hn := norm_sub_norm_le (gaussFactor v chi false (z:ℂ)) (1:ℂ)
      rw [norm_one] at hn
      linarith [mul_le_mul_of_nonneg_left hz.2.le hCP]
    have hgm : ‖gaussFactor (-v) chi false (z:ℂ)‖≤CM+1 := by
      have hn := norm_sub_norm_le (gaussFactor (-v) chi false (z:ℂ)) (1:ℂ)
      rw [norm_one] at hn
      linarith [mul_le_mul_of_nonneg_left hz.2.le hCM]
    have hure : |u.re-w.re|<1/4 := by
      have hn : ‖u-w‖<1/4 := by simpa only [dist_eq_norm] using (mem_ball.mp hu).trans_le hRq
      have hh := (Complex.abs_re_le_norm (u-w)).trans_lt hn
      simpa only [Complex.sub_re,dist_eq_norm] using hh
    have hvre : |v.re-w.re|<1/4 := by
      have hn : ‖v-w‖<1/4 := by simpa only [dist_eq_norm] using (mem_ball.mp hv).trans_le hRq
      have hh := (Complex.abs_re_le_norm (v-w)).trans_lt hn
      simpa only [Complex.sub_re,dist_eq_norm] using hh
    have hpRe : -(1/2:ℝ)≤((u+v)/2).re := by
      simp only [Complex.div_ofNat_re,Complex.add_re]
      linarith [(abs_lt.mp hure).1,(abs_lt.mp hvre).1]
    have hmRe : -(1/2:ℝ)≤((u-v)/2).re := by
      simp only [Complex.div_ofNat_re,Complex.sub_re]
      linarith [(abs_lt.mp hure).1,(abs_lt.mp hvre).2]
    have hpBound (a : ℂ) (ha : -(1/2:ℝ)≤a.re) : ‖power a z‖≤z^(-(1/2:ℝ)) := by
      rw [power,Complex.norm_cpow_eq_rpow_re_of_pos hz.1]
      exact Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2.le ha
    have hnormal := (original_homogeneous_horizon_representation v chi (hsmall v hv).1
      (fun z hz => (normalizable_derivatives_continued hz).1)
      (fun z hz => (normalizable_derivatives_continued hz).2)
      (fun z hz => normalizable_equation_continued hz) hz).1
    rw [normalizable_opposite_coefficient v chi (hsmall v hv).1] at hnormal
    have hmul (a : ℂ) : power (a/2) z*power (u/2) z=power ((u+a)/2) z := by
      rw [power,power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.1.ne')]
      congr 1
      ring
    have he : normalizable v chi z*continuedSourceProfile s amp J K u z=
        A v*power ((u+v)/2) z*gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u+
        beta v*power ((u-v)/2) z*gaussFactor (-v) chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u := by
      rw [hnormal,hSrc]
      dsimp only [horizon,dress,A,beta]
      have hm := hmul (-v)
      rw [show u+-v=u-v by ring] at hm
      linear_combination
        horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*
          gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u*(hmul v)+
        (connection v chi/(2*v))*gaussFactor (-v) chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u*hm
    rw [he]
    calc
      _ ≤ ‖A v*power ((u+v)/2) z*gaussFactor v chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u‖+
          ‖beta v*power ((u-v)/2) z*gaussFactor (-v) chi false (z:ℂ)*sourceRemainder s u amp J K 1 z*continuedOnset s u‖ := norm_add_le _ _
      _ ≤ MA*z^(-(1/2:ℝ))*(CP+1)*M*MT+MB*z^(-(1/2:ℝ))*(CM+1)*M*MT := by
        simp only [norm_mul]
        gcongr
        · exact hpBound _ hpRe
        · exact hpBound _ hmRe
      _ = CH*z^(-(1/2:ℝ)) := by dsimp [CH]; ring
      _ ≤ (CH+CO)*z^(-(1/2:ℝ)) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCO) hweight
  · have hzhalf : z∈Icc (1/2:ℝ) 1 := ⟨(lt_of_not_ge hzh).le,hz.2.le⟩
    have hn : ‖1-(z:ℂ)‖≤1/2 := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hz.2.le)]
      linarith [hzhalf.1]
    have hg := hGO v (ball_subset_ball hR1 hv) _ hn
    have hroot : ‖power (1/2) (1-z)‖≤1 := by
      rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le),Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (by linarith [hz.1])
    rw [hSrc,normalizable,dress,outerFactor]
    calc
      _ = ‖power (v/2) z‖*‖power (1/2) (1-z)‖*‖gaussFactor v chi true (1-z)‖*
          ‖power (u/2) z‖*‖sourceRemainder s u amp J K 1 z‖*‖continuedOnset s u‖ := by simp only [norm_mul]; ring
      _ ≤ P*1*CG*P*M*MT := by gcongr <;> first | exact hpower _ hv _ hzhalf | exact hpower _ hu _ hzhalf
      _ = CO := by dsimp [CO]; ring
      _ ≤ CO*z^(-(1/2:ℝ)) := le_mul_of_one_le_right hCO (by
        have hh := Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2.le (by norm_num : -(1/2:ℝ)≤0)
        simpa only [Real.rpow_zero] using hh)
      _ ≤ (CH+CO)*z^(-(1/2:ℝ)) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCH) hweight

/-- The literal source divided difference is uniformly dominated; its whole
exterior integral tends to the admitted fixed-source derivative overlap. -/
theorem sourceDifference_integral_tendsto (s chi amp J K w : ℂ)
    (hw : w.im≠0) (hwr : 0<w.re) (hs : w-2*s≠0) :
    IntervalIntegrable (fun z : ℝ => normalizable w chi z*
      deriv (fun u => continuedSourceProfile s amp J K u z) w) volume 0 1 ∧
    Tendsto (fun v : ℂ => ∫ z in (0:ℝ)..1,normalizable v chi z*
      (continuedSourceProfile s amp J K v z-continuedSourceProfile s amp J K w z)/(v-w))
      (𝓝[≠] w) (𝓝 (∫ z in (0:ℝ)..1,normalizable w chi z*
        deriv (fun u => continuedSourceProfile s amp J K u z) w)) := by
  obtain ⟨R,C,hR,hC,hpole,hbound⟩ := mixedSource_uniform_bound s chi amp J K w hw hwr hs
  let D := fun v : ℂ => fun z : ℝ => normalizable v chi z*
    (continuedSourceProfile s amp J K v z-continuedSourceProfile s amp J K w z)/(v-w)
  let L := fun z : ℝ => normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w
  let B := fun z : ℝ => (2*C/R)*z^(-(1/2:ℝ))
  have hhalf : 0<R/2 := half_pos hR
  have hsub : ball w (R/2)⊆ball w R := ball_subset_ball (by linarith)
  have hdom (v : ℂ) (hv : v∈ball w (R/2)) (hvw : v≠w) (z : ℝ) (hz : z∈Ioo (0:ℝ) 1) :
      ‖D v z‖≤B z := by
    have hf : DifferentiableOn ℂ (fun u => normalizable v chi z*continuedSourceProfile s amp J K u z) (ball w R) := by
      intro u hu
      exact ((continuedSourceProfile_frequency_analyticAt s amp J K u (hpole u hu) hz.1).differentiableAt.const_mul
        (normalizable v chi z)).differentiableWithinAt
    have h := Bottcher.norm_sub_le_of_bounded_on_ball hR hf
      (fun u hu => hbound u hu v (hsub hv) z hz) hv (mem_ball_self hhalf)
    have he : ‖D v z‖=
        ‖normalizable v chi z*continuedSourceProfile s amp J K v z-
          normalizable v chi z*continuedSourceProfile s amp J K w z‖/‖v-w‖ := by
      dsimp only [D]
      rw [norm_div,mul_sub]
    rw [he]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hvw))).mpr
    calc
      _ ≤ (2*(C*z^(-(1/2:ℝ)))/R)*‖v-w‖ := h
      _ = B z*‖v-w‖ := by dsimp [B]; ring
  have hmeas (v : ℂ) : AEStronglyMeasurable (D v) (volume.restrict (Ioo (0:ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro z hz
    exact (((normalizable_derivatives_continued (w:=v) (chi:=chi) hz).1.continuousAt.mul
      ((continuedSourceProfile_continuousAt s amp J K v hz.1).sub
        (continuedSourceProfile_continuousAt s amp J K w hz.1))).div_const (v-w)).continuousWithinAt
  have hpoint (z : ℝ) (hz : z∈Ioo (0:ℝ) 1) :
      Tendsto (fun v => D v z) (𝓝[≠] w) (𝓝 (L z)) := by
    have hS := (continuedSourceProfile_frequency_analyticAt s amp J K w hs hz.1).differentiableAt
    have hd : ContinuousAt (dslope (fun u => continuedSourceProfile s amp J K u z) w) w :=
      continuousAt_dslope_same.mpr hS
    have ht := ((normalizable_frequency_entire chi hz w).continuousAt.mul hd).tendsto.mono_left
      (show 𝓝[≠] w≤𝓝 w from nhdsWithin_le_nhds)
    change Tendsto (fun v : ℂ => normalizable v chi z*dslope (fun u => continuedSourceProfile s amp J K u z) w v)
      (𝓝[≠] w) (𝓝 (normalizable w chi z*dslope (fun u => continuedSourceProfile s amp J K u z) w w)) at ht
    rw [dslope_same] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [dslope_of_ne _ hv,slope_def_field]
    dsimp only [D]
    ring
  have hpointAE : ∀ᵐ z ∂volume.restrict (Ioo (0:ℝ) 1), Tendsto (fun v => D v z) (𝓝[≠] w) (𝓝 (L z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hpoint z hz
  have hboundAE : ∀ᶠ v in 𝓝[≠] w, ∀ᵐ z ∂volume.restrict (Ioo (0:ℝ) 1), ‖D v z‖≤B z := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds w hhalf),self_mem_nhdsWithin] with v hv hvw
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hdom v hv hvw z hz
  have hBI : Integrable B (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -(1/2)))).const_mul (2*C/R)
  have hLm : AEStronglyMeasurable L (volume.restrict (Ioo (0:ℝ) 1)) :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[≠] w) hmeas hpointAE
  have hLI : Integrable L (volume.restrict (Ioo (0:ℝ) 1)) := by
    apply hBI.mono' hLm
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    apply le_of_tendsto (hpoint z hz).norm
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds w hhalf),self_mem_nhdsWithin] with v hv hvw
    exact hdom v hv hvw z hz
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mpr hLI,?_⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence B (Filter.Eventually.of_forall hmeas)
    hboundAE hBI hpointAE
  have heq (v : ℂ) : (∫ z in (0:ℝ)..1,D v z)=∫ z in Ioo (0:ℝ) 1,D v z := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  have heqL : (∫ z in (0:ℝ)..1,L z)=∫ z in Ioo (0:ℝ) 1,L z := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]
  change Tendsto (fun v => ∫ z in (0:ℝ)..1,D v z) _ (𝓝 (∫ z in (0:ℝ)..1,L z))
  simp_rw [heq,heqL]
  exact hlim


/-- Source-only evaluation of the actual full Green metric action plus its
prescribed temporal corner in the genuine convergence chamber. -/
theorem originalMetricTemporal_eq_sourceDerivative_below (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      2*w*(normalizableHorizonPairingFinitePart s chi amp J K b w+
        (∫ z in b..1,mixedDensity s chi amp J K w w z))+
        connection w chi*(deriv (D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp J K) w+
          D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp J K w/(2*w))=
        -(∫ z in (0:ℝ)..1,normalizable w chi z*deriv (fun u => continuedSourceProfile s amp J K u z) w) := by
  have hwr := chamber_re_pos hw
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  obtain ⟨BI,hBI,hBIhalf,hI⟩ := readerFullRegularPart_source_difference_below s chi amp J K w hw hwi hs
  obtain ⟨BL,hBL,_,hL⟩ := fullMetricTemporal_diagonal_limit_below s chi amp J K w hw hwi hs
  have hD := (sourceDifference_integral_tendsto s chi amp J K w hwi hwr hsp).2
  refine ⟨min BI BL,lt_min hBI hBL,(min_le_left _ _).trans hBIhalf,?_⟩
  intro b hb hbB
  have hpath : Tendsto (fun t : ℝ => w-(t:ℂ)) (𝓝[>] (0:ℝ)) (𝓝[≠] w) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have hcont : ContinuousAt (fun t : ℝ => w-(t:ℂ)) 0 := by fun_prop
      simpa only [Complex.ofReal_zero,sub_zero] using hcont.tendsto.mono_left
        (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
      intro he
      apply ht0
      change w-(t:ℂ)=w at he
      linear_combination -he
  have hleft := (hL b hb (hbB.trans (min_le_right _ _))).comp hpath
  have hright := hD.neg.comp hpath
  have hdelta : (0:ℝ) < min (w.re-|chi.im|) (w.re-(2*s).re) := lt_min (sub_pos.mpr hw) (sub_pos.mpr hs)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [Ioo_mem_nhdsGT hdelta] with t ht
  have hch : Chamber (w-(t:ℂ)) chi := by
    change |chi.im|<(w-(t:ℂ)).re
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith [ht.2.trans_le (min_le_left _ _)]
  have hmi : (w-(t:ℂ)).im≠0 := by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hwi
  have hsource : (2*s).re<(w-(t:ℂ)).re := by
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith [ht.2.trans_le (min_le_right _ _)]
  have hplus : 0<(w+(w-(t:ℂ))).re := by
    simp only [Complex.add_re]
    exact add_pos hwr (chamber_re_pos hch)
  have hminus : 0<(w-(w-(t:ℂ))).re := by
    simpa only [sub_sub_cancel,Complex.ofReal_re] using ht.1
  exact (hI b hb (hbB.trans (min_le_left _ _)) (w-(t:ℂ)) hch hmi hsource hplus hminus).symm


/-- Exact original tortoise phase; the source amplitude holds every angular
coefficient fixed and keeps the original coordinate normalization. -/
theorem sourceProfile_tortoiseFactor (s w amp J K T : ℂ) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    sourceProfile s w amp J K T z=Complex.exp (w*(tortoiseOf z:ℂ))*
      sourceRemainder s 0 amp J K 1 z*T := by
  have ht := tortoiseOf_neg hz
  have hunit := radialUnit_eq_sqrt (tortoiseOf z) ht
  rw [horizonCoordinate_tortoiseOf hz] at hunit
  have hP := horizonPower_tortoise w (tortoiseOf z) ht
  rw [horizonCoordinate_tortoiseOf hz,hunit] at hP
  have hbase : power w (1+Real.sqrt (1-z))*power (2*s-w) (1+Real.sqrt (1-z))=
      power (2*s) (1+Real.sqrt (1-z)) := by
    rw [power,power,← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (show (1+Real.sqrt (1-z):ℝ)≠0 by positivity))]
    congr 1
    ring
  dsimp only [sourceProfile,sourceRemainder]
  rw [hP]
  simp only [sub_zero,mul_one]
  linear_combination Complex.exp (w*(tortoiseOf z:ℂ))*amp^2*
    (((5*s^2+15*s+4)/4)*J+(1-(z:ℂ))*s*(s-1)/4*((s+2)^2*J-K))*T*hbase

/-- The source-frequency derivative has the original tortoise weight and
the derivative of the unchanged smooth onset, with fixed angular data. -/
theorem continuedSourceProfile_frequency_deriv (s amp J K w : ℂ)
    (hs : w-2*s≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    deriv (fun u => continuedSourceProfile s amp J K u z) w=
      sourceProfile s w amp J K 1 z*((tortoiseOf z:ℂ)*continuedOnset s w+deriv (continuedOnset s) w) := by
  let A := sourceRemainder s 0 amp J K 1 z
  let t : ℂ := (tortoiseOf z:ℂ)
  have he : (fun u => continuedSourceProfile s amp J K u z)=
      (fun u => Complex.exp (u*t)*A*continuedOnset s u) := by
    funext u
    exact sourceProfile_tortoiseFactor s u amp J K (continuedOnset s u) hz
  have hd := (((hasDerivAt_id w).mul_const t).cexp.mul_const A).mul
    (literalOnset_analyticAt s w hs).differentiableAt.hasDerivAt
  simp only [Pi.mul_def, id_eq, one_mul] at hd
  rw [he,hd.deriv,sourceProfile_tortoiseFactor s w amp J K 1 hz]
  dsimp only [A,t]
  ring

/-- Explicit source-only period for the complete original Green metric and
temporal action in its convergence chamber. -/
theorem originalMetricTemporal_eq_sourcePeriod_below (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    ∃ B : ℝ, 0<B ∧ B≤1/2 ∧ ∀ b : ℝ, 0<b → b≤B →
      2*w*(normalizableHorizonPairingFinitePart s chi amp J K b w+
        (∫ z in b..1,mixedDensity s chi amp J K w w z))+
        connection w chi*(deriv (D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp J K) w+
          D4BMOriginalHorizonGreenMatch.greenHorizonAmplitude s chi amp J K w/(2*w))=
        -(∫ z in (0:ℝ)..1,normalizable w chi z*sourceProfile s w amp J K 1 z*
          ((tortoiseOf z:ℂ)*continuedOnset s w+deriv (continuedOnset s) w)) := by
  obtain ⟨B,hB,hBhalf,hI⟩ := originalMetricTemporal_eq_sourceDerivative_below s chi amp J K w hw hwi hs
  refine ⟨B,hB,hBhalf,?_⟩
  intro b hb hbB
  rw [hI b hb hbB]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0:ℝ)≤1)
  intro z hz
  have hsp : w-2*s≠0 := sub_ne_zero.mpr (fun he => by rw [he] at hs; exact (lt_irrefl _ hs))
  dsimp only
  rw [continuedSourceProfile_frequency_deriv s amp J K w hsp hz]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
