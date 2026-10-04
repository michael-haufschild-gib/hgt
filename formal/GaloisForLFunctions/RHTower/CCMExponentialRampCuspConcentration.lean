import GaloisForLFunctions.RHTower.CCMPrimeDeficitFluxBoundary
import GaloisForLFunctions.RHTower.ChebyshevSchmidtOmega
import GaloisForLFunctions.RHTower.CCMExponentialRampCurrentProjection
import GaloisForLFunctions.RHTower.CCMPrimeQuantileHeightLimit

/-!
# Nonvanishing signed ramp action forces Gamma energy into the cusp

At the literal physical cutoff, the complete exponential-ramp current has
vanishing integral outside every fixed neighborhood of zero displacement.
Its signed total action nevertheless has a fixed nonzero amplitude cofinally,
as forced by the actual deficit flux and unconditional Weil-lag recurrence.

Every fixed cusp window therefore contains arbitrarily large visible Gamma
energy, at times when the signed action is nonzero. Uniform visible energy,
and hence uniform full arithmetic energy, is impossible. This does not exclude
bounded signed action and does not decide the Riemann hypothesis.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped BigOperators
namespace RHTower

private theorem fluxState_bound {c T : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, T ≤ t → |ccmPrimeDeficitIncoming t| ≤ c) :
    |ccmPrimeDeficitFluxState T| ≤ 2*c := by
  apply le_of_tendsto (tendsto_future_integral_ccmPrimeDeficitIncoming T).abs
  filter_upwards [eventually_ge_atTop T] with U hU
  have hi : IntervalIntegrable (fun t : ℝ => c*Real.exp (-(t-T)/2)) volume T U := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hU
    (Filter.Eventually.of_forall fun t (ht : t ∈ Ioc T U) => show
      ‖Real.exp (-(t-T)/2)*ccmPrimeDeficitIncoming t‖ ≤ c*Real.exp (-(t-T)/2) by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (h t ht.1.le) (Real.exp_pos _).le) hi
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => -2*c*Real.exp (-(u-T)/2))
      (c*Real.exp (-(t-T)/2)) t := by
    convert! ((((hasDerivAt_id t).sub_const T).neg.div_const 2).exp).const_mul (-2*c) using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [Real.norm_eq_abs] at hb
  rw [he] at hb
  simp only [sub_self, neg_zero, zero_div, Real.exp_zero, mul_one] at hb
  have hp := mul_nonneg hc (Real.exp_pos (-(U-T)/2)).le
  linarith

/-- The actual incoming critical deficit has nonvanishing tail amplitude. -/
theorem frequently_ccmPrimeDeficitIncoming_abs_gt :
    ∃ᶠ T : ℝ in atTop, poleSharpConstant/4 < |ccmPrimeDeficitIncoming T| := by
  by_contra h
  rw [not_frequently] at h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  have hp := poleSharpConstant_pos
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n, ⟨hn, hnT⟩, hn2⟩ := ((frequently_integerLag_gt (poleSharpConstant/8)
    (by positivity)).and_eventually (hlog.eventually (eventually_ge_atTop T₀)) |>.and_eventually
      (eventually_ge_atTop 2)).exists
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hln := Real.log_pos hnR
  have hb : |ccmPrimeDeficitFluxState (Real.log n)| ≤ 2*(poleSharpConstant/4) :=
    fluxState_bound (by positivity) (fun t ht => le_of_not_gt (hT₀ t (hnT.trans ht)))
  have hin := le_of_not_gt (hT₀ (Real.log n) hnT)
  have hout : ccmPrimeDeficitOutgoing (Real.log n) ≤ 3*(poleSharpConstant/4) := by
    unfold ccmPrimeDeficitOutgoing
    linarith [le_abs_self (ccmPrimeDeficitFluxState (Real.log n)),
      neg_le_abs (ccmPrimeDeficitIncoming (Real.log n))]
  have hcorr : 0 ≤ Real.exp (-Real.log n/2)*
      (Real.log (2*Real.pi)-trivialZeroSeriesReal (Real.exp (Real.log n))) := by
    apply mul_nonneg (Real.exp_pos _).le
    have hz := trivialZeroSeriesReal_le_one (Real.one_le_exp hln.le)
    linarith [one_lt_log_two_pi]
  rw [ccmPrimeDeficitOutgoing_eq_weilLag hln] at hout
  change poleSharpConstant-poleSharpConstant/8 < weilLagFunctionReal (Real.log n) at hn
  linarith
private theorem physical_terminal_zero :
    Tendsto (fun T : ℝ => ccmOutgoingPrimeQuantileBoundary (⌊Real.exp T⌋₊+1)-T)
      atTop (𝓝 0) := by
  have hf : Tendsto (fun T : ℝ => ⌊Real.exp T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have hr := (tendsto_nat_floor_div_atTop (R := ℝ)).comp Real.tendsto_exp_atTop
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  have hgap : Tendsto (fun T : ℝ => Real.log (⌊Real.exp T⌋₊ : ℝ)-T) atTop (𝓝 0) := by
    simpa only [Real.log_one] using hl.congr' (by
      filter_upwards [hf.eventually (eventually_ge_atTop 1)] with T hT
      have hn : (⌊Real.exp T⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ⌊Real.exp T⌋₊ ≠ 0)
      simp only [Function.comp_def, Real.log_div hn (Real.exp_ne_zero _), Real.log_exp])
  have h := (tendsto_ccmOutgoingPrimeQuantileUpper_sub_log.comp hf).add hgap
  simpa only [Function.comp_def, sub_add_sub_cancel, add_zero] using h

private theorem late_cell_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ n, M ≤ n → ∀ r : ℝ, δ ≤ |r| →
      ccmOutgoingQuantileDisplacementCellDensity n r = 0 := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_ccmOutgoingPrimeQuantileCell_near_log δ hδ)
  refine ⟨M, fun n hn r hr => ?_⟩
  have hnot : r ∉ Ioc (ccmOutgoingPrimeQuantileBoundary n-Real.log n)
      (ccmOutgoingPrimeQuantileBoundary (n+1)-Real.log n) := by
    intro hh
    have hm := hM n hn (r+Real.log n) ⟨by linarith [hh.1], by linarith [hh.2]⟩
    simp only [add_sub_cancel_right] at hm
    exact (not_lt_of_ge hr) hm
  exact Set.indicator_of_notMem hnot _

private theorem late_terminal_zero {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ r : ℝ, δ ≤ |r| →
      ccmActualHeadQuantileTerminalDisplacementDensity T (⌊Real.exp T⌋₊+1) r = 0 := by
  have hb := physical_terminal_zero (Metric.ball_mem_nhds (0 : ℝ) hδ)
  filter_upwards [hb] with T hT r hr
  change dist (ccmOutgoingPrimeQuantileBoundary (⌊Real.exp T⌋₊+1)-T) 0 < δ at hT
  simp only [Real.dist_eq, sub_zero, abs_lt] at hT
  unfold ccmActualHeadQuantileTerminalDisplacementDensity
  dsimp only
  split_ifs with h
  · apply Set.indicator_of_notMem
    intro hh
    have ha := abs_of_nonpos hh.2
    linarith [hh.1]
  · rw [Set.indicator_of_notMem, neg_zero]
    intro hh
    have ha := abs_of_nonneg hh.1.le
    linarith [hh.2]

private theorem decay_exp_half :
    Tendsto (fun T : ℝ => Real.exp (-T/2)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  simpa only [neg_div, Function.comp_def, id_eq] using h

private theorem decay_linear_exp_half :
    Tendsto (fun T : ℝ => T*Real.exp (-T/2)) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).const_mul 2
  norm_num only [mul_zero, pow_one, Function.comp_def, id_eq] at h
  refine h.congr fun T => ?_
  rw [neg_div]
  ring

private theorem fixed_cell_outside_zero (n : ℕ) (s : Set ℝ) :
    Tendsto (fun T : ℝ => ∫ r in s, ccmOutgoingQuantileDisplacementCellDensity n r *
      (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n)))
      atTop (𝓝 0) := by
  let A : ℝ := ∫ r in s, ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r
  let B : ℝ := ∫ r in s, ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDerivativeWeight r
  have hA := (integrable_ccmOutgoingQuantileCellDensity_continuousTest n
    ⟨ccmExponentialRampDisplacementWeight, by unfold ccmExponentialRampDisplacementWeight; fun_prop⟩).integrableOn (s := s)
  have hB := (integrable_ccmOutgoingQuantileCellDensity_continuousTest n
    ⟨ccmExponentialRampDerivativeWeight, by unfold ccmExponentialRampDerivativeWeight; fun_prop⟩).integrableOn (s := s)
  change IntegrableOn (fun r => ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r) s at hA
  change IntegrableOn (fun r => ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDerivativeWeight r) s at hB
  have he (T : ℝ) : (∫ r in s, ccmOutgoingQuantileDisplacementCellDensity n r *
      (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n))) =
      Real.exp (Real.log n/2) *
        ((T*Real.exp (-T/2))*A+Real.exp (-T/2)*(B-Real.log n*A)) := by
    have hexp : Real.exp ((Real.log n-T)/2) = Real.exp (Real.log n/2)*Real.exp (-T/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hp (r : ℝ) : ccmOutgoingQuantileDisplacementCellDensity n r *
        (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n)) =
        Real.exp ((Real.log n-T)/2)*((T-Real.log n)*
          (ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDisplacementWeight r)+
            ccmOutgoingQuantileDisplacementCellDensity n r*ccmExponentialRampDerivativeWeight r) := by
      rw [ccmNormalizedExponentialRampTest_increment]
      unfold ccmExponentialRampDisplacementWeight ccmExponentialRampDerivativeWeight
      ring
    simp_rw [hp]
    rw [integral_const_mul, integral_add (hA.const_mul _) hB, integral_const_mul, hexp]
    dsimp only [A, B]
    ring
  simp_rw [he]
  simpa only [zero_mul, zero_add, mul_zero] using
    ((decay_linear_exp_half.mul_const A).add (decay_exp_half.mul_const (B-Real.log n*A))).const_mul (Real.exp (Real.log n/2))

/-- Outside each fixed cusp window, the literal full signed current vanishes in integral. -/
theorem tendsto_ccmActualTimeExponentialRampCurrent_outside_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => ∫ r in {r : ℝ | δ ≤ |r|},
      ccmActualHeadQuantileTestCurrent T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T) r)
      atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := late_cell_zero hδ
  have hf : Tendsto (fun T : ℝ => ⌊Real.exp T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  have he : ∀ᶠ T : ℝ in atTop, (∫ r in {r : ℝ | δ ≤ |r|},
      ccmActualHeadQuantileTestCurrent T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T) r) =
        ∑ n ∈ Finset.range M, ∫ r in {r : ℝ | δ ≤ |r|}, ccmOutgoingQuantileDisplacementCellDensity n r *
          (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n)) := by
    filter_upwards [late_terminal_zero hδ, hf.eventually (eventually_ge_atTop M)] with T hterm hfloor
    have hi (n : ℕ) : IntegrableOn (fun r => ccmOutgoingQuantileDisplacementCellDensity n r *
        (ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n)))
        {r : ℝ | δ ≤ |r|} :=
      (integrable_ccmOutgoingQuantileCellDensity_continuousTest n
        ⟨fun r => ccmNormalizedExponentialRampTest T (Real.log n+r)-ccmNormalizedExponentialRampTest T (Real.log n), by fun_prop⟩).integrableOn
    rw [← integral_finsetSum (Finset.range M) (fun n _ => hi n)]
    apply setIntegral_congr_fun (isClosed_le continuous_const continuous_abs).measurableSet
    intro r hr
    unfold ccmActualHeadQuantileTestCurrent
    rw [hterm r hr, zero_mul, add_zero]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro n hn hnot
    have hnM : M ≤ n := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [hM n hnM r hr, zero_mul]
  have h := tendsto_finsetSum (Finset.range M) (fun n _ => fixed_cell_outside_zero n {r : ℝ | δ ≤ |r|})
  simp only [Finset.sum_const_zero] at h
  exact h.congr' (he.mono fun T hT => hT.symm)
private theorem small_capacity :
    Tendsto (fun δ : ℝ => ∫ r in {r : ℝ | |r| < δ}, ccmExponentialRampGammaCapacityDensity r)
      (𝓝 0) (𝓝 0) := by
  let C := ccmExponentialRampGammaCapacityDensity
  let F (δ : ℝ) : ℝ → ℝ := {r : ℝ | |r| < δ}.indicator C
  have hm (δ : ℝ) : MeasurableSet {r : ℝ | |r| < δ} :=
    (isOpen_lt continuous_abs continuous_const).measurableSet
  have h := tendsto_integral_filter_of_dominated_convergence C
    (F := F) (f := fun _ : ℝ => (0 : ℝ))
    (Eventually.of_forall fun δ => integrable_ccmExponentialRampGammaCapacityDensity.aestronglyMeasurable.indicator (hm δ))
    (Eventually.of_forall fun δ => Eventually.of_forall fun r => show ‖F δ r‖ ≤ C r by
      by_cases hr : |r| < δ
      · change ‖{r : ℝ | |r| < δ}.indicator C r‖ ≤ C r
        rw [indicator_of_mem (show r ∈ {r : ℝ | |r| < δ} from hr), Real.norm_eq_abs,
          abs_of_nonneg (ccmExponentialRampGammaCapacityDensity_nonneg r)]
      · change ‖{r : ℝ | |r| < δ}.indicator C r‖ ≤ C r
        rw [indicator_of_notMem (show r ∉ {r : ℝ | |r| < δ} from hr), norm_zero]
        exact ccmExponentialRampGammaCapacityDensity_nonneg r)
    integrable_ccmExponentialRampGammaCapacityDensity
    (Eventually.of_forall fun r => show Tendsto (fun δ => F δ r) (𝓝 0) (𝓝 0) by
      by_cases hr : r = 0
      · subst r
        have hz : C 0 = 0 := by
          simp [C, ccmExponentialRampGammaCapacityDensity, ccmExponentialRampDisplacementWeight,
            ccmExponentialRampDerivativeWeight]
        simpa only [F, indicator_apply, hz, ite_self] using
          (tendsto_const_nhds (x := (0 : ℝ)) : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
      · apply tendsto_const_nhds.congr'
        filter_upwards [eventually_lt_nhds (abs_pos.mpr hr)] with δ hδ
        symm
        exact indicator_of_notMem (show r ∉ {r : ℝ | |r| < δ} from fun h => (not_lt_of_ge hδ.le) h) _)
  simpa only [F, integral_indicator (hm _), integral_zero] using h

private theorem local_visible_dual_bound (T : ℝ) (N : ℕ) (t : ℝ) (s : Set ℝ) :
    2*t*(∫ r in s, ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r) ≤
      (∫ r in s, ccmExponentialRampVisibleEnergyDensity T N r)+
        t^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) := by
  have hp (r : ℝ) : 2*t*ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r ≤
      ccmExponentialRampVisibleEnergyDensity T N r+t^2*ccmExponentialRampGammaCapacityDensity r := by
    have h := add_nonneg
      (sq_nonneg (ccmExponentialRampProjectedPositionField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDisplacementWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
      (sq_nonneg (ccmExponentialRampProjectedMassField T N r*Real.sqrt (ccmGammaHigherBinetDualDensity |r|)-
        t*ccmExponentialRampDerivativeWeight r*Real.sqrt (ccmGammaHigherBinetModeDensity |r|)))
    rw [ccmExponentialRampWeightedSquare, ccmExponentialRampProjectedField_energy,
      ccmExponentialRampProjectedField_preserves_current] at h
    linarith only [h]
  have h := integral_mono
    (((integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T)).integrableOn (s := s)).const_mul (2*t))
    (((integrable_ccmExponentialRampVisibleEnergyDensity T N).integrableOn (s := s)).add
      (integrable_ccmExponentialRampGammaCapacityDensity.integrableOn.const_mul (t^2))) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_ccmExponentialRampVisibleEnergyDensity T N).integrableOn
    (integrable_ccmExponentialRampGammaCapacityDensity.integrableOn.const_mul (t^2)),
    integral_const_mul, integral_const_mul] at h
  exact h
/-- The literal ramp action retains an unconditional nonzero critical amplitude. -/
theorem frequently_ccmActualTimeExponentialRampAction_abs_gt :
    ∃ᶠ T : ℝ in atTop, poleSharpConstant/8 <
      |ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T)| := by
  have hp := poleSharpConstant_pos
  have ht := decay_linear_exp_half.abs.eventually_lt_const (show |(0 : ℝ)| < poleSharpConstant/8 by rw [abs_zero]; positivity)
  obtain h := (frequently_ccmPrimeDeficitIncoming_abs_gt.and_eventually ht).and_eventually
    (eventually_ge_atTop 0)
  refine h.mono fun T ⟨⟨hT, hsmall⟩, hT0⟩ => ?_
  have he := ccmActualTimeExponentialRampAction_eq_normalizedDeficit (⟨T, hT0⟩ : NNReal)
  change ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T) =
    Real.exp (-T/2)*(ccmLogChebyshevDeficitPrimitive T-T) at he
  have hid : ccmPrimeDeficitIncoming T =
      ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T)+T*Real.exp (-T/2) := by
    rw [he]
    unfold ccmPrimeDeficitIncoming
    ring
  have hb := abs_add_le
    (ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊+1) (ccmNormalizedExponentialRampTest T)) (T*Real.exp (-T/2))
  rw [← hid] at hb
  linarith

/-- The actual visible energy exceeds every bound cofinally inside every fixed cusp window.
This is compatible with bounded signed action: squaring discards cusp cancellation. -/
theorem frequently_ccmActualTimeExponentialRamp_nonvanishing_cuspEnergy
    {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ᶠ T : ℝ in atTop,
      poleSharpConstant/8 < |ccmActualHeadQuantileTestAction T (⌊Real.exp T⌋₊+1)
        (ccmNormalizedExponentialRampTest T)| ∧
      B < ∫ r in {r : ℝ | |r| < δ},
        ccmExponentialRampVisibleEnergyDensity T (⌊Real.exp T⌋₊+1) r := by
  by_contra h
  rw [not_frequently] at h
  have hp := poleSharpConstant_pos
  let k := poleSharpConstant/8
  have hk : 0 < k := by dsimp [k]; positivity
  let B' := max B 0+1
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hBB : B < B' := by dsimp [B']; linarith [le_max_left B 0]
  let t := 2*B'/k
  have ht : 0 < t := by dsimp [t]; positivity
  have hthreshold : (0 : ℝ) < k^2/(4*B') := by positivity
  obtain ⟨η, hη, hηcap⟩ := Metric.eventually_nhds_iff.mp
    (small_capacity.eventually (eventually_lt_nhds hthreshold))
  let ε := min δ η/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ η]
  have hεη : ε < η := by dsimp [ε]; linarith [min_le_right δ η]
  have hcap : (∫ r in {r : ℝ | |r| < ε}, ccmExponentialRampGammaCapacityDensity r) < k^2/(4*B') :=
    hηcap (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεη)
  have hout := (tendsto_ccmActualTimeExponentialRampCurrent_outside_zero hε).abs.eventually_lt_const
    (show |(0 : ℝ)| < k/2 by rw [abs_zero]; positivity)
  obtain ⟨T, ⟨hT, hE⟩, hO⟩ :=
    ((frequently_ccmActualTimeExponentialRampAction_abs_gt.and_eventually h).and_eventually hout).exists
  have hEbound := le_of_not_gt (fun hh => hE ⟨hT, hh⟩)
  let N := ⌊Real.exp T⌋₊+1
  let s : Set ℝ := {r : ℝ | |r| < ε}
  let I : ℝ := ∫ r in s, ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r
  have hEin : (∫ r in s, ccmExponentialRampVisibleEnergyDensity T N r) ≤ B := by
    refine (setIntegral_mono_set
      (integrable_ccmExponentialRampVisibleEnergyDensity T N).integrableOn
      (Eventually.of_forall fun r => ccmExponentialRampVisibleEnergyDensity_nonneg T N r)
      (Eventually.of_forall fun r (hr : r ∈ s) => show |r| < δ from hr.trans hεδ)).trans hEbound
  have hplus := local_visible_dual_bound T N t s
  have hminus := local_visible_dual_bound T N (-t) s
  have hab : 2*t*|I| ≤ B+t^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) := by
    have hp' : 2*t*I ≤ B+t^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) := by linarith only [hplus, hEin]
    have hm' : -(2*t*I) ≤ B+t^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) := by
      simpa only [neg_sq] using (show -(2*t*I) ≤ B+(-t)^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) by
        linarith only [hminus, hEin])
    rcases le_total 0 I with hi | hi
    · rw [abs_of_nonneg hi]
      exact hp'
    · rw [abs_of_nonpos hi]
      linarith only [hm']
  have hcap' : t^2*(∫ r in s, ccmExponentialRampGammaCapacityDensity r) < B' := by
    have hm := mul_lt_mul_of_pos_left hcap (sq_pos_of_pos ht)
    have he : t^2*(k^2/(4*B')) = B' := by dsimp [t]; field_simp [ne_of_gt hk, ne_of_gt hB']; ring
    exact he ▸ hm
  have hI : |I| < k/2 := by
    have htk : 2*t*(k/2) = 2*B' := by dsimp [t]; field_simp [ne_of_gt hk, ne_of_gt hB']
    have hl : 2*t*|I| < 2*t*(k/2) := by rw [htk]; linarith
    exact (mul_lt_mul_iff_right₀ (by positivity : 0 < 2*t)).mp hl
  have hs : MeasurableSet s := (isOpen_lt continuous_abs continuous_const).measurableSet
  have hsplit := integral_add_compl hs
    (integrable_ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T))
  have hsc : sᶜ = {r : ℝ | ε ≤ |r|} := by ext r; simp [s, not_lt]
  rw [hsc] at hsplit
  change I+(∫ r in {r : ℝ | ε ≤ |r|}, ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r) =
    ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T) at hsplit
  have htriangle := abs_add_le I
    (∫ r in {r : ℝ | ε ≤ |r|}, ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r)
  rw [hsplit] at htriangle
  change k < |ccmActualHeadQuantileTestAction T N (ccmNormalizedExponentialRampTest T)| at hT
  change |∫ r in {r : ℝ | ε ≤ |r|}, ccmActualHeadQuantileTestCurrent T N (ccmNormalizedExponentialRampTest T) r| < k/2 at hO
  linarith

/-- Cusp visible energy has no eventual uniform bound. -/
theorem frequently_ccmActualTimeExponentialRampVisibleEnergy_cusp_gt
    {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ᶠ T : ℝ in atTop, B < ∫ r in {r : ℝ | |r| < δ},
      ccmExponentialRampVisibleEnergyDensity T (⌊Real.exp T⌋₊+1) r :=
  (frequently_ccmActualTimeExponentialRamp_nonvanishing_cuspEnergy hδ B).mono fun _ h => h.2

/-- No eventual uniform bound exists for the full actual visible energy. -/
theorem frequently_ccmActualTimeExponentialRampVisibleEnergy_gt (B : ℝ) :
    ∃ᶠ T : ℝ in atTop, B < ccmExponentialRampVisibleEnergy T (⌊Real.exp T⌋₊+1) := by
  refine (frequently_ccmActualTimeExponentialRampVisibleEnergy_cusp_gt (δ := 1) (by norm_num) B).mono fun T hT => ?_
  exact hT.trans_le (setIntegral_le_integral
    (integrable_ccmExponentialRampVisibleEnergyDensity T (⌊Real.exp T⌋₊+1))
    (Eventually.of_forall fun r => ccmExponentialRampVisibleEnergyDensity_nonneg T (⌊Real.exp T⌋₊+1) r))

end RHTower
