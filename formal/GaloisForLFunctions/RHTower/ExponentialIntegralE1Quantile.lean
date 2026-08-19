import GaloisForLFunctions.RHTower.ExponentialIntegralE1

/-!
# The retention quantile of the exponential integral

`E₁` is strictly decreasing and locally Lipschitz on the positive half line, diverges at the
origin and vanishes at infinity.  Consequently `Q(c) = exp(-E₁(c))` is a continuous strictly
increasing bijection of the positive half line onto `(0,1)`, and every retained fraction
`q ∈ (0,1)` is realized by a unique scaled prime aperture `c_q`.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace RHTower

noncomputable section

theorem exp_neg_div_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ Real.exp (-u) / u :=
  div_nonneg (Real.exp_pos _).le hu.le

theorem expIntegralOne_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ expIntegralOne c := by
  rw [expIntegralOne]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  exact exp_neg_div_nonneg (lt_trans hc (mem_Ioi.mp hu))

theorem expIntegralOne_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    expIntegralOne a - expIntegralOne b = ∫ u in Ioc a b, Real.exp (-u) / u := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hunion : Ioi a = Ioc a b ∪ Ioi b := by
    ext u
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      by_cases hu : u ≤ b
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr (not_le.mp hu)
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · linarith
  have hdisj : Disjoint (Ioc a b) (Ioi b) := by
    rw [Set.disjoint_left]
    rintro u ⟨-, hub⟩ hub'
    exact absurd (mem_Ioi.mp hub') (not_lt.mpr hub)
  have hsplit : expIntegralOne a
      = (∫ u in Ioc a b, Real.exp (-u) / u) + expIntegralOne b := by
    rw [expIntegralOne, expIntegralOne, hunion,
      MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
        ((integrableOn_exp_neg_div_Ioi ha).mono_set Set.Ioc_subset_Ioi_self)
        (integrableOn_exp_neg_div_Ioi hb)]
  rw [hsplit]
  ring

theorem expIntegralOne_strictAntiOn : StrictAntiOn expIntegralOne (Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := mem_Ioi.mp ha
  have hpos : 0 < ∫ u in Ioc a b, Real.exp (-u) / u := by
    have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioc a b) volume :=
      (integrableOn_exp_neg_div_Ioi ha0).mono_set Set.Ioc_subset_Ioi_self
    have hcont : IntervalIntegrable (fun u : ℝ => Real.exp (-u) / u) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
      exact hint
    have h := intervalIntegral.intervalIntegral_pos_of_pos_on hcont
      (fun u hu => div_pos (Real.exp_pos _) (lt_trans ha0 hu.1)) hab
    rwa [intervalIntegral.integral_of_le hab.le] at h
  have hsub := expIntegralOne_sub ha0 hab.le
  linarith [hsub ▸ hpos]

/-- `E₁` is Lipschitz with constant `1/δ` above `δ`. -/
theorem abs_expIntegralOne_sub_le {δ a b : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hab : a ≤ b) :
    |expIntegralOne a - expIntegralOne b| ≤ (b - a) / δ := by
  have ha0 : 0 < a := lt_of_lt_of_le hδ ha
  rw [expIntegralOne_sub ha0 hab]
  have hbound : ∀ u ∈ Ioc a b, ‖Real.exp (-u) / u‖ ≤ δ⁻¹ := by
    intro u hu
    have hu0 : 0 < u := lt_trans ha0 hu.1
    have hδu : δ ≤ u := le_trans ha hu.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_neg_div_nonneg hu0)]
    have h1 : Real.exp (-u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    calc Real.exp (-u) / u = Real.exp (-u) * u⁻¹ := div_eq_mul_inv _ _
      _ ≤ 1 * u⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hu0.le)
      _ = u⁻¹ := one_mul _
      _ ≤ δ⁻¹ := by gcongr
  have hmeas : volume (Ioc a b) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmeas hbound
  have hvol : volume.real (Ioc a b) = b - a := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  rw [hvol, Real.norm_eq_abs] at h
  rw [div_eq_inv_mul]
  linarith [h]

theorem abs_expIntegralOne_sub_le' {δ a b : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) :
    |expIntegralOne a - expIntegralOne b| ≤ |a - b| / δ := by
  rcases le_total a b with hab | hab
  · have h := abs_expIntegralOne_sub_le hδ ha hab
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub]
    exact h
  · have h := abs_expIntegralOne_sub_le hδ hb hab
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    exact h

theorem continuousOn_expIntegralOne : ContinuousOn expIntegralOne (Ioi 0) := by
  intro c hc
  have hc0 : 0 < c := mem_Ioi.mp hc
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (c / 2) (ε * c / 4), by positivity, fun {x} _ hdist => ?_⟩
  have hd : |x - c| < min (c / 2) (ε * c / 4) := by rwa [Real.dist_eq] at hdist
  have h1 : |x - c| < c / 2 := lt_of_lt_of_le hd (min_le_left _ _)
  have h2 : |x - c| < ε * c / 4 := lt_of_lt_of_le hd (min_le_right _ _)
  have hxlow : c / 2 ≤ x := by
    have := abs_lt.mp h1
    linarith [this.1]
  have hclow : c / 2 ≤ c := by linarith
  have hbound := abs_expIntegralOne_sub_le' (by positivity : (0:ℝ) < c / 2) hxlow hclow
  rw [Real.dist_eq]
  have hcpos : (0 : ℝ) < c / 2 := by positivity
  have hstep : |x - c| / (c / 2) < (ε * c / 4) / (c / 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right h2 (inv_pos.mpr hcpos)
  calc |expIntegralOne x - expIntegralOne c| ≤ |x - c| / (c / 2) := hbound
    _ < (ε * c / 4) / (c / 2) := hstep
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

/-! ### The two ends -/

theorem expIntegralOne_le_exp_div {c : ℝ} (hc : 0 < c) :
    expIntegralOne c ≤ Real.exp (-c) / c := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi c) volume :=
    (exp_neg_integrableOn_Ioi c (b := 1) one_pos).congr_fun (fun v _ => by simp) measurableSet_Ioi
  have hmono : ∫ u in Ioi c, Real.exp (-u) / u ≤ ∫ u in Ioi c, Real.exp (-u) / c := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_exp_neg_div_Ioi hc)
      (hexp.div_const c) measurableSet_Ioi fun u hu => ?_
    have hcu : c ≤ u := (mem_Ioi.mp hu).le
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hc hcu
  have hval : ∫ u in Ioi c, Real.exp (-u) / c = Real.exp (-c) / c := by
    rw [MeasureTheory.integral_div, integral_exp_neg_Ioi]
  rw [expIntegralOne, ← hval]
  exact hmono

theorem tendsto_expIntegralOne_atTop : Tendsto expIntegralOne atTop (nhds 0) := by
  have hupper : Tendsto (fun c : ℝ => Real.exp (-c) / c) atTop (nhds 0) := by
    have h1 : Tendsto (fun c : ℝ => Real.exp (-c)) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun c : ℝ => c⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h3 := h1.mul h2
    rw [mul_zero] at h3
    exact h3.congr fun c => (div_eq_mul_inv _ _).symm
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
    exact expIntegralOne_nonneg hc
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
    exact expIntegralOne_le_exp_div hc

theorem integrableOn_inv_Ioc {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    IntegrableOn (fun u : ℝ => u⁻¹) (Ioc c 1) volume := by
  have hsub : Set.uIcc c 1 ⊆ {x : ℝ | x ≠ 0} := by
    rw [Set.uIcc_of_le hc1]
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le hc hx.1)
  have hcont : ContinuousOn (fun u : ℝ => u⁻¹) (Set.uIcc c 1) :=
    continuousOn_inv₀.mono hsub
  have hii := hcont.intervalIntegrable (μ := volume)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc1).mp hii

theorem integral_inv_Ioc {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∫ u in Ioc c 1, u⁻¹ = -Real.log c := by
  have h := integral_inv_of_pos hc (zero_lt_one : (0:ℝ) < 1)
  rw [intervalIntegral.integral_of_le hc1] at h
  rw [h, one_div, Real.log_inv]

/-- Near the origin the exponential integral dominates the logarithm. -/
theorem exp_neg_one_mul_neg_log_le {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Real.exp (-1) * (-Real.log c) ≤ expIntegralOne c := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioc c 1) volume :=
    (integrableOn_exp_neg_div_Ioi hc).mono_set Set.Ioc_subset_Ioi_self
  have hlow : IntegrableOn (fun u : ℝ => Real.exp (-1) * u⁻¹) (Ioc c 1) volume :=
    (integrableOn_inv_Ioc hc hc1).const_mul _
  have hcmp : ∫ u in Ioc c 1, Real.exp (-1) * u⁻¹ ≤ ∫ u in Ioc c 1, Real.exp (-u) / u := by
    refine MeasureTheory.setIntegral_mono_on hlow hint measurableSet_Ioc fun u hu => ?_
    have hu0 : 0 < u := lt_trans hc hu.1
    have hexp : Real.exp (-1) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith [hu.2])
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr hu0.le)
  have hval : ∫ u in Ioc c 1, Real.exp (-1) * u⁻¹ = Real.exp (-1) * (-Real.log c) := by
    rw [MeasureTheory.integral_const_mul, integral_inv_Ioc hc hc1]
  have hsub := expIntegralOne_sub hc hc1
  have hpos1 : 0 ≤ expIntegralOne 1 := expIntegralOne_nonneg one_pos
  rw [hval] at hcmp
  linarith [hsub, hcmp, hpos1]

theorem tendsto_expIntegralOne_nhdsGT : Tendsto expIntegralOne (𝓝[>] (0:ℝ)) atTop := by
  have hlog : Tendsto (fun c : ℝ => Real.exp (-1) * (-Real.log c)) (𝓝[>] (0:ℝ)) atTop := by
    have h : Tendsto (fun c : ℝ => -Real.log c) (𝓝[>] (0:ℝ)) atTop :=
      Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    exact Filter.Tendsto.const_mul_atTop (Real.exp_pos _) h
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with c hc hc1
  exact exp_neg_one_mul_neg_log_le (mem_Ioi.mp hc) hc1

/-! ### The retention quantile -/

theorem expIntegralOne_pos {c : ℝ} (hc : 0 < c) : 0 < expIntegralOne c := by
  have h := expIntegralOne_strictAntiOn (mem_Ioi.mpr hc)
    (mem_Ioi.mpr (by linarith : (0:ℝ) < c + 1)) (by linarith)
  have h2 := expIntegralOne_nonneg (show (0:ℝ) < c + 1 by linarith)
  linarith

/-- The retained-fraction profile `Q(c) = exp(-E₁(c))`. -/
def retentionQuantile (c : ℝ) : ℝ := Real.exp (-expIntegralOne c)

theorem retentionQuantile_pos (c : ℝ) : 0 < retentionQuantile c := Real.exp_pos _

theorem retentionQuantile_lt_one {c : ℝ} (hc : 0 < c) : retentionQuantile c < 1 := by
  rw [retentionQuantile, Real.exp_lt_one_iff]
  have := expIntegralOne_pos hc
  linarith

/-- **`Q` is strictly increasing.** -/
theorem retentionQuantile_strictMonoOn : StrictMonoOn retentionQuantile (Ioi 0) := by
  intro a ha b hb hab
  have h := expIntegralOne_strictAntiOn ha hb hab
  exact Real.exp_lt_exp.mpr (by linarith)

theorem continuousOn_retentionQuantile : ContinuousOn retentionQuantile (Ioi 0) :=
  Real.continuous_exp.comp_continuousOn continuousOn_expIntegralOne.neg

/-- **`Q` vanishes at the origin.** -/
theorem tendsto_retentionQuantile_nhdsGT :
    Tendsto retentionQuantile (𝓝[>] (0:ℝ)) (nhds 0) := by
  have h : Tendsto (fun c : ℝ => -expIntegralOne c) (𝓝[>] (0:ℝ)) atBot :=
    Filter.tendsto_neg_atTop_atBot.comp tendsto_expIntegralOne_nhdsGT
  exact Real.tendsto_exp_atBot.comp h

/-- **`Q` saturates at one.** -/
theorem tendsto_retentionQuantile_atTop : Tendsto retentionQuantile atTop (nhds 1) := by
  have h : Tendsto (fun c : ℝ => -expIntegralOne c) atTop (nhds 0) := by
    have := tendsto_expIntegralOne_atTop.neg
    rwa [neg_zero] at this
  have h2 := (Real.continuous_exp.tendsto 0).comp h
  rw [Real.exp_zero] at h2
  exact h2

/-- **The quantile law.**  Every retained fraction `q ∈ (0,1)` is realized by a unique scaled
prime aperture `c_q`. -/
theorem existsUnique_retentionQuantile {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    ∃! c : ℝ, 0 < c ∧ retentionQuantile c = q := by
  obtain ⟨a, haq, ha0⟩ : ∃ a : ℝ, retentionQuantile a < q ∧ a ∈ Ioi (0:ℝ) := by
    have hev : ∀ᶠ c in 𝓝[>] (0:ℝ), retentionQuantile c < q :=
      tendsto_retentionQuantile_nhdsGT (Iio_mem_nhds h0)
    exact (hev.and self_mem_nhdsWithin).exists
  obtain ⟨b, hbq, hb0⟩ : ∃ b : ℝ, q < retentionQuantile b ∧ b ∈ Ioi (0:ℝ) := by
    have hev : ∀ᶠ c in atTop, q < retentionQuantile c :=
      tendsto_retentionQuantile_atTop (Ioi_mem_nhds h1)
    exact (hev.and (eventually_gt_atTop (0:ℝ))).exists
  have hab : a < b := by
    by_contra hcon
    have hba : b ≤ a := not_lt.mp hcon
    rcases eq_or_lt_of_le hba with heq | hlt
    · rw [heq] at hbq; linarith
    · have := retentionQuantile_strictMonoOn hb0 ha0 hlt
      linarith
  have hsub : Icc a b ⊆ Ioi (0:ℝ) := by
    intro x hx
    exact lt_of_lt_of_le (mem_Ioi.mp ha0) hx.1
  have hcont : ContinuousOn retentionQuantile (Icc a b) :=
    continuousOn_retentionQuantile.mono hsub
  have hmem : q ∈ Icc (retentionQuantile a) (retentionQuantile b) := ⟨haq.le, hbq.le⟩
  obtain ⟨c, hc, hcq⟩ := intermediate_value_Icc hab.le hcont hmem
  refine ⟨c, ⟨lt_of_lt_of_le (mem_Ioi.mp ha0) hc.1, hcq⟩, ?_⟩
  rintro d ⟨hd0, hdq⟩
  refine retentionQuantile_strictMonoOn.injOn (mem_Ioi.mpr hd0)
    (mem_Ioi.mpr (lt_of_lt_of_le (mem_Ioi.mp ha0) hc.1)) ?_
  rw [hdq, hcq]

end

end RHTower
