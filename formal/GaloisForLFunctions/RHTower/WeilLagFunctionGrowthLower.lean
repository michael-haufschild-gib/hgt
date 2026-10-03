import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth

/-!
# Growth of the lag function from below and zero-free half-planes

The mirror of `re_le_half_add_of_weilLagFunctionReal_le_exp`: if `Φ(L) ≥ -M e^{aL}` for all `L ≥ 0`
with `0 ≤ a < ½`, every zero copy has real part at most `½ + a`.  The nonnegative density is
`M e^{au} + Φ(u)`; with the shift measure `e^{au} du` its Laplace transform is
`(M+1)/(s−a) + G(s)` on `Re s > ½`, Landau's theorem puts the abscissa at `a`, and `G` extends to
`Re s > a`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The growth measure -/

/-- The clipped density `max(M e^{au} + Φ(u), 0)`. -/
def growthDensityLower (a M : ℝ) (u : ℝ) : NNReal :=
  Real.toNNReal (M * Real.exp (a * u) + weilLagFunctionReal u)

theorem measurable_growthDensityLower (a M : ℝ) : Measurable (growthDensityLower a M) :=
  ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).add
    measurable_weilLagFunctionReal).real_toNNReal

/-- `(M e^{au} + Φ) du + e^{au} du` on `(0,∞)`. -/
def growthMeasureLower (a M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthDensityLower a M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

/-- The density is at most `(|M| + W) e^{u/2}` for `u > 0`, when `a ≤ ½`. -/
theorem growthDensityLower_le {a M : ℝ} (ha : a ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    ((growthDensityLower a M u : ℝ)) ≤ (|M| + lagWeightTotal) * Real.exp (u / 2) := by
  unfold growthDensityLower
  rw [Real.coe_toNNReal']
  have h1 := abs_weilLagFunctionReal_le u
  rw [abs_of_pos hu] at h1
  have h2 : Real.exp (a * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have h3 : M * Real.exp (a * u) ≤ |M| * Real.exp (u / 2) := by
    calc M * Real.exp (a * u) ≤ |M| * Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le
      _ ≤ |M| * Real.exp (u / 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg M)
  have h4 := le_abs_self (weilLagFunctionReal u)
  have hW := lagWeightTotal_nonneg
  have hE := Real.exp_pos (u / 2)
  rcases le_or_gt (M * Real.exp (a * u) + weilLagFunctionReal u) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h.le]; nlinarith

theorem laplaceMass_growthLower_density_ne_top {a M σ : ℝ} (ha : a ≤ 1 / 2) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (growthDensityLower a M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_growthDensityLower a M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_growth_majorant (C := |M| + lagWeightTotal) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (growthDensityLower_le ha hu) (Real.exp_pos _).le

theorem laplaceMass_growthLower_eq (a M σ : ℝ) :
    laplaceMass (growthMeasureLower a M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthDensityLower a M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass growthMeasureLower
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

/-- The real points of convergence lie in `(a, ∞)`, contain `1`, and form an up-set; their infimum
is the abscissa, which is at least `a`. -/
theorem isAbscissa_growthLower {a M : ℝ} (ha : a < 1 / 2) :
    IsAbscissa (growthMeasureLower a M)
        (sInf {σ : ℝ | laplaceMass (growthMeasureLower a M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (growthMeasureLower a M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (growthMeasureLower a M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_growthLower_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (growthMeasureLower a M) 1 ≠ ⊤
    rw [laplaceMass_growthLower_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_growthLower_density_ne_top ha.le (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The complex transform on `Re s > ½` -/

/-- The candidate analytic continuation `H(z) = (M+1)/(z − a) + G(z)`. -/
def growthLowerContinuation (a M : ℝ) (z : ℂ) : ℂ := (M + 1) / (z - a) + lagPoleSeries z

theorem analyticAt_growthLowerContinuation (a M : ℝ) {z : ℂ} (hza : z ≠ a)
    (hz : xi (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (growthLowerContinuation a M) z := by
  unfold growthLowerContinuation
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).add
    (analyticAt_lagPoleSeries hz)

theorem integrable_cexp_growthLower_density {a M : ℝ} (ha : a ≤ 1 / 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (fun u : ℝ => Complex.exp (-s * (u : ℂ)))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthDensityLower a M u : ENNReal))).restrict (Ioi 0)) := by
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self,
    integrable_withDensity_iff_integrable_smul (measurable_growthDensityLower a M)]
  refine (integrableOn_growth_majorant (C := |M| + lagWeightTotal) (by exact hs)).mono' ?_ ?_
  · exact ((measurable_growthDensityLower a M).coe_nnreal_real.aestronglyMeasurable.smul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
      norm_cexp_neg_mul]
    exact mul_le_mul_of_nonneg_right (growthDensityLower_le ha hu) (Real.exp_pos _).le

/-- On `Re s > ½` the complex Laplace transform of the growth measure is `H(s)`. -/
theorem complexLaplace_growthLower_eq {a M : ℝ} (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → -(M * Real.exp (a * L))
        ≤ weilLagFunctionReal L) {s : ℂ} (hs : 1 / 2 < s.re) :
    complexLaplace (growthMeasureLower a M) s = growthLowerContinuation a M s := by
  have hs0 : 0 < s.re := by linarith
  have hsa : a < s.re := by linarith
  have hsa' : 0 < (s - a).re := by simp; linarith
  have hcexp : Continuous (fun u : ℝ => Complex.exp (-s * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hexpInt : IntegrableOn (fun u : ℝ => Complex.exp (-s * (u : ℂ))) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hs0).mono' hcexp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  have hexpInt' : IntegrableOn (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) (Ioi 0) := by
    have hc : Continuous (fun u : ℝ => Complex.exp (-(s - a) * (u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (exp_neg_integrableOn_Ioi 0 hsa').mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (norm_cexp_neg_mul _ u))
  unfold complexLaplace growthMeasureLower growthLowerContinuation
  rw [Measure.restrict_add, integral_add_measure (integrable_cexp_growthLower_density ha.le hs)
    (integrable_cexp_growthShift hsa), complexLaplace_growthShift hsa]
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self,
    integral_withDensity_eq_integral_smul (measurable_growthDensityLower a M)]
  have hpt : ∀ u ∈ Ioi (0:ℝ), growthDensityLower a M u • Complex.exp (-s * (u : ℂ)) =
      (M : ℂ) * Complex.exp (-(s - a) * (u : ℂ)) +
        ((weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    intro u hu
    rw [NNReal.smul_def, Complex.real_smul]
    unfold growthDensityLower
    rw [Real.coe_toNNReal _ (by linarith [hM u (le_of_lt hu)])]
    push_cast
    rw [show Complex.exp (-(s - a) * (u : ℂ)) = Complex.exp (a * u) * Complex.exp (-s * (u : ℂ)) by
      rw [← Complex.exp_add]; congr 1; ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add (hexpInt'.const_mul _) (integrable_weilLag_mul_cexp hs),
    integral_const_mul, integral_cexp_neg_mul_Ioi hsa']
  have hΦ : ∫ u in Ioi (0:ℝ), (weilLagFunctionReal u : ℂ) * Complex.exp (-s * (u : ℂ)) =
      lagPoleSeries s := by
    rw [← integral_weilLagFunction_mul_cexp hs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      beta_reduce; rw [weilLagFunction_eq_ofReal])
  rw [hΦ]
  have hne : (s - a) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-! ## Landau: the abscissa is `a` -/

theorem abscissa_growthLower_eq {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → -(M * Real.exp (a * L)) ≤ weilLagFunctionReal L) :
    IsAbscissa (growthMeasureLower a M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_growthLower (M := M) ha
  set c : ℝ := sInf {σ : ℝ | laplaceMass (growthMeasureLower a M) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc34 : c ≤ 3 / 4 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_growthLower_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]),
            add_top]
      · show laplaceMass (growthMeasureLower a M) (3 / 4) ≠ ⊤
        rw [laplaceMass_growthLower_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_growthLower_density_ne_top ha.le (by norm_num),
          laplaceMass_volume_ne_top (by linarith)⟩
    have hcpos : 0 < c := lt_of_le_of_lt ha0 hpos
    have hne : xi ((c : ℂ) + 1 / 2) ≠ 0 := xi_ofReal_add_half_ne_zero hcpos
    have hopen : IsOpen {z : ℂ | xi z ≠ 0}
        := isOpen_ne_fun xi_differentiable.continuous continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hne
    set δ : ℝ := min (c - a) d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (by linarith) hd)
    have hδc : δ ≤ (c - a) / 2 := by rw [hδdef]; linarith [min_le_left (c - a) d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right (c - a) d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := growthLowerContinuation a M) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : (c + a) / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hza : z ≠ a := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hzxi : xi (z + 1 / 2) ≠ 0 := by
        apply hball
        rw [Metric.mem_ball, Complex.dist_eq]
        calc ‖z + 1 / 2 - ((c : ℂ) + 1 / 2)‖ = ‖z - c‖ := by congr 1; ring
          _ < δ := hz
          _ ≤ d / 2 := hδd
          _ < d := by linarith
      exact analyticAt_growthLowerContinuation a M hza hzxi
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (growthMeasureLower a M))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ
          => complexLaplace (growthMeasureLower a M) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (growthMeasureLower a M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => growthLowerContinuation a M (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have ht0 : 0 < t := lt_of_le_of_lt ha0 hta
        have h1 : AnalyticAt ℂ (growthLowerContinuation a M) (t : ℂ) :=
          analyticAt_growthLowerContinuation a M (by exact_mod_cast hta.ne')
            (xi_ofReal_add_half_ne_zero ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by show c < 1; linarith
      have hfg : (fun t : ℝ => complexLaplace (growthMeasureLower a M) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => growthLowerContinuation a M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        exact complexLaplace_growthLower_eq ha hM (by simpa using ht.1)
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ : complexLaplace (growthMeasureLower a M) (σ : ℂ)
          = growthLowerContinuation a M (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-! ## The growth criterion -/

/-- **One-sided exponential growth from below bounds the real parts of the zeros.**
If `Φ(L) ≥ -M e^{aL}` for all `L ≥ 0` with `0 ≤ a < ½`, every zero copy has real part at most
`½ + a`. -/
theorem re_le_half_add_of_neg_exp_le_weilLagFunctionReal {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ L, 0 ≤ L → -(M * Real.exp (a * L)) ≤ weilLagFunctionReal L) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have hc := abscissa_growthLower_eq ha0 ha hM
  refine re_le_half_add_of_lagPoleSeries_extension ha0
    (F := fun z => complexLaplace (growthMeasureLower a M) z - ((M : ℂ) + 1) / (z - a)) ?_ ?_ q
  · intro z hza _
    have hz : z - a ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((M : ℂ) + 1) / (z - a)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hz
    have h2 : DifferentiableAt ℂ (complexLaplace (growthMeasureLower a M)) z :=
      (hasDerivAt_complexLaplace hc hza).differentiableAt
    exact h2.sub h1
  · intro s hs
    rw [complexLaplace_growthLower_eq ha hM hs]
    unfold growthLowerContinuation
    ring

end

end RHTower
