import GaloisForLFunctions.RHTower.PrimeCountingLiLandau

/-!
# A lower bound for `Π - L` forces zeros to the left

The mirror of `PrimeCountingLiLandau`.  Let `0 < a ≤ 1`, `K, M ≥ 0` and suppose
`g(t) = K e^{at} + Π(e^t) - L(t) + M ≥ 0` for `t > 0`.  The measure `ν = g dt + e^{at} dt` on
`(0, ∞)` has, for real `σ > 1`,

```text
∫ e^{-σt} dν = (K+1)/(σ-a) + M/σ + log((σ-1)ζ(σ)/σ)/σ ,
```

which is analytic at every real point of `(a, ∞)`.  Landau's theorem puts the abscissa at `a`, so
`B(z) = z(∫ e^{-zt} dν - (K+1)/(z-a) - M/z)` is holomorphic on `Re z > a` with
`e^{B} = (z-1)ζ(z)/z` there: no zero of `ζ` has real part above `a`.  With `π ≤ Π` and
`li(x) ≥ L(log x) - L(log 2)`, a bound `π(x) ≥ li(x) - K√x` for large `x` gives the Riemann
hypothesis.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The clipped density `K e^{at} + Π(e^t) - L(t) + M`. -/
def piLiLowerDensity (a K M : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (K * Real.exp (a * t) + primePowerCount (Real.exp t) - logIntegralCompare t + M)

theorem measurable_piLiLowerDensity (a K M : ℝ) : Measurable (piLiLowerDensity a K M) := by
  unfold piLiLowerDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add ?_ measurable_const
  refine Measurable.sub ?_ continuous_logIntegralCompare.measurable
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).add
    (primePowerCount_mono.measurable.comp Real.measurable_exp)

/-- `g dt + e^{at} dt` on `(0, ∞)`. -/
def piLiLowerMeasure (a K M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (piLiLowerDensity a K M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

theorem piLiLowerDensity_le {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) {t : ℝ}
    (ht : 0 < t) : ((piLiLowerDensity a K M t : ℝ)) ≤ (K + M + 1) * Real.exp t := by
  unfold piLiLowerDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (a * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have h2 := logIntegralCompare_nonneg ht.le
  have h3 : primePowerCount (Real.exp t) ≤ Real.exp t :=
    (primePowerCount_le _).trans (Nat.floor_le (Real.exp_pos t).le)
  have h4 : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hE := Real.exp_pos t
  refine max_le ?_ (by positivity)
  nlinarith

theorem laplaceMass_piLiLower_density_ne_top {a K M σ : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hσ : 1 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (piLiLowerDensity a K M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_piLiLowerDensity a K M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_exp_majorant (C := K + M + 1) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (piLiLowerDensity_le ha hK hM hu) (Real.exp_pos _).le

theorem laplaceMass_piLiLower_eq (a K M σ : ℝ) :
    laplaceMass (piLiLowerMeasure a K M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (piLiLowerDensity a K M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass piLiLowerMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

theorem isAbscissa_piLiLower {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    IsAbscissa (piLiLowerMeasure a K M)
        (sInf {σ : ℝ | laplaceMass (piLiLowerMeasure a K M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (piLiLowerMeasure a K M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (piLiLowerMeasure a K M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_piLiLower_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2:ℝ) ∈ S := by
    show laplaceMass (piLiLowerMeasure a K M) 2 ≠ ⊤
    rw [laplaceMass_piLiLower_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_piLiLower_density_ne_top ha hK hM (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-- Under the lower bound, the real transform of `ν` for `σ > 1`. -/
theorem laplaceReal_piLiLower_eq {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → logIntegralCompare t
      ≤ K * Real.exp (a * t) + primePowerCount (Real.exp t) + M) {σ : ℝ} (hσ : 1 < σ) :
    laplaceReal (piLiLowerMeasure a K M) σ = (K + 1) / (σ - a) + M / σ
      + ((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) - Real.log (σ / (σ - 1))) / σ := by
  have hσ0 : 0 < σ := by linarith
  have hσa : 0 < σ - a := by linarith
  have hexpInt : ∀ b : ℝ, 0 < b → IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) :=
    fun b hb => exp_neg_integrableOn_Ioi 0 hb
  have hI1 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (piLiLowerDensity a K M u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_piLiLowerDensity a K M)]
    refine (integrableOn_exp_majorant (C := K + M + 1) hσ).mono' ?_ ?_
    · exact ((measurable_piLiLowerDensity a K M).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (piLiLowerDensity_le ha hK hM hu) (Real.exp_pos _).le
  have hI2 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthShiftDensity a u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_growthShiftDensity a)]
    refine (hexpInt (σ - a) hσa).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [NNReal.smul_def, smul_eq_mul, growthShiftDensity_coe, ← Real.exp_add]
    ring_nf
  unfold laplaceReal piLiLowerMeasure
  rw [Measure.restrict_add, integral_add_measure hI1 hI2]
  have hshift : ∫ u in Ioi (0:ℝ), Real.exp (-σ * u)
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal)))
      = 1 / (σ - a) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_growthShiftDensity a)]
    rw [← integral_Ioi_exp_neg_mul_eq_one_div hσa]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [NNReal.smul_def, smul_eq_mul, growthShiftDensity_coe, ← Real.exp_add]
    ring_nf
  have hdens : ∫ u in Ioi (0:ℝ), Real.exp (-σ * u)
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (piLiLowerDensity a K M u : ENNReal)))
      = K / (σ - a) + (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) / σ
        - Real.log (σ / (σ - 1)) / σ + M / σ := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_piLiLowerDensity a K M)]
    have hpt : ∀ u ∈ Ioi (0:ℝ), piLiLowerDensity a K M u • Real.exp (-σ * u)
        = ((K * Real.exp (-(σ - a) * u) + primePowerCount (Real.exp u) * Real.exp (-σ * u))
          - logIntegralCompare u * Real.exp (-σ * u)) + M * Real.exp (-σ * u) := by
      intro u hu
      rw [NNReal.smul_def, smul_eq_mul]
      unfold piLiLowerDensity
      rw [Real.coe_toNNReal _ (by linarith [hg u hu])]
      rw [show Real.exp (-(σ - a) * u) = Real.exp (a * u) * Real.exp (-σ * u) by
        rw [← Real.exp_add]; ring_nf]
      ring
    have i1 : IntegrableOn (fun u => K * Real.exp (-(σ - a) * u)) (Ioi 0) :=
      (hexpInt _ hσa).const_mul K
    have i2 := integrableOn_primePowerCount_exp_mul hσ
    have i3 := integrableOn_logIntegralCompare_mul_exp hσ
    have i4 : IntegrableOn (fun u => M * Real.exp (-σ * u)) (Ioi 0) := (hexpInt σ hσ0).const_mul M
    have i12 : IntegrableOn (fun u => K * Real.exp (-(σ - a) * u)
        + primePowerCount (Real.exp u) * Real.exp (-σ * u)) (Ioi 0) := i1.add i2
    have i123 : IntegrableOn (fun u => (K * Real.exp (-(σ - a) * u)
        + primePowerCount (Real.exp u) * Real.exp (-σ * u))
        - logIntegralCompare u * Real.exp (-σ * u)) (Ioi 0) := i12.sub i3
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i123 i4, integral_sub i12 i3,
      integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_Ioi_exp_neg_mul_eq_one_div hσa,
      integral_Ioi_exp_neg_mul_eq_one_div hσ0, integral_logIntegralCompare_mul_exp hσ,
      integral_primePowerCount_exp_mul hσ]
    ring
  rw [hdens, hshift]
  ring

/-- `Φ(z) = (K+1)/(z-a) + M/z + log((z-1)ζ(z)/z)/z`. -/
def piLiLowerContinuation (a K M : ℝ) (z : ℂ) : ℂ :=
  (K + 1) / (z - a) + M / z + Complex.log (zetaResidueUnit z / z) / z

theorem analyticAt_piLiLowerContinuation (a K M : ℝ) {z : ℂ} (hza : z ≠ a) (hz0 : z ≠ 0)
    (hslit : zetaResidueUnit z / z ∈ slitPlane) :
    AnalyticAt ℂ (piLiLowerContinuation a K M) z := by
  unfold piLiLowerContinuation
  refine ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).add
    (analyticAt_const.div analyticAt_id hz0)).add ?_
  exact (((analyticAt_zetaResidueUnit z).div analyticAt_id hz0).clog hslit).div analyticAt_id hz0

theorem piLiLowerContinuation_ofReal {a K M : ℝ} {σ : ℝ} (hσ : 1 < σ) :
    piLiLowerContinuation a K M (σ : ℂ) = (((K + 1) / (σ - a) + M / σ
      + ((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) - Real.log (σ / (σ - 1))) / σ : ℝ)
        : ℂ) := by
  unfold piLiLowerContinuation
  rw [log_zetaResidueUnit_div_ofReal hσ]
  push_cast
  ring

theorem abscissa_piLiLower_eq {a K M : ℝ} (ha0 : 0 < a) (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → logIntegralCompare t
      ≤ K * Real.exp (a * t) + primePowerCount (Real.exp t) + M) :
    IsAbscissa (piLiLowerMeasure a K M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_piLiLower (K := K) (M := M) ha hK hM
  set c : ℝ := sInf {σ : ℝ | laplaceMass (piLiLowerMeasure a K M) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc2 : c ≤ 2 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_piLiLower_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]),
          add_top]
      · show laplaceMass (piLiLowerMeasure a K M) 2 ≠ ⊤
        rw [laplaceMass_piLiLower_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_piLiLower_density_ne_top ha hK hM (by norm_num),
          laplaceMass_volume_ne_top (by linarith)⟩
    have hcpos : 0 < c := lt_trans ha0 hpos
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hca : (c : ℂ) ≠ a := by exact_mod_cast hpos.ne'
    have hcont : ContinuousAt (fun z => zetaResidueUnit z / z) (c : ℂ) :=
      (analyticAt_zetaResidueUnit _).continuousAt.div continuousAt_id hc0
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit z / z ∈ slitPlane ∧ z ≠ 0 ∧ z ≠ a :=
      (hcont.eventually (isOpen_slitPlane.mem_nhds (zetaResidueUnit_div_mem_slitPlane hcpos))).and
        ((eventually_ne_nhds hc0).and (eventually_ne_nhds hca))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := piLiLowerContinuation a K M) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hball hz
      exact analyticAt_piLiLowerContinuation a K M h3 h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (piLiLowerMeasure a K M))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (piLiLowerMeasure a K M) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (piLiLowerMeasure a K M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => piLiLowerContinuation a K M (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have ht0 : 0 < t := lt_trans ha0 hta
        have h1 : AnalyticAt ℂ (piLiLowerContinuation a K M) (t : ℂ) :=
          analyticAt_piLiLowerContinuation a K M (by exact_mod_cast hta.ne')
            (by exact_mod_cast ht0.ne') (zetaResidueUnit_div_mem_slitPlane ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (piLiLowerMeasure a K M) (t : ℂ)) =ᶠ[𝓝 (3:ℝ)]
          (fun t : ℝ => piLiLowerContinuation a K M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3:ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < t := by linarith [ht.1]
        show complexLaplace (piLiLowerMeasure a K M) (t : ℂ) = piLiLowerContinuation a K M (t : ℂ)
        rw [complexLaplace_ofReal, laplaceReal_piLiLower_eq ha hK hM hg ht1,
          piLiLowerContinuation_ofReal ht1]
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (piLiLowerMeasure a K M) (σ : ℂ)
          = piLiLowerContinuation a K M (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **A one-sided lower bound `L(t) ≤ K e^{at} + Π(e^t) + M` excludes zeros of `ζ` from
`Re s > a`.** -/
theorem zetaResidueUnit_ne_zero_of_logIntegralCompare_le {a K M : ℝ} (ha0 : 0 < a) (ha : a ≤ 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → logIntegralCompare t
      ≤ K * Real.exp (a * t) + primePowerCount (Real.exp t) + M) {z : ℂ} (hz : a < z.re) :
    zetaResidueUnit z ≠ 0 := by
  have hc := abscissa_piLiLower_eq ha0 ha hK hM hg
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hne0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by
    rw [h] at hw; simp [hU] at hw; linarith
  have hnea : ∀ w ∈ U, w - a ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set B : ℂ → ℂ := fun w => w * (complexLaplace (piLiLowerMeasure a K M) w
    - (K + 1) / (w - a) - M / w) with hB
  have hBd : DifferentiableOn ℂ B U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => ((K : ℂ) + 1) / (w - a)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hnea w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (M : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id (hne0 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    exact (differentiableAt_id.mul ((h3.sub h1).sub h2)).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ (fun w => Complex.exp (B w) * w) U :=
    ((hBd.cexp).mul differentiableOn_id).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ zetaResidueUnit U := fun w _ => analyticAt_zetaResidueUnit w
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; linarith
  have hreal : ∀ t : ℝ, 1 < t → Complex.exp (B t) * t = zetaResidueUnit t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < t).ne'
    have hBt : B t = Complex.log (zetaResidueUnit t / t) := by
      simp only [hB]
      rw [complexLaplace_ofReal, laplaceReal_piLiLower_eq ha hK hM hg ht,
        log_zetaResidueUnit_div_ofReal ht]
      push_cast
      field_simp
      ring
    have hslit := zetaResidueUnit_div_mem_slitPlane (by linarith : (0:ℝ) < t)
    rw [hBt, Complex.exp_log (slitPlane_ne_zero hslit)]
    field_simp
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] ((2 : ℂ)), Complex.exp (B w) * w = zetaResidueUnit w := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ), Complex.exp (B t) * t = zetaResidueUnit t := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (2 : ℝ) ∈ Ioi (1 : ℝ) by norm_num))] with t ht
      exact hreal t ht
    have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have hEq := hF.eqOn_of_preconnected_of_frequently_eq hG (convex_halfSpace_re_gt a).isPreconnected
    h2U hfreq
  rw [← hEq hz]
  exact mul_ne_zero (Complex.exp_ne_zero _) (hne0 z hz)

/-! ## From `π ≥ li - K√x` to the Riemann hypothesis -/

/-- `π(x) ≤ Π(x)`. -/
theorem primeCounting_le_primePowerCount (x : ℝ) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ primePowerCount x := by
  classical
  unfold primePowerCount
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊x⌋₊) Nat.Prime]
  have hprime : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with n.Prime, eulerLogCoeffReal n
      = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one,
      Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hp : n.Prime := (Finset.mem_filter.mp hn).2
    unfold eulerLogCoeffReal
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp, div_self]
    exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hrest : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, eulerLogCoeffReal n :=
    Finset.sum_nonneg fun n _ => eulerLogCoeffReal_nonneg n
  rw [hprime]
  linarith

/-- **Landau's theorem for `li - π`.**  If `π(x) ≥ li(x) - K√x` for all large `x`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_logIntegral_sub_sqrt_le_primeCounting {K : ℝ}
    (h : ∀ᶠ x : ℝ in atTop,
      (∫ t in (2 : ℝ)..x, 1 / Real.log t) - K * Real.sqrt x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)) :
    RiemannHypothesis := by
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp h
  set x₀ : ℝ := max x₁ 2 with hx₀
  set L₂ : ℝ := logIntegralCompare (Real.log 2) with hL₂
  have hL₂0 : 0 ≤ L₂ := logIntegralCompare_nonneg (Real.log_pos (by norm_num)).le
  have hK0 : 0 ≤ |K| := abs_nonneg K
  have hM0 : 0 ≤ x₀ + L₂ := by rw [hx₀]; linarith [le_max_right x₁ 2]
  have hg : ∀ t, 0 < t → logIntegralCompare t
      ≤ |K| * Real.exp (1 / 2 * t) + primePowerCount (Real.exp t) + (x₀ + L₂) := by
    intro t ht
    have hE := Real.exp_pos (1 / 2 * t)
    have hPc := primePowerCount_nonneg (Real.exp t)
    by_cases hxt : x₀ ≤ Real.exp t
    · have hx2 : 2 ≤ Real.exp t := le_trans (le_max_right _ _) hxt
      have hpi := hx₁ (Real.exp t) (le_trans (le_max_left _ _) hxt)
      have hli := logIntegralCompare_sub_le_integral_inv_log hx2
      rw [Real.log_exp] at hli
      have hpp := primeCounting_le_primePowerCount (Real.exp t)
      rw [sqrt_exp_eq_exp_half_mul] at hpi
      have hKK : -(|K| * Real.exp (1 / 2 * t)) ≤ -(K * Real.exp (1 / 2 * t)) := by
        have := mul_le_mul_of_nonneg_right (le_abs_self K) hE.le
        linarith
      have hx02 : 2 ≤ x₀ := le_max_right _ _
      linarith
    · have h1 := logIntegralCompare_le_exp ht.le
      have hxt' : Real.exp t < x₀ := not_le.mp hxt
      have h3 : 0 ≤ |K| * Real.exp (1 / 2 * t) := mul_nonneg hK0 hE.le
      linarith
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs
  exact zetaResidueUnit_ne_zero_of_logIntegralCompare_le (by norm_num) (by norm_num) hK0 hM0 hg hs

end

end RHTower
