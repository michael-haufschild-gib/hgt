import GaloisForLFunctions.RHTower.PrimePowerCountLaplace
import GaloisForLFunctions.RHTower.LogIntegralLaplaceComparison
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.OneSignTailImpossible
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# A one-sided bound for `Π - L` forces zeros to the left

Let `0 < a ≤ 1`, `K, M ≥ 0` and suppose `g(t) = K e^{at} + L(t) - Π(e^t) + M ≥ 0` for `t > 0`.
With the shift measure `e^{at} dt`, the measure `ν = g dt + e^{at} dt` on `(0, ∞)` has, for real
`σ > 1`,

```text
∫ e^{-σt} dν = (K+1)/(σ-a) + M/σ - log((σ-1)ζ(σ)/σ)/σ ,
```

(`integral_primePowerCount_exp_mul`, `integral_logIntegralCompare_mul_exp`).  The right side is
analytic at every real point of `(a, ∞)`, because `(σ-1)ζ(σ)/σ > 0` there; Landau's theorem puts the
abscissa at `a`, so `B(z) = z((K+1)/(z-a) + M/z - ∫ e^{-zt} dν)` is holomorphic on `Re z > a` with
`e^{B} = (z-1)ζ(z)/z` on `(1, ∞)`, hence on `Re z > a`: no zero of `ζ` has real part above `a`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **The residue unit is a positive real on `(0, ∞)`.** -/
theorem exists_zetaResidueUnit_ofReal_eq_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ r : ℝ, 0 < r ∧ zetaResidueUnit (σ : ℂ) = (r : ℂ) := by
  rcases lt_trichotomy σ 1 with h1 | h1 | h1
  · obtain ⟨x, hx, hzx⟩ := riemannZeta_real_strip_neg hσ h1
    have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne
    refine ⟨(σ - 1) * x, mul_pos_of_neg_of_neg (by linarith) hx, ?_⟩
    rw [zetaResidueUnit, Function.update_of_ne hne, hzx]
    push_cast; ring
  · subst h1
    exact ⟨1, one_pos, by simp⟩
  · obtain ⟨hexp, him⟩ := log_riemannZeta_ofReal_eq_tsum h1
    have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne'
    have hre : 0 < (riemannZeta σ).re := by rw [← hexp]; exact Real.exp_pos _
    refine ⟨(σ - 1) * (riemannZeta σ).re, mul_pos (by linarith) hre, ?_⟩
    rw [zetaResidueUnit, Function.update_of_ne hne]
    have hz : riemannZeta (σ : ℂ) = ((riemannZeta σ).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    conv_lhs => rw [hz]
    push_cast; ring

/-- `log((σ-1)ζ(σ)/σ) = Σ_n a_n n^{-σ} - log(σ/(σ-1))` for real `σ > 1`. -/
theorem log_zetaResidueUnit_div_ofReal {σ : ℝ} (hσ : 1 < σ) :
    Complex.log (zetaResidueUnit (σ : ℂ) / σ)
      = (((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) - Real.log (σ / (σ - 1)) : ℝ) : ℂ) := by
  obtain ⟨hexp, him⟩ := log_riemannZeta_ofReal_eq_tsum hσ
  have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
  have hz : riemannZeta (σ : ℂ) = ((riemannZeta σ).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hval : zetaResidueUnit (σ : ℂ) / σ
      = (((σ - 1) * Real.exp (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) / σ : ℝ) : ℂ) := by
    rw [zetaResidueUnit, Function.update_of_ne hne, hz, ← hexp]
    push_cast; ring
  have hpos : 0 < (σ - 1) * Real.exp (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) / σ := by
    have := Real.exp_pos (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ))
    apply div_pos (mul_pos (by linarith) this) (by linarith)
  rw [hval, ← Complex.ofReal_log hpos.le]
  congr 1
  rw [Real.log_div (by positivity) (by linarith), Real.log_mul (by linarith) (Real.exp_pos _).ne',
    Real.log_exp, Real.log_div (by linarith) (by linarith)]
  ring

/-! ## The measure -/

/-- The clipped density `K e^{at} + L(t) - Π(e^t) + M`. -/
def piLiDensity (a K M : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (K * Real.exp (a * t) + logIntegralCompare t - primePowerCount (Real.exp t) + M)

theorem measurable_piLiDensity (a K M : ℝ) : Measurable (piLiDensity a K M) := by
  unfold piLiDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add ?_ measurable_const
  refine Measurable.sub ?_ (primePowerCount_mono.measurable.comp Real.measurable_exp)
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).add
    continuous_logIntegralCompare.measurable

/-- `g dt + e^{at} dt` on `(0, ∞)`. -/
def piLiMeasure (a K M : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (piLiDensity a K M u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity a u : ENNReal))

/-- The density is at most `(K + M + 1) e^{t}` for `t > 0`. -/
theorem piLiDensity_le {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) {t : ℝ} (ht : 0 < t) :
    ((piLiDensity a K M t : ℝ)) ≤ (K + M + 1) * Real.exp t := by
  unfold piLiDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp (a * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have h2 := logIntegralCompare_le_exp ht.le
  have h3 := primePowerCount_nonneg (Real.exp t)
  have h4 : 1 ≤ Real.exp t := Real.one_le_exp ht.le
  have hE := Real.exp_pos t
  refine max_le ?_ (by positivity)
  nlinarith

theorem integrableOn_exp_majorant {σ C : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun u : ℝ => C * Real.exp u * Real.exp (-σ * u)) (Ioi 0) := by
  have h := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1)).const_mul C
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [show Real.exp (-(σ - 1) * u) = Real.exp u * Real.exp (-σ * u) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_piLi_density_ne_top {a K M σ : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hσ : 1 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (piLiDensity a K M u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_piLiDensity a K M).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_exp_majorant (C := K + M + 1) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (piLiDensity_le ha hK hM hu) (Real.exp_pos _).le

theorem laplaceMass_piLi_eq (a K M σ : ℝ) :
    laplaceMass (piLiMeasure a K M) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (piLiDensity a K M u : ENNReal))) σ + laplaceMass volume (σ - a) := by
  unfold laplaceMass piLiMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift a σ
  unfold laplaceMass at this
  exact this

/-- The abscissa of `ν` lies in `[a, 2]`. -/
theorem isAbscissa_piLi {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    IsAbscissa (piLiMeasure a K M) (sInf {σ : ℝ | laplaceMass (piLiMeasure a K M) σ ≠ ⊤}) ∧
      a ≤ sInf {σ : ℝ | laplaceMass (piLiMeasure a K M) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (piLiMeasure a K M) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, a < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_piLi_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top (by linarith), add_top]
    · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨a, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2:ℝ) ∈ S := by
    show laplaceMass (piLiMeasure a K M) 2 ≠ ⊤
    rw [laplaceMass_piLi_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_piLi_density_ne_top ha hK hM (by norm_num),
      laplaceMass_volume_ne_top (by linarith)⟩
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)


/-! ## The real transform for `σ > 1` -/

theorem integrableOn_primePowerCount_exp_mul {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => primePowerCount (Real.exp t) * Real.exp (-σ * t)) (Ioi 0) := by
  refine (integrableOn_exp_majorant (C := 1) hσ).mono' ?_ ?_
  · exact ((primePowerCount_mono.measurable.comp Real.measurable_exp).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (primePowerCount_nonneg _)
      (Real.exp_pos _).le), one_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact (primePowerCount_le _).trans (Nat.floor_le (Real.exp_pos t).le)

theorem integrableOn_logIntegralCompare_mul_exp {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => logIntegralCompare t * Real.exp (-σ * t)) (Ioi 0) := by
  refine (integrableOn_exp_majorant (C := 1) hσ).mono' ?_ ?_
  · exact (continuous_logIntegralCompare.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (logIntegralCompare_nonneg (le_of_lt ht))
      (Real.exp_pos _).le), one_mul]
    exact mul_le_mul_of_nonneg_right (logIntegralCompare_le_exp (le_of_lt ht)) (Real.exp_pos _).le

theorem integral_Ioi_exp_neg_mul_eq_one_div {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) = 1 / b := by
  rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
  field_simp

/-- Under the one-sided bound, the real transform of `ν` for `σ > 1`. -/
theorem laplaceReal_piLi_eq {a K M : ℝ} (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → primePowerCount (Real.exp t)
      ≤ K * Real.exp (a * t) + logIntegralCompare t + M) {σ : ℝ} (hσ : 1 < σ) :
    laplaceReal (piLiMeasure a K M) σ = (K + 1) / (σ - a) + M / σ
      - ((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) - Real.log (σ / (σ - 1))) / σ := by
  have hσ0 : 0 < σ := by linarith
  have hσa : 0 < σ - a := by linarith
  have hexpInt : ∀ b : ℝ, 0 < b → IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) :=
    fun b hb => exp_neg_integrableOn_Ioi 0 hb
  have hI1 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (piLiDensity a K M u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_piLiDensity a K M)]
    refine (integrableOn_exp_majorant (C := K + M + 1) hσ).mono' ?_ ?_
    · exact ((measurable_piLiDensity a K M).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (piLiDensity_le ha hK hM hu) (Real.exp_pos _).le
  have hI2 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthShiftDensity a u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_growthShiftDensity a)]
    refine (hexpInt (σ - a) hσa).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [NNReal.smul_def, smul_eq_mul, growthShiftDensity_coe, ← Real.exp_add]
    ring_nf
  unfold laplaceReal piLiMeasure
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
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (piLiDensity a K M u : ENNReal)))
      = K / (σ - a) + Real.log (σ / (σ - 1)) / σ
        - (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) / σ + M / σ := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_piLiDensity a K M)]
    have hpt : ∀ u ∈ Ioi (0:ℝ), piLiDensity a K M u • Real.exp (-σ * u)
        = ((K * Real.exp (-(σ - a) * u) + logIntegralCompare u * Real.exp (-σ * u))
          - primePowerCount (Real.exp u) * Real.exp (-σ * u)) + M * Real.exp (-σ * u) := by
      intro u hu
      rw [NNReal.smul_def, smul_eq_mul]
      unfold piLiDensity
      rw [Real.coe_toNNReal _ (by linarith [hg u hu])]
      rw [show Real.exp (-(σ - a) * u) = Real.exp (a * u) * Real.exp (-σ * u) by
        rw [← Real.exp_add]; ring_nf]
      ring
    have i1 : IntegrableOn (fun u => K * Real.exp (-(σ - a) * u)) (Ioi 0) :=
      (hexpInt _ hσa).const_mul K
    have i2 := integrableOn_logIntegralCompare_mul_exp hσ
    have i3 := integrableOn_primePowerCount_exp_mul hσ
    have i4 : IntegrableOn (fun u => M * Real.exp (-σ * u)) (Ioi 0) := (hexpInt σ hσ0).const_mul M
    have i12 : IntegrableOn (fun u => K * Real.exp (-(σ - a) * u)
        + logIntegralCompare u * Real.exp (-σ * u)) (Ioi 0) := i1.add i2
    have i123 : IntegrableOn (fun u => (K * Real.exp (-(σ - a) * u)
        + logIntegralCompare u * Real.exp (-σ * u))
        - primePowerCount (Real.exp u) * Real.exp (-σ * u)) (Ioi 0) := i12.sub i3
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i123 i4, integral_sub i12 i3,
      integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_Ioi_exp_neg_mul_eq_one_div hσa,
      integral_Ioi_exp_neg_mul_eq_one_div hσ0, integral_logIntegralCompare_mul_exp hσ,
      integral_primePowerCount_exp_mul hσ]
    ring
  rw [hdens, hshift]
  ring

/-! ## The continuation and Landau's theorem -/

/-- `Φ(z) = (K+1)/(z-a) + M/z - log((z-1)ζ(z)/z)/z`. -/
def piLiContinuation (a K M : ℝ) (z : ℂ) : ℂ :=
  (K + 1) / (z - a) + M / z - Complex.log (zetaResidueUnit z / z) / z

theorem analyticAt_piLiContinuation (a K M : ℝ) {z : ℂ} (hza : z ≠ a) (hz0 : z ≠ 0)
    (hslit : zetaResidueUnit z / z ∈ slitPlane) : AnalyticAt ℂ (piLiContinuation a K M) z := by
  unfold piLiContinuation
  refine ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)).add
    (analyticAt_const.div analyticAt_id hz0)).sub ?_
  exact (((analyticAt_zetaResidueUnit z).div analyticAt_id hz0).clog hslit).div analyticAt_id hz0

theorem zetaResidueUnit_div_mem_slitPlane {t : ℝ} (ht : 0 < t) :
    zetaResidueUnit (t : ℂ) / (t : ℂ) ∈ slitPlane := by
  obtain ⟨r, hr, hzr⟩ := exists_zetaResidueUnit_ofReal_eq_pos ht
  rw [hzr, ← Complex.ofReal_div, Complex.ofReal_mem_slitPlane]
  exact div_pos hr ht

theorem piLiContinuation_ofReal {a K M : ℝ} {σ : ℝ} (hσ : 1 < σ) :
    piLiContinuation a K M (σ : ℂ) = (((K + 1) / (σ - a) + M / σ
      - ((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-σ)) - Real.log (σ / (σ - 1))) / σ : ℝ)
        : ℂ) := by
  unfold piLiContinuation
  rw [log_zetaResidueUnit_div_ofReal hσ]
  push_cast
  ring

theorem abscissa_piLi_eq {a K M : ℝ} (ha0 : 0 < a) (ha : a ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → primePowerCount (Real.exp t)
      ≤ K * Real.exp (a * t) + logIntegralCompare t + M) :
    IsAbscissa (piLiMeasure a K M) a := by
  obtain ⟨hc, hac⟩ := isAbscissa_piLi (K := K) (M := M) ha hK hM
  set c : ℝ := sInf {σ : ℝ | laplaceMass (piLiMeasure a K M) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc2 : c ≤ 2 := by
      refine csInf_le ⟨a, fun σ hσ => ?_⟩ ?_
      · by_contra hlt
        apply hσ
        rw [laplaceMass_piLi_eq, laplaceMass_volume_eq_top (by linarith [not_le.mp hlt]), add_top]
      · show laplaceMass (piLiMeasure a K M) 2 ≠ ⊤
        rw [laplaceMass_piLi_eq]
        exact ENNReal.add_ne_top.mpr ⟨laplaceMass_piLi_density_ne_top ha hK hM (by norm_num),
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
    refine false_of_analyticAt_abscissa hc hd (Φ := piLiContinuation a K M) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := hball hz
      exact analyticAt_piLiContinuation a K M h3 h2 h1
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (piLiMeasure a K M)) {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (piLiMeasure a K M) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (piLiMeasure a K M)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => piLiContinuation a K M (t : ℂ)) (Ioi c) := by
        intro t ht
        have hta : a < t := lt_trans hpos ht
        have ht0 : 0 < t := lt_trans ha0 hta
        have h1 : AnalyticAt ℂ (piLiContinuation a K M) (t : ℂ) :=
          analyticAt_piLiContinuation a K M (by exact_mod_cast hta.ne') (by exact_mod_cast ht0.ne')
            (zetaResidueUnit_div_mem_slitPlane ht0)
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (piLiMeasure a K M) (t : ℂ)) =ᶠ[𝓝 (3:ℝ)]
          (fun t : ℝ => piLiContinuation a K M (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3:ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < t := by linarith [ht.1]
        show complexLaplace (piLiMeasure a K M) (t : ℂ) = piLiContinuation a K M (t : ℂ)
        rw [complexLaplace_ofReal, laplaceReal_piLi_eq ha hK hM hg ht1,
          piLiContinuation_ofReal ht1]
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (piLiMeasure a K M) (σ : ℂ) = piLiContinuation a K M (σ : ℂ) :=
        heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **A one-sided bound `Π(e^t) ≤ K e^{at} + L(t) + M` excludes zeros of `ζ` from `Re s > a`.** -/
theorem zetaResidueUnit_ne_zero_of_primePowerCount_le {a K M : ℝ} (ha0 : 0 < a) (ha : a ≤ 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hg : ∀ t, 0 < t → primePowerCount (Real.exp t)
      ≤ K * Real.exp (a * t) + logIntegralCompare t + M) {z : ℂ} (hz : a < z.re) :
    zetaResidueUnit z ≠ 0 := by
  have hc := abscissa_piLi_eq ha0 ha hK hM hg
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hne0 : ∀ w ∈ U, w ≠ 0 := fun w hw h => by
    rw [h] at hw; simp [hU] at hw; linarith
  have hnea : ∀ w ∈ U, w - a ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set B : ℂ → ℂ := fun w => w * ((K + 1) / (w - a) + M / w
    - complexLaplace (piLiMeasure a K M) w) with hB
  have hBd : DifferentiableOn ℂ B U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => ((K : ℂ) + 1) / (w - a)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hnea w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (M : ℂ) / w) w :=
      (differentiableAt_const _).div differentiableAt_id (hne0 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    exact (differentiableAt_id.mul ((h1.add h2).sub h3)).differentiableWithinAt
  have hF : AnalyticOnNhd ℂ (fun w => Complex.exp (B w) * w) U :=
    ((hBd.cexp).mul differentiableOn_id).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ zetaResidueUnit U := fun w _ => analyticAt_zetaResidueUnit w
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; linarith
  have hreal : ∀ t : ℝ, 1 < t → Complex.exp (B t) * t = zetaResidueUnit t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < t).ne'
    have hBt : B t = Complex.log (zetaResidueUnit t / t) := by
      simp only [hB]
      rw [complexLaplace_ofReal, laplaceReal_piLi_eq ha hK hM hg ht,
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


/-! ## From `π ≤ li` to the Riemann hypothesis -/

theorem eulerLogCoeffReal_le_vonMangoldt_div_log_two (n : ℕ) :
    eulerLogCoeffReal n ≤ ArithmeticFunction.vonMangoldt n / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold eulerLogCoeffReal
  rcases le_or_gt n 1 with hn | hn
  · have hlog : Real.log n = 0 := by
      interval_cases n <;> simp
    rw [hlog, div_zero]
    exact div_nonneg hΛ hl2.le
  · refine div_le_div_of_nonneg_left hΛ hl2 (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast hn

/-- `Π(x) ≤ π(x) + (ψ(x) - θ(x))/log 2`. -/
theorem primePowerCount_le_primeCounting_add (x : ℝ) :
    primePowerCount x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)
      + (Chebyshev.psi x - Chebyshev.theta x) / Real.log 2 := by
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
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hrest : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬n.Prime, eulerLogCoeffReal n
      ≤ (Chebyshev.psi x - Chebyshev.theta x) / Real.log 2 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_div, hIcc]
    exact Finset.sum_le_sum fun n _ => eulerLogCoeffReal_le_vonMangoldt_div_log_two n
  rw [hprime]
  linarith

theorem log_le_two_mul_exp_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.exp (1 / 2 * t) := by
  have h1 := Real.log_le_sub_one_of_pos ht
  have h2 := Real.add_one_le_exp (1 / 2 * t)
  linarith

theorem sqrt_exp_eq_exp_half_mul (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (1 / 2 * t) := by
  rw [show Real.exp t = Real.exp (1 / 2 * t) * Real.exp (1 / 2 * t) by
    rw [← Real.exp_add]; ring_nf]
  exact Real.sqrt_mul_self (Real.exp_pos _).le

/-- **Landau's theorem for `π - li`.**  If `π(x) ≤ li(x) + K√x` for all large `x`, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt {K : ℝ}
    (h : ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (∫ t in (2 : ℝ)..x, 1 / Real.log t) + K * Real.sqrt x) :
    RiemannHypothesis := by
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp h
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set x₀ : ℝ := max x₁ 2 with hx₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₁ : ℝ := |K| + |C| / Real.log 2 + 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hM0 : 0 ≤ x₀ + 1 := by rw [hx₀]; linarith [le_max_right x₁ 2]
  have hg : ∀ t, 0 < t → primePowerCount (Real.exp t)
      ≤ K₁ * Real.exp (1 / 2 * t) + logIntegralCompare t + (x₀ + 1) := by
    intro t ht
    have hE := Real.exp_pos (1 / 2 * t)
    have hL := logIntegralCompare_nonneg ht.le
    by_cases hxt : x₀ ≤ Real.exp t
    · have hx2 : 2 ≤ Real.exp t := le_trans (le_max_right _ _) hxt
      have hpi := hx₁ (Real.exp t) (le_trans (le_max_left _ _) hxt)
      have hli := integral_inv_log_le_logIntegralCompare hx2
      rw [Real.log_exp] at hli
      have hpp := primePowerCount_le_primeCounting_add (Real.exp t)
      have hps := hC (Real.exp t)
      rw [sqrt_exp_eq_exp_half_mul] at hpi hps
      have hps' : (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)) / Real.log 2
          ≤ |C| / Real.log 2 * Real.exp (1 / 2 * t) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (hps.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
          hE.le)) hl2.le
      have hKK : K * Real.exp (1 / 2 * t) ≤ |K| * Real.exp (1 / 2 * t) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hE.le
      have hlog := log_le_two_mul_exp_half ht
      have hexp : K₁ * Real.exp (1 / 2 * t) = |K| * Real.exp (1 / 2 * t)
          + |C| / Real.log 2 * Real.exp (1 / 2 * t) + 2 * Real.exp (1 / 2 * t) := by
        rw [hK₁]; ring
      have hx02 : 2 ≤ x₀ := le_max_right _ _
      linarith
    · have h1 := primePowerCount_le (Real.exp t)
      have h2 := Nat.floor_le (Real.exp_pos t).le
      have h3 : 0 ≤ K₁ * Real.exp (1 / 2 * t) := mul_nonneg hK₁0 hE.le
      have hxt' : Real.exp t < x₀ := not_le.mp hxt
      linarith
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs
  exact zetaResidueUnit_ne_zero_of_primePowerCount_le (by norm_num) (by norm_num) hK₁0 hM0 hg hs

end

end RHTower
