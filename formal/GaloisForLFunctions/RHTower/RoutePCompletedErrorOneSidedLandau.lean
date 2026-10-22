import GaloisForLFunctions.RHTower.ChebyshevDeficitPrimitiveOneSidedRH
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCompletedSourceLaplaceWeld
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeCone

/-!
# One-sided critical-mass control in Route P

An eventual linear upper bound on the literal completed Mellin error forces RH.
The positive comparison measure retains both polar endpoints; its transform is
`(B+1)/z+B/z²+epsilon*regularizedCriticalMellinDefect(z-1/2)/z`.
Landau's theorem moves its abscissa to zero because the regularized zeta has no
positive real zero. The resulting defect extension supplies the conclusion.

This proves the one-sided analytic implication needed by the nonlinear Route-P
barrier argument. It does not establish the source bound or the signed history floor.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- Exact unweighted completed-error Laplace transform, including both polar endpoints. -/
theorem routeP_completedError_laplace {z : ℂ} (hz : 1 / 2 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
      (criticalMellinCompletedError t : ℂ)) =
        regularizedCriticalMellinDefect (z - 1 / 2) / z := by
  have hu : 0 < (z - 1 / 2).re := by simp; linarith
  have hpt : ∀ t : ℝ, Complex.exp (-((z - 1 / 2) * (t : ℂ))) *
      (unitRieszCompletedCurrent t : ℂ) =
        Complex.exp (-(z * (t : ℂ))) * (criticalMellinCompletedError t : ℂ) := by
    intro t
    rw [unitRieszCompletedCurrent]
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hL := unitRieszCompletedCurrent_laplace hu
  simp_rw [hpt] at hL
  have hLS := vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv hu
  unfold vonMangoldtPrimeLaplaceChannelComplex at hLS
  rw [show (1 : ℂ) + (z - 1 / 2) = (z - 1 / 2) + 1 by ring, hLS] at hL
  rw [hL, regularizedCriticalMellinDefect_eq_explicit hu]
  have hz0 : z ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hu0 : z - 1 / 2 ≠ 0 := ne_zero_of_re_pos hu
  have hu1 : z - 1 / 2 + 1 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
  have heq : z - 1 / 2 + 1 / 2 = z := by ring
  rw [heq]
  have hm : -1 + z * 2 ≠ 0 := fun h => hu0 (by linear_combination h / 2)
  have hp : 1 + z * 2 ≠ 0 := fun h => hu1 (by linear_combination h / 2)
  field_simp
  ring_nf
  linear_combination 2 * mul_inv_cancel₀ hm - 2 * mul_inv_cancel₀ hp

/-- The initial completed-error transform is absolutely convergent. -/
theorem routeP_integrable_exp_completedError {σ : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun t => Real.exp (-σ * t) * criticalMellinCompletedError t) (Ioi 0) := by
  have hm := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1 / 2)).const_mul 23
  refine hm.mono' ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    measurable_criticalMellinCompletedError).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-σ * t) * |criticalMellinCompletedError t|
      ≤ Real.exp (-σ * t) * (23 * Real.exp (t / 2)) :=
        mul_le_mul_of_nonneg_left (abs_criticalMellinCompletedError_le_sqrt ht.le)
          (Real.exp_pos _).le
    _ = 23 * Real.exp (-(σ - 1 / 2) * t) := by
      rw [show -(σ - 1 / 2) * t = -σ * t + t / 2 by ring, Real.exp_add]; ring

theorem routeP_completedError_real_laplace {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((∫ t in Ioi (0 : ℝ), Real.exp (-σ * t) * criticalMellinCompletedError t : ℝ) : ℂ) =
      regularizedCriticalMellinDefect ((σ : ℂ) - 1 / 2) / σ := by
  rw [← routeP_completedError_laplace (by simpa using hσ)]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  congr 2
  ring

/-- The clipped density `max(B(1+T) + ε E(T), 0)`, `ε = ±1`. -/
def rpCompletedOneSidedDensity (ε B : ℝ) (T : ℝ) : NNReal :=
  Real.toNNReal (B * (1 + T) + ε * (criticalMellinCompletedError T))

theorem measurable_rpCompletedOneSidedDensity (ε B : ℝ) : Measurable (rpCompletedOneSidedDensity ε B) := by
  unfold rpCompletedOneSidedDensity
  exact ((measurable_const.mul (measurable_const.add measurable_id)).add
    (measurable_const.mul measurable_criticalMellinCompletedError)).real_toNNReal

/-- `(B(1+T) + ε E(T)) dT` on `(0,∞)` plus Lebesgue measure. -/
def rpCompletedOneSidedMeasure (ε B : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal)) +
    volume

theorem rpCompletedOneSidedDensity_le {ε B : ℝ} (hε : |ε| ≤ 1) {T : ℝ} (hT : 0 < T) :
    ((rpCompletedOneSidedDensity ε B T : ℝ)) ≤
      (2 * |B| + (23 : ℝ)) * Real.exp (T / 2) := by
  unfold rpCompletedOneSidedDensity
  rw [Real.coe_toNNReal']
  have hprod := abs_criticalMellinCompletedError_le_sqrt hT.le
  have hε' : |ε * (criticalMellinCompletedError T)| ≤
      (23 : ℝ) * Real.exp (T / 2) := by
    rw [abs_mul]
    calc |ε| * |criticalMellinCompletedError T|
        ≤ 1 * ((23 : ℝ) * Real.exp (T / 2)) :=
          mul_le_mul hε hprod (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h1T : 1 + T ≤ 2 * Real.exp (T / 2) := by
    have := Real.add_one_le_exp (T / 2); linarith
  have h1 : B * (1 + T) ≤ 2 * |B| * Real.exp (T / 2) := by
    calc B * (1 + T) ≤ |B| * (1 + T) := mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith)
      _ ≤ |B| * (2 * Real.exp (T / 2)) := mul_le_mul_of_nonneg_left h1T (abs_nonneg B)
      _ = 2 * |B| * Real.exp (T / 2) := by ring
  have h2 := le_abs_self (ε * (criticalMellinCompletedError T))
  have h3 : 0 ≤ (2 * |B| + (23 : ℝ)) * Real.exp (T / 2) := by
    positivity
  rcases le_or_gt (B * (1 + T) + ε * (criticalMellinCompletedError T)) 0
    with h | h
  · rw [max_eq_right h]; exact h3
  · rw [max_eq_left h.le]; nlinarith

theorem integrableOn_rpCompletedMajorant {σ B : ℝ} (hσ : 1 / 2 < σ) :
    IntegrableOn (fun T : ℝ =>
      (2 * |B| + (23 : ℝ)) * Real.exp (T / 2) * Real.exp (-σ * T)) (Ioi 0) := by
  have h2 := (exp_neg_integrableOn_Ioi 0 (by linarith : (0:ℝ) < σ - 1 / 2)).const_mul
    (2 * |B| + (23 : ℝ))
  refine IntegrableOn.congr_fun h2 (fun T _ => ?_) measurableSet_Ioi
  rw [show Real.exp (-(σ - 1 / 2) * T) = Real.exp (T / 2) * Real.exp (-σ * T) by
    rw [← Real.exp_add]; ring_nf]
  ring

theorem laplaceMass_rpCompletedDensity_ne_top {ε B σ : ℝ} (hε : |ε| ≤ 1) (hσ : 1 / 2 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun T : ℝ => ENNReal.ofReal (Real.exp (-σ * T))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_self,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_rpCompletedOneSidedDensity ε B).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top (integrableOn_rpCompletedMajorant (B := B) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (rpCompletedOneSidedDensity_le hε hT) (Real.exp_pos _).le

theorem laplaceMass_rpCompletedOneSided_eq (ε B σ : ℝ) :
    laplaceMass (rpCompletedOneSidedMeasure ε B) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal))) σ + laplaceMass volume σ := by
  unfold laplaceMass rpCompletedOneSidedMeasure
  rw [Measure.restrict_add, lintegral_add_measure]

/-- The convergence set lies in `(0,∞)`, contains `1`, and is an up-set; its infimum is the
abscissa. -/
theorem isAbscissa_rpCompletedOneSided {ε B : ℝ} (hε : |ε| ≤ 1) :
    IsAbscissa (rpCompletedOneSidedMeasure ε B)
        (sInf {σ : ℝ | laplaceMass (rpCompletedOneSidedMeasure ε B) σ ≠ ⊤}) ∧
      0 ≤ sInf {σ : ℝ | laplaceMass (rpCompletedOneSidedMeasure ε B) σ ≠ ⊤} := by
  set S := {σ : ℝ | laplaceMass (rpCompletedOneSidedMeasure ε B) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, 0 < σ := by
    intro σ hσ
    by_contra hle
    apply hσ
    rw [laplaceMass_rpCompletedOneSided_eq]
    rcases lt_or_eq_of_le (not_lt.mp hle) with h | h
    · rw [laplaceMass_volume_eq_top h, add_top]
    · rw [h, laplaceMass_volume_zero_eq_top, add_top]
  have hbdd : BddBelow S := ⟨0, fun σ hσ => (hpos σ hσ).le⟩
  have h1S : (1:ℝ) ∈ S := by
    show laplaceMass (rpCompletedOneSidedMeasure ε B) 1 ≠ ⊤
    rw [laplaceMass_rpCompletedOneSided_eq]
    exact ENNReal.add_ne_top.mpr ⟨laplaceMass_rpCompletedDensity_ne_top hε (by norm_num),
      laplaceMass_volume_ne_top one_pos⟩
  have hne : S.Nonempty := ⟨1, h1S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, Real.sInf_nonneg fun σ hσ => (hpos σ hσ).le⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)


/-- Meromorphic continuation of the positive comparison measure's transform. -/
def rpCompletedOneSidedContinuation (ε B : ℝ) (z : ℂ) : ℂ :=
  (B + 1) / z + B / z ^ 2 + ε *
    ((1 / (z + 1 / 2) + logDeriv zetaResidueUnit (z + 1 / 2)) / z)

theorem analyticAt_rpCompletedOneSidedContinuation (ε B : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z + 1 / 2 ≠ 0) (hζ : zetaResidueUnit (z + 1 / 2) ≠ 0) :
    AnalyticAt ℂ (rpCompletedOneSidedContinuation ε B) z := by
  unfold rpCompletedOneSidedContinuation
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hζan : AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)) hshift
  have hdζ : AnalyticAt ℂ (fun w : ℂ => deriv zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (analyticAt_zetaResidueUnit (z + 1 / 2)).deriv
      hshift
  have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2)) z := by
    simp only [logDeriv_apply]
    exact hdζ.div hζan hζ
  refine ((analyticAt_const.div analyticAt_id hz0).add
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero 2 hz0))).add (analyticAt_const.mul ?_)
  exact ((analyticAt_const.div hshift hz1).add hlog).div analyticAt_id hz0

theorem rpCompletedOneSidedDensity_eq {ε B : ℝ}
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * criticalMellinCompletedError T)
    {T : ℝ} (hT : 0 ≤ T) :
    ((rpCompletedOneSidedDensity ε B T : ℝ)) =
      B * (1 + T) + ε * criticalMellinCompletedError T := by
  unfold rpCompletedOneSidedDensity
  exact Real.coe_toNNReal _ (hB T hT)

/-- Agreement on the real convergence ray uses the literal completed-error transform. -/
theorem laplaceReal_rpCompletedOneSided_eq {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * criticalMellinCompletedError T)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((laplaceReal (rpCompletedOneSidedMeasure ε B) σ : ℝ) : ℂ) =
      rpCompletedOneSidedContinuation ε B (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have hexpInt : IntegrableOn (fun T : ℝ => Real.exp (-σ * T)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hσ0
  have hdensInt : Integrable (fun T : ℝ => Real.exp (-σ * T))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_rpCompletedOneSidedDensity ε B)]
    refine (integrableOn_rpCompletedMajorant (B := B) hσ).mono' ?_ ?_
    · exact ((measurable_rpCompletedOneSidedDensity ε B).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with T hT
      rw [NNReal.smul_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _),
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (rpCompletedOneSidedDensity_le hε hT) (Real.exp_pos _).le
  have hsplit : laplaceReal (rpCompletedOneSidedMeasure ε B) σ =
      (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal)))) + 1 / σ := by
    unfold laplaceReal rpCompletedOneSidedMeasure
    rw [Measure.restrict_add, integral_add_measure hdensInt hexpInt,
      integral_exp_neg_mul_Ioi_real hσ0]
  have hdens : (∫ T in Ioi (0:ℝ), Real.exp (-σ * T) ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun T => (rpCompletedOneSidedDensity ε B T : ENNReal)))) =
      B / σ + B / σ ^ 2 + ε * ∫ T in Ioi (0:ℝ),
        Real.exp (-σ * T) * criticalMellinCompletedError T := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_rpCompletedOneSidedDensity ε B)]
    have hpt : ∀ T ∈ Ioi (0:ℝ), rpCompletedOneSidedDensity ε B T • Real.exp (-σ * T) =
        (B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T))) +
          ε * (Real.exp (-σ * T) * criticalMellinCompletedError T) := by
      intro T hT
      rw [NNReal.smul_def, smul_eq_mul, rpCompletedOneSidedDensity_eq hB (le_of_lt hT)]
      ring
    have hf : Integrable (fun T : ℝ => B * Real.exp (-σ * T) + B * (T * Real.exp (-σ * T)))
        (volume.restrict (Ioi 0)) :=
      (hexpInt.const_mul B).add ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add hf ((routeP_integrable_exp_completedError hσ).const_mul ε),
      integral_add (hexpInt.const_mul B) ((integrableOn_id_mul_real_exp_neg_mul hσ0).const_mul B),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_exp_neg_mul_Ioi_real hσ0,
      integral_id_mul_real_exp_neg_mul hσ0]
    ring
  rw [hsplit, hdens]
  push_cast
  rw [routeP_completedError_real_laplace hσ]
  unfold rpCompletedOneSidedContinuation regularizedCriticalMellinDefect
  rw [show (σ : ℂ) - 1 / 2 + 1 = σ + 1 / 2 by ring]
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hreg]
  ring
/-! ## Landau: the abscissa is zero -/

theorem abscissa_rpCompletedOneSided_eq_zero {ε B : ℝ} (hε : |ε| ≤ 1)
    (hB : ∀ T : ℝ, 0 ≤ T →
      0 ≤ B * (1 + T) + ε * (criticalMellinCompletedError T)) :
    IsAbscissa (rpCompletedOneSidedMeasure ε B) 0 := by
  obtain ⟨hc, hc0⟩ := isAbscissa_rpCompletedOneSided (B := B) hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (rpCompletedOneSidedMeasure ε B) σ ≠ ⊤} with hcdef
  rcases hc0.lt_or_eq with hpos | hzero
  · exfalso
    have hζc : zetaResidueUnit ((c : ℂ) + 1 / 2) ≠ 0 := by
      have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := c + 1 / 2) (by linarith)
      simpa using h
    have hopen : IsOpen {z : ℂ | zetaResidueUnit (z + 1 / 2) ≠ 0} :=
      isOpen_ne_fun ((analyticOnNhd_univ_iff_differentiable.mp
        (fun z _ => analyticAt_zetaResidueUnit z)).continuous.comp
          (continuous_id.add continuous_const)) continuous_const
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hopen _ hζc
    set δ : ℝ := min c d / 2 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; exact half_pos (lt_min hpos hd)
    have hδc : δ ≤ c / 2 := by rw [hδdef]; linarith [min_le_left c d]
    have hδd : δ ≤ d / 2 := by rw [hδdef]; linarith [min_le_right c d]
    refine false_of_analyticAt_abscissa hc hδ (Φ := rpCompletedOneSidedContinuation ε B) ?_ ?_
    · intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hzre : c / 2 < z.re := by
        have := Complex.abs_re_le_norm (z - c)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        have := abs_le.mp this
        linarith
      have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
      have hz1 : z + 1 / 2 ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      have hzζ : zetaResidueUnit (z + 1 / 2) ≠ 0 := by
        have hmem := hball (show z ∈ Metric.ball (c : ℂ) d from by
          rw [Metric.mem_ball, Complex.dist_eq]; linarith)
        exact hmem
      exact analyticAt_rpCompletedOneSidedContinuation ε B hz0 hz1 hzζ
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (rpCompletedOneSidedMeasure ε B))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace (rpCompletedOneSidedMeasure ε B) (t : ℂ))
          (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (rpCompletedOneSidedMeasure ε B)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => rpCompletedOneSidedContinuation ε B (t : ℂ)) (Ioi c) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hpos ht
        have h1 : AnalyticAt ℂ (rpCompletedOneSidedContinuation ε B) (t : ℂ) := by
          refine analyticAt_rpCompletedOneSidedContinuation ε B (by exact_mod_cast ht0.ne') ?_ ?_
          · intro h; have hre := congrArg Complex.re h; simp at hre; linarith
          · have h := zetaResidueUnit_ne_zero_of_ofReal_pos (u := t + 1 / 2) (by linarith)
            simpa using h
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h1mem : (1 : ℝ) ∈ Ioi c := by
        show c < 1
        have hc34 : c ≤ 3 / 4 := by
          refine csInf_le ⟨0, fun σ' hσ' => ?_⟩ ?_
          · by_contra hlt
            apply hσ'
            rw [laplaceMass_rpCompletedOneSided_eq, laplaceMass_volume_eq_top (not_le.mp hlt), add_top]
          · show laplaceMass (rpCompletedOneSidedMeasure ε B) (3 / 4) ≠ ⊤
            rw [laplaceMass_rpCompletedOneSided_eq]
            exact ENNReal.add_ne_top.mpr ⟨laplaceMass_rpCompletedDensity_ne_top hε (by norm_num),
              laplaceMass_volume_ne_top (by norm_num)⟩
        linarith
      have hfg : (fun t : ℝ => complexLaplace (rpCompletedOneSidedMeasure ε B) (t : ℂ)) =ᶠ[𝓝 (1:ℝ)]
          (fun t : ℝ => rpCompletedOneSidedContinuation ε B (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1:ℝ) < 3/2)) fun t ht => ?_
        rw [complexLaplace_ofReal]
        exact laplaceReal_rpCompletedOneSided_eq hε hB ht.1
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h1mem hfg
      have hσ' : complexLaplace (rpCompletedOneSidedMeasure ε B) (σ : ℂ) =
          rpCompletedOneSidedContinuation ε B (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ', complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- The regularized defect recovered from the positive comparison measure. -/
def rpCompletedOneSidedDefectExtension (ε B : ℝ) (u : ℂ) : ℂ :=
  ε * ((u + 1 / 2) *
    (complexLaplace (rpCompletedOneSidedMeasure ε B) (u + 1 / 2) - (B + 1) / (u + 1 / 2) -
      B / (u + 1 / 2) ^ 2))

theorem rpCompletedOneSidedDefectExtension_eq_regularized {ε B : ℝ}
    (hεsq : (ε : ℂ) * ε = 1) {u : ℂ}
    (hu : complexLaplace (rpCompletedOneSidedMeasure ε B) (u + 1 / 2) =
      rpCompletedOneSidedContinuation ε B (u + 1 / 2))
    (hu12 : u + 1 / 2 ≠ 0) :
    rpCompletedOneSidedDefectExtension ε B u = regularizedCriticalMellinDefect u := by
  unfold rpCompletedOneSidedDefectExtension regularizedCriticalMellinDefect
  rw [hu]
  unfold rpCompletedOneSidedContinuation
  rw [show u + 1 / 2 + 1 / 2 = u + 1 by ring]
  have hreg : regularizedRiemannZeta = zetaResidueUnit := rfl
  rw [hreg]
  calc
    (ε : ℂ) * ((u + 1 / 2) *
        (((B:ℂ) + 1) / (u + 1 / 2) + (B:ℂ) / (u + 1 / 2) ^ 2 +
        (ε : ℂ) * ((1 / (u + 1) + logDeriv zetaResidueUnit (u + 1)) / (u + 1 / 2)) -
        ((B:ℂ) + 1) / (u + 1 / 2) - (B:ℂ) / (u + 1 / 2) ^ 2)) =
      ((ε : ℂ) * ε) * ((u + 1 / 2) *
        ((1 / (u + 1) + logDeriv zetaResidueUnit (u + 1)) / (u + 1 / 2))) := by ring
    _ = _ := by rw [hεsq, one_mul, mul_div_cancel₀ _ hu12]

/-- Either one-sided linear bound on the actual completed Mellin error forces RH. -/
theorem riemannHypothesis_of_completedError_oneSided_linear {ε B : ℝ}
    (hε : ε = 1 ∨ ε = -1)
    (hB : ∀ T : ℝ, 0 ≤ T → 0 ≤ B * (1 + T) + ε * criticalMellinCompletedError T) :
    RiemannHypothesis := by
  have hε1 : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hc := abscissa_rpCompletedOneSided_eq_zero hε1 hB
  have hA : AnalyticOnNhd ℂ (rpCompletedOneSidedDefectExtension ε B)
      ccmGuinandWeilCriticalMellinContinuationHalfPlane := by
    intro u hu
    change -1 / 2 < u.re at hu
    have hz : 0 < (u + 1 / 2).re := by simp; linarith
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) u := by fun_prop
    have hL : AnalyticAt ℂ (fun w : ℂ => complexLaplace (rpCompletedOneSidedMeasure ε B) (w + 1 / 2)) u := by
      have hdiff : DifferentiableOn ℂ (complexLaplace (rpCompletedOneSidedMeasure ε B)) {z : ℂ | 0 < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      exact AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2) (hdiff.analyticAt (hopen.mem_nhds hz))
        hshift
    have hu12 : u + 1 / 2 ≠ 0 := ne_zero_of_re_pos hz
    unfold rpCompletedOneSidedDefectExtension
    exact analyticAt_const.mul (hshift.mul
      ((hL.sub (analyticAt_const.div hshift hu12)).sub
        (analyticAt_const.div (hshift.pow 2) (pow_ne_zero 2 hu12))))
  refine riemannHypothesis_of_regularizedCriticalMellinDefect_extension _ hA ?_
  let U : Set ℂ := {u : ℂ | 0 < u.re}
  have hAU : AnalyticOnNhd ℂ (rpCompletedOneSidedDefectExtension ε B) U :=
    hA.mono (fun u hu => by change 0 < u.re at hu; change -1 / 2 < u.re; linarith)
  have hR : AnalyticOnNhd ℂ regularizedCriticalMellinDefect U := by
    simpa only [U] using analyticOnNhd_regularizedCriticalMellinDefect_rightHalfPlane
  have hreal : ∀ r : ℝ, 0 < r →
      rpCompletedOneSidedDefectExtension ε B (r : ℂ) = regularizedCriticalMellinDefect (r : ℂ) := by
    intro r hr
    have hlap := laplaceReal_rpCompletedOneSided_eq hε1 hB (σ := r + 1 / 2) (by linarith)
    rw [← complexLaplace_ofReal] at hlap
    have hcast : (((r + 1 / 2 : ℝ)) : ℂ) = (r : ℂ) + 1 / 2 := by push_cast; ring
    rw [hcast] at hlap
    have hr12 : (r : ℂ) + 1 / 2 ≠ 0 := ne_zero_of_re_pos (by simp; linarith)
    exact rpCompletedOneSidedDefectExtension_eq_regularized hεsq hlap hr12
  have htwo : (2 : ℂ) ∈ U := by change 0 < (2 : ℂ).re; norm_num
  have htend : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 (2 : ℝ)) (𝓝 (2 : ℂ)) := by
        simpa using Complex.continuous_ofReal.tendsto (2 : ℝ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_compl_iff, mem_singleton_iff]
      intro hcon
      have : r = 2 := by exact_mod_cast hcon
      exact absurd this (ne_of_gt hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      rpCompletedOneSidedDefectExtension ε B z = regularizedCriticalMellinDefect z := by
    refine htend.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r (lt_trans (by norm_num) hr)
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have heq := hAU.eqOn_of_preconnected_of_frequently_eq hR hUpre htwo hfreq
  intro s hs
  exact heq (show s ∈ U from hs)

/-- A late one-sided upper bound suffices; no absolute-value bound is assumed. -/
theorem riemannHypothesis_of_completedError_eventually_linear_upper {C L : ℝ}
    (hC : ∀ t : ℝ, L ≤ t → criticalMellinCompletedError t ≤ C * (1 + t)) :
    RiemannHypothesis := by
  let B : ℝ := |C| + 23 * Real.exp (L / 2)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  refine riemannHypothesis_of_completedError_oneSided_linear (ε := -1) (B := B) (Or.inr rfl) ?_
  intro t ht
  have hCt : criticalMellinCompletedError t ≤ B * (1 + t) := by
    by_cases hLt : L ≤ t
    · exact (hC t hLt).trans (mul_le_mul_of_nonneg_right
        (by dsimp [B]; have := le_abs_self C; have := Real.exp_pos (L / 2); linarith)
        (by linarith))
    · have hEt := (le_abs_self (criticalMellinCompletedError t)).trans
        (abs_criticalMellinCompletedError_le_sqrt ht)
      have he := Real.exp_le_exp.mpr (show t / 2 ≤ L / 2 by linarith)
      have hB : 23 * Real.exp (t / 2) ≤ B := by
        dsimp [B]; nlinarith [abs_nonneg C]
      exact (hEt.trans hB).trans (by nlinarith)
  nlinarith

end
end RHTower
