import GaloisForLFunctions.HTGeometry.AnalyticNullPreimage
import GaloisForLFunctions.HTGeometry.AnnealedSpectralDephasing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Dephasing of the two compact-core Hecke sources

The relative phase is analytic and nonconstant along every positive horizontal
slice. Its pushforward on the core rectangle is absolutely continuous, including
across the stationary line. Thus every continuous test removes its interference
at large frequency.
-/

open Set MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- Real coordinates of the single-return core rectangle. -/
def coreSourceRect : Set (ℝ × ℝ) :=
  Icc (-(1 / 4)) (1 / 4) ×ˢ Icc (7 / 4) (15 / 8)

theorem coreSourceRect_measurable : MeasurableSet coreSourceRect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem coreSourceRect_compact : IsCompact coreSourceRect :=
  isCompact_Icc.prod isCompact_Icc

/-- Relative logarithmic height of the direct and returning Weyl terms. -/
def coreSourcePhase (p : ℝ × ℝ) : ℝ := Real.log (4 / (p.1 ^ 2 + p.2 ^ 2))

theorem coreSourcePhase_measurable : Measurable coreSourcePhase := by
  unfold coreSourcePhase
  fun_prop

private theorem phase_slice_analytic {y : ℝ} (hy : 0 < y) :
    AnalyticOnNhd ℝ (fun x => coreSourcePhase (x, y)) univ := by
  intro x _
  have hd : 0 < x ^ 2 + y ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)
  exact (analyticAt_const.div ((analyticAt_id.pow 2).add analyticAt_const)
    hd.ne').log (div_pos (by norm_num) hd)

private theorem phase_slice_nonconstant {y : ℝ} (hy : 0 < y) :
    ∃ x x', coreSourcePhase (x, y) ≠ coreSourcePhase (x', y) := by
  refine ⟨0, 1, ?_⟩
  intro he
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hd : 0 < 1 + y ^ 2 := by positivity
  simp only [coreSourcePhase, zero_pow (by norm_num : 2 ≠ 0), zero_add, one_pow] at he
  have hq := Real.log_injOn_pos (div_pos (by norm_num) hy2)
    (div_pos (by norm_num) hd) he
  have hc := (div_eq_div_iff hy2.ne' hd.ne').mp hq
  linarith

/-- The relative phase has no singular pushforward mass on the core rectangle. -/
theorem coreSourcePhase_absolutelyContinuous :
    Measure.map coreSourcePhase (volume.restrict coreSourceRect) ≪ volume := by
  intro E hE
  obtain ⟨E', hEE', hEm, hEn⟩ := exists_measurable_superset_of_null hE
  refine measure_mono_null hEE' ?_
  rw [Measure.map_apply coreSourcePhase_measurable hEm,
    Measure.restrict_apply (hEm.preimage coreSourcePhase_measurable)]
  let S := coreSourcePhase ⁻¹' E' ∩ coreSourceRect
  have hS : MeasurableSet S :=
    (hEm.preimage coreSourcePhase_measurable).inter coreSourceRect_measurable
  have hT : MeasurableSet (Prod.swap ⁻¹' S) := hS.preimage measurable_swap
  have hnull : (volume.prod volume) (Prod.swap ⁻¹' S) = 0 := by
    refine Measure.measure_prod_null_of_ae_null hT (Eventually.of_forall fun y => ?_)
    change volume (Prod.mk y ⁻¹' (Prod.swap ⁻¹' S)) = 0
    by_cases hy : y ∈ Icc (7 / 4 : ℝ) (15 / 8)
    · have hy0 : 0 < y := by linarith [hy.1]
      have hn := analytic_preimage_volume_eq_zero (phase_slice_analytic hy0)
        (phase_slice_nonconstant hy0) hEn
      exact measure_mono_null (fun x hx => hx.1) hn
    · have he : Prod.mk y ⁻¹' (Prod.swap ⁻¹' S) = ∅ := by
        ext x
        simp only [mem_preimage, Prod.swap_prod_mk, S, mem_inter_iff, coreSourceRect,
          mem_prod, mem_empty_iff_false, iff_false]
        exact fun hx => hy hx.2.2
      rw [he, measure_empty]
  rw [(Measure.measurePreserving_swap).measure_preimage hS.nullMeasurableSet] at hnull
  simpa only [Measure.volume_eq_prod] using hnull

instance coreSourceRect_finite : IsFiniteMeasure (volume.restrict coreSourceRect) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using coreSourceRect_compact.measure_lt_top⟩

theorem coreSourceRect_height_pos {p : ℝ × ℝ} (hp : p ∈ coreSourceRect) : 0 < p.2 := by
  have := hp.2.1
  linarith

theorem coreSourcePhase_continuousOn : ContinuousOn coreSourcePhase coreSourceRect := by
  have hd (p : ℝ × ℝ) (hp : p ∈ coreSourceRect) : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (coreSourceRect_height_pos hp))
  exact (continuousOn_const.div
    ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn
    (fun p hp => (hd p hp).ne')).log (fun p hp => (div_pos (by norm_num) (hd p hp)).ne')

/-- The compact-core relative phase dephases every continuous complex test. -/
theorem coreSourcePhase_dephases (g : ℝ × ℝ → ℂ) (hg : Continuous g) :
    Tendsto (fun t : ℝ => ∫ p in coreSourceRect,
      g p * Complex.exp (-((t * coreSourcePhase p : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := coreSourceRect_compact.exists_bound_of_continuousOn hg.continuousOn
  have hb : ∀ p, ‖coreSourceRect.indicator g p‖ ≤ max C 0 := by
    intro p
    by_cases hp : p ∈ coreSourceRect
    · rw [indicator_of_mem hp]
      exact (hC p hp).trans (le_max_left _ _)
    · rw [indicator_of_notMem hp, norm_zero]
      exact le_max_right _ _
  have ht := (tendsto_integral_exp_phase_weight (volume.restrict coreSourceRect)
    coreSourcePhase_measurable coreSourcePhase_absolutelyContinuous
    (coreSourceRect.indicator g) (hg.measurable.indicator coreSourceRect_measurable)
    (le_max_right C 0) hb).mono_left atTop_le_cocompact
  refine ht.congr fun t => ?_
  exact setIntegral_congr_fun coreSourceRect_measurable
    (fun p hp => by rw [indicator_of_mem hp])

/-- The real interference term vanishes against every continuous test. -/
theorem coreSourcePhase_cos_dephases (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun t : ℝ => ∫ p in coreSourceRect,
      g p * Real.cos (t * coreSourcePhase p)) atTop (𝓝 0) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (coreSourcePhase_dephases (fun p => (g p : ℂ)) (Complex.continuous_ofReal.comp hg))
  have he (t : ℝ) :
      (∫ p in coreSourceRect, (g p : ℂ) *
        Complex.exp (-((t * coreSourcePhase p : ℝ) : ℂ) * Complex.I)).re =
      ∫ p in coreSourceRect, g p * Real.cos (t * coreSourcePhase p) := by
    have hc : ContinuousOn (fun p => (g p : ℂ) *
        Complex.exp (-((t * coreSourcePhase p : ℝ) : ℂ) * Complex.I)) coreSourceRect :=
      (Complex.continuous_ofReal.comp hg).continuousOn.mul
        (Complex.continuous_exp.comp_continuousOn
          (((Complex.continuous_ofReal.comp_continuousOn
            (continuousOn_const.mul coreSourcePhase_continuousOn)).neg).mul continuousOn_const))
    have hi := integral_re (μ := volume.restrict coreSourceRect)
      (ContinuousOn.integrableOn_compact (μ := volume) coreSourceRect_compact hc)
    change (∫ p in coreSourceRect, ((g p : ℂ) *
      Complex.exp (-((t * coreSourcePhase p : ℝ) : ℂ) * Complex.I)).re) = _ at hi
    rw [← hi]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, Real.exp_zero,
      one_mul, Real.cos_neg]
  simpa only [Function.comp_apply, Complex.zero_re, he] using ht

/-- Dephasing survives a convergent real parameter in a continuous amplitude. -/
theorem coreSourcePhase_varying_cos_dephases
    (g : ℝ → ℝ × ℝ → ℝ) (hg : Continuous (Function.uncurry g))
    {a t : ℕ → ℝ} {b : ℝ} (ha : Tendsto a atTop (𝓝 b))
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun n => ∫ p in coreSourceRect,
      g (a n) p * Real.cos (t n * coreSourcePhase p)) atTop (𝓝 0) := by
  have hc (v : ℝ) : Continuous (g v) := hg.comp (by fun_prop)
  have hcos (v : ℝ) : ContinuousOn (fun p => Real.cos (v * coreSourcePhase p))
      coreSourceRect := Real.continuous_cos.comp_continuousOn
    (continuousOn_const.mul coreSourcePhase_continuousOn)
  have hi (v w : ℝ) : IntegrableOn
      (fun p => g v p * Real.cos (w * coreSourcePhase p)) coreSourceRect :=
    ContinuousOn.integrableOn_compact coreSourceRect_compact ((hc v).continuousOn.mul (hcos w))
  have hdiff : Continuous (fun v => ∫ p in coreSourceRect, ‖g v p - g b p‖) :=
    continuous_parametric_integral_of_continuous
      ((hg.sub ((hc b).comp continuous_snd)).norm) coreSourceRect_compact
  have hsmall : Tendsto (fun n => ∫ p in coreSourceRect, ‖g (a n) p - g b p‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, integral_zero] using hdiff.continuousAt.tendsto.comp ha
  have herr : Tendsto (fun n => ∫ p in coreSourceRect,
      (g (a n) p - g b p) * Real.cos (t n * coreSourcePhase p)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hsmall
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on
      (ContinuousOn.integrableOn_compact coreSourceRect_compact
        ((((hc (a n)).sub (hc b)).continuousOn.mul (hcos (t n))).norm))
      (ContinuousOn.integrableOn_compact coreSourceRect_compact
        (((hc (a n)).sub (hc b)).norm.continuousOn)) coreSourceRect_measurable ?_
    intro p _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t n * coreSourcePhase p))
  have hfixed := (coreSourcePhase_cos_dephases (g b) (hc b)).comp ht
  have hsum := herr.add hfixed
  simp only [zero_add] at hsum
  refine hsum.congr fun n => ?_
  rw [← integral_add ((hi (a n) (t n)).sub (hi b (t n))) (hi b (t n))]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
