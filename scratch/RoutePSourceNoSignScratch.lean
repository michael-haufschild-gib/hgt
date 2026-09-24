import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceLandauCarrier
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowContinuation

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

private theorem routePSourceLandauMeasure_moments_below_nine_eighth
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) :
    Iio (9 / 8 : ℝ) ⊆
      interior (integrableExpSet id (routePSourceLandauMeasure epsilon 1 T)) := by
  apply interior_maximal ?_ isOpen_Iio
  intro rho hrho
  have hbig := integrable_exp_nine_eighth_routePSourceLandauMeasure hT hpos
  refine Integrable.mono' hbig ?_ ?_
  · exact (Real.measurable_exp.comp (measurable_const.mul measurable_id))
      |>.aestronglyMeasurable
  · filter_upwards [id_nonneg_ae_routePSourceLandauMeasure hT] with t ht
    simp only [id_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hrho.le ht)

private theorem analyticOnNhd_routePSourceLandauMGF
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t) :
    AnalyticOnNhd ℂ (complexMGF id (routePSourceLandauMeasure epsilon 1 T))
      {w : ℂ | w.re < 9 / 8} := by
  intro w hw
  exact analyticAt_complexMGF
    (routePSourceLandauMeasure_moments_below_nine_eighth hT hpos hw)

private def routePSourceLaplaceUnderSign (epsilon T : ℝ) (z : ℂ) : ℂ :=
  (complexMGF id (routePSourceLandauMeasure epsilon 1 T) ((1 : ℂ) - z) +
    routePSourceSignedHeadLaplace epsilon T z) / (epsilon : ℂ)

private theorem analyticOnNhd_routePSourceLaplaceUnderSign
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hepsilon : epsilon ≠ 0) :
    AnalyticOnNhd ℂ (routePSourceLaplaceUnderSign epsilon T)
      {z : ℂ | -(1 / 8 : ℝ) < z.re} := by
  intro z hz
  change -(1 / 8 : ℝ) < z.re at hz
  have hshift : ((1 : ℂ) - z).re < 9 / 8 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hMGF : AnalyticAt ℂ
      (complexMGF id (routePSourceLandauMeasure epsilon 1 T)) ((1 : ℂ) - z) :=
    analyticOnNhd_routePSourceLandauMGF hT hpos _ hshift
  have haffine : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun w : ℂ =>
      complexMGF id (routePSourceLandauMeasure epsilon 1 T) ((1 : ℂ) - w)) z :=
    hMGF.comp haffine
  have hhead : AnalyticAt ℂ (routePSourceSignedHeadLaplace epsilon T) z :=
    (differentiable_routePSourceSignedHeadLaplace epsilon T).analyticAt z
  have hene : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  exact (hcomp.add hhead).div analyticAt_const hene

private theorem routePSourceLaplaceUnderSign_eq_continuation
    {epsilon T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t →
      0 ≤ epsilon *
        GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventRayRepresentative t)
    (hepsilon : epsilon ≠ 0)
    {z : ℂ} (hz : 1 / 2 < z.re) :
    routePSourceLaplaceUnderSign epsilon T z = routePSourceLaplaceContinuation z := by
  have hene : (epsilon : ℂ) ≠ 0 := by exact_mod_cast hepsilon
  have hmgf := complexMGF_id_routePSourceLandauMeasure_eq_tailLaplace
    (r := 1) hpos ((1 : ℂ) - z)
  have hmgf' : complexMGF id (routePSourceLandauMeasure epsilon 1 T)
      ((1 : ℂ) - z) = routePSourceSignedTailLaplace epsilon T z := by
    have hcoord : ((1 : ℝ) : ℂ) - ((1 : ℂ) - z) = z := by
      push_cast
      ring
    simpa only [hcoord] using hmgf
  have htail := routePSourceSignedTailLaplace_eq_continuation_sub_head
    (epsilon := epsilon) (T := T) hT hz
  unfold routePSourceLaplaceUnderSign
  rw [hmgf', htail]
  field_simp [hene]
  ring

end
end RHTower
