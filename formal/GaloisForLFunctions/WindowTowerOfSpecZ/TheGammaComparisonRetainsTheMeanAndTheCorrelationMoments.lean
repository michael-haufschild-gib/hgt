import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderHasAnExactEnergyIdentity
import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalFinitePartAndBroadClassification

/-!
# The mean charge in the Gamma lag comparison

The total correlation mass is the square of the source mean. Retaining it
extends the logarithmic Gamma comparison to both parities, with the exact
negative mean charge and both polynomial lag moments.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilMarkovPole _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity ArithmeticCriticalityTheory
open BiScaleUncertainty SpacingScaleHarmonicAnalysis

private theorem window_autocorr_integral_eq_half_mean_sq {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hs : tsupport F ⊆ Icc (-(r / 2)) (r / 2)) :
    (∫ t in Ioc (0 : ℝ) r, autocorr F t) = (∫ x, F x) ^ 2 / 2 := by
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hcut : (∫ t in Icc (-r) r, autocorr F t) = ∫ t, autocorr F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    by_cases hp : r < t
    · exact autocorr_eq_zero_of_support hs (by linarith only [hp])
    · have hn : r < -t := by
        by_contra h
        exact ht ⟨by linarith, le_of_not_gt hp⟩
      rw [← _root_.RHTower.ArchimedeanExactForm.autocorr_neg F t]
      exact autocorr_eq_zero_of_support hs (by linarith only [hn])
  have hneg := intervalIntegral.integral_comp_neg
    (f := autocorr F) (a := (0 : ℝ)) (b := r)
  simp only [_root_.RHTower.ArchimedeanExactForm.autocorr_neg, neg_zero] at hneg
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-r) 0) (hc.intervalIntegrable 0 r)
  rw [← hneg, intervalIntegral.integral_of_le (by linarith only [hr] : -r ≤ r),
    ← integral_Icc_eq_integral_Ioc, hcut] at hadd
  let f : CompactlySupportedContinuousMap ℝ ℝ := ⟨⟨F, hF.continuous⟩, hcs⟩
  have hm := integral_autocorr_eq_sq_integral f
  change (∫ t, autocorr F t) = (∫ x, F x) ^ 2 at hm
  rw [intervalIntegral.integral_of_le hr.le, hm] at hadd
  linarith only [hadd]

private theorem retained_gamma_weight_lower {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 ≤ archLevySinhWeight t := by
  refine le_of_mul_le_mul_left (a := t) ?_ ht
  have h := mul_archLevyDensity_ge_sharp ht ht1
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht]
  have he : t * (1 / t + 1 / 2 - t / 24 - t ^ 2 / 16) =
      2 * (1 / 2 + t / 4 - t ^ 2 / 48 - t ^ 3 / 32) := by
    field_simp [ht.ne']
    ring
  rw [he]
  linarith only [h]

/-- The exact Gamma decomposition retains the mean, two correlation moments, and local remainder. -/
theorem gamma_eq_logarithmic_lag_correlation_moments_and_remainder {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hs : tsupport F ⊆ Icc (-(r / 2)) (r / 2)) :
    (∫ t in Ioc (0 : ℝ) r, (autocorr F 0 - autocorr F t) / t) +
      (EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r) *
        (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
      (∫ t in Ioc (0 : ℝ) r, t * autocorr F t) / 24 +
      (∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t) / 16 +
      (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) =
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  set M := autocorr F 0
  set D := fun t => M - autocorr F t
  set W := fun t => D t * archLevySinhWeight t
  have hc : Continuous (autocorr F) :=
    _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hdc : Continuous D := continuous_const.sub hc
  have hd : ∀ t, 0 ≤ D t := fun t => sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi : IntegrableOn W (Ioi (0 : ℝ)) := integrableOn_biScaleLevyIntegrand hF hcs
  have hsub : Ioc (0 : ℝ) r ⊆ Ioi 0 := fun _ ht => ht.1
  have hsubtail : Ioi r ⊆ Ioi 0 := fun t ht =>
    show (0 : ℝ) < t from lt_trans hr ht
  have hilog : IntegrableOn (fun t => D t / t) (Ioc (0 : ℝ) r) := by
    apply (hi.mono_set hsub).mono'
      ((hdc.measurable.div measurable_id).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖D t / t‖ ≤ W t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hd t) ht.1.le)]
    have hw := retained_gamma_weight_lower ht.1 (ht.2.trans hr1)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2, hr1]
    have hwinv : 1 / t ≤ archLevySinhWeight t := by linarith only [hw, ht.2, ht2, hr1]
    simpa only [W, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hwinv (hd t)
  have hiD : IntegrableOn D (Ioc (0 : ℝ) r) :=
    hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hitD : IntegrableOn (fun t => t * D t) (Ioc (0 : ℝ) r) :=
    (continuous_id.mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hit2D : IntegrableOn (fun t => t ^ 2 * D t) (Ioc (0 : ℝ) r) :=
    ((continuous_pow 2).mul hdc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiSum : IntegrableOn (fun t => D t / t + D t / 2) (Ioc (0 : ℝ) r) :=
    hilog.add (hiD.div_const 2)
  have hiSub : IntegrableOn (fun t => D t / t + D t / 2 - t * D t / 24)
      (Ioc (0 : ℝ) r) := hiSum.sub (hitD.div_const 24)
  have hiR : IntegrableOn (fun t => retainedGammaRemainderWeight t * D t)
      (Ioc (0 : ℝ) r) :=
    (retainedGammaRemainder_integrable_nonneg hF hcs).1.mono_set
      (fun _ ht => ⟨ht.1, ht.2.trans hr1⟩)
  have hiP : IntegrableOn
      (fun t => D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16)
      (Ioc (0 : ℝ) r) := by
    exact Integrable.sub
      (f := fun t => D t / t + D t / 2 - t * D t / 24)
      (g := fun t => t ^ 2 * D t / 16) hiSub (hit2D.div_const 16)
  have hcomp : (∫ t in Ioc (0 : ℝ) r,
      D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16) +
      (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t * D t) =
      ∫ t in Ioc (0 : ℝ) r, W t := by
    rw [← integral_add (μ := volume.restrict (Ioc (0 : ℝ) r))
      (f := fun t => D t / t + D t / 2 - t * D t / 24 - t ^ 2 * D t / 16)
      (g := fun t => retainedGammaRemainderWeight t * D t)
      hiP hiR]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp [retainedGammaRemainderWeight, W]
    ring
  have hmean := window_autocorr_integral_eq_half_mean_sq hF hcs hr hs
  have hD : (∫ t in Ioc (0 : ℝ) r, D t) = r * M - (∫ x, F x) ^ 2 / 2 := by
    change (∫ t in Ioc (0 : ℝ) r, M - autocorr F t) = r * M - (∫ x, F x) ^ 2 / 2
    rw [integral_sub (f := fun _ : ℝ => M) (g := autocorr F)
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self), hmean, setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, hr.le]
  rw [integral_sub hiSub (hit2D.div_const 16), integral_sub hiSum (hitD.div_const 24),
    integral_add hilog (hiD.div_const 2), integral_div, integral_div, integral_div, hD] at hcomp
  have htail : (∫ t in Ioi r, W t) = 2 * archLevyAntideriv r * M := by
    have he : ∀ t ∈ Ioi r, W t = 2 * archLevyDensity t * M := by
      intro t ht
      dsimp [W, D, M]
      rw [autocorr_eq_zero_of_support (x := t) hs (by
        have ht' : r < t := ht
        linarith only [ht']), sub_zero,
        archLevySinhWeight, exp_half_div_sinh_eq (lt_trans hr ht)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_mul_const, integral_const_mul,
      WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hr]
  have hsplit : (∫ t in Ioc (0 : ℝ) r, W t) +
      (∫ t in Ioi r, W t) = biScaleLevyEnergy F := by
    rw [← setIntegral_union (s := Ioc (0 : ℝ) r) (t := Ioi r)
      (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'))
      measurableSet_Ioi (hi.mono_set hsub) (hi.mono_set hsubtail),
      Ioc_union_Ioi_eq_Ioi hr.le]
    rfl
  rw [htail] at hsplit
  have hJ1 : (∫ t in Ioc (0 : ℝ) r, t * D t) =
      r ^ 2 * M / 2 - ∫ t in Ioc (0 : ℝ) r, t * autocorr F t := by
    have he : (fun t => t * D t) = fun t => M * t - t * autocorr F t := by
      funext t
      dsimp [D]
      ring
    rw [he, integral_sub (f := fun t => M * t) (g := fun t => t * autocorr F t)
      ((continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((continuous_id.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      integral_const_mul, ← intervalIntegral.integral_of_le hr.le, integral_id]
    ring
  have hJ2 : (∫ t in Ioc (0 : ℝ) r, t ^ 2 * D t) =
      r ^ 3 * M / 3 - ∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t := by
    have hiM2 : IntegrableOn (fun t : ℝ => M * t ^ 2) (Ioc (0 : ℝ) r) :=
      (continuous_const.mul (continuous_pow 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hiA2 : IntegrableOn (fun t : ℝ => t ^ 2 * autocorr F t) (Ioc (0 : ℝ) r) :=
      ((continuous_pow 2).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have he : (fun t => t ^ 2 * D t) = fun t => M * t ^ 2 - t ^ 2 * autocorr F t := by
      funext t
      dsimp [D]
      ring
    rw [he, integral_sub hiM2 hiA2,
      integral_const_mul, ← intervalIntegral.integral_of_le hr.le, integral_pow]
    norm_num
    ring
  rw [hJ1, hJ2] at hcomp
  rw [← autocorr_zero_eq]
  change (∫ t in Ioc (0 : ℝ) r, D t / t) +
      (EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r) * M -
      (∫ x, F x) ^ 2 / 4 + (∫ t in Ioc (0 : ℝ) r, t * autocorr F t) / 24 +
      (∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t) / 16 +
      (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t * D t) = _
  nlinarith only [hcomp, hsplit]


/-- The exact mean charge and the first two correlation moments survive the Gamma comparison. -/
theorem gamma_ge_logarithmic_lag_and_correlation_moments {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hs : tsupport F ⊆ Icc (-(r / 2)) (r / 2)) :
    (∫ t in Ioc (0 : ℝ) r, (autocorr F 0 - autocorr F t) / t) +
      (EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r) *
        (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
      (∫ t in Ioc (0 : ℝ) r, t * autocorr F t) / 24 +
      (∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t) / 16 ≤
        EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F := by
  have he := gamma_eq_logarithmic_lag_correlation_moments_and_remainder hF hcs hr hr1 hs
  have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
      (autocorr F 0 - autocorr F t) := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact mul_nonneg (retainedGammaRemainderWeight_nonneg ⟨ht.1, ht.2.trans hr1⟩)
      (sub_nonneg.mpr ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t)))
  linarith only [he, hn]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_eq_logarithmic_lag_correlation_moments_and_remainder
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_ge_logarithmic_lag_and_correlation_moments
