import GaloisForLFunctions.BiScaleUncertainty.NyquistCriticalSourceClassification
import GaloisForLFunctions.BiScaleUncertainty.LocalCorrelationEnergyStability

/-!
# Quantitative normalized critical Nyquist sources

The actual stretched sources satisfy an exact first-moment energy bound and
uniform correlation convergence on bounded intervals. Ordinary zero mean is
necessary and sufficient for a finite critical residual limit.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported NNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
namespace GaloisForLFunctions.BiScaleUncertainty
set_option autoImplicit false

/-- A nonzero compact continuous source has strictly positive correlation mass. -/
theorem nyquistSourceMass_pos (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) : 0 < autocorr f 0 := by
  have hnonneg : 0 ≤ autocorr f 0 := by
    unfold autocorr
    simp only [add_zero]
    exact integral_nonneg fun u => mul_self_nonneg (f u)
  have hn : autocorr f 0 ≠ 0 := by
    intro h
    have hz := nyquistNormalizedCorrelation_zero f hne
    change autocorr f 0 / autocorr f 0 = 1 at hz
    rw [h, zero_div] at hz
    exact zero_ne_one hz
  exact lt_of_le_of_ne hnonneg hn.symm

/-- Signed normalized correlations are bounded by one in absolute value. -/
theorem abs_nyquistNormalizedCorrelation_le_one (f : C_c(ℝ, ℝ)) (hne : f ≠ 0) (x : ℝ) :
    |nyquistNormalizedCorrelation f x| ≤ 1 := by
  change |autocorr f x / autocorr f 0| ≤ 1
  rw [abs_div, abs_of_pos (nyquistSourceMass_pos f hne)]
  exact (div_le_one (nyquistSourceMass_pos f hne)).mpr
    (abs_autocorr_le_zero f.hasCompactSupport f.continuous x)

/-- The exact correlation error at every lag and every positive dilation. -/
theorem abs_nyquistNormalizedCorrelation_scaled_sub_one_le (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) {A : ℝ≥0} (hA : LipschitzWith A (nyquistNormalizedCorrelation f))
    {L : ℝ} (hL : 0 < L) (x : ℝ) :
    |nyquistNormalizedCorrelation f (x / L) - 1| ≤ (A : ℝ) * |x| / L := by
  have hb := hA.dist_le_mul (x / L) 0
  rw [nyquistNormalizedCorrelation_zero f hne, Real.dist_eq, Real.dist_eq,
    sub_zero, abs_div, abs_of_pos hL] at hb
  simpa only [mul_div_assoc] using hb

private theorem normalized_source_levy_integrand_eq (f : C_c(ℝ, ℝ))
    (hne : f ≠ 0) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    (autocorr (sourceRescale f L⁻¹) 0 - autocorr (sourceRescale f L⁻¹) x) *
        archLevySinhWeight x / autocorr (sourceRescale f L⁻¹) 0 =
      (1 - nyquistNormalizedCorrelation f (x / L)) * archLevySinhWeight x := by
  have hmass : 0 < autocorr (sourceRescale f L⁻¹) 0 := by
    rw [autocorr_sourceRescale f (inv_pos.mpr hL), mul_zero, inv_inv]
    exact mul_pos hL (nyquistSourceMass_pos f hne)
  rw [← normalized_sourceRescale_eq_nyquistNormalizedCorrelation f hne hL]
  field_simp [hmass.ne']

/-- Exact normalized energy integral of the actual stretched source. -/
theorem normalizedArchEnergy_broadSource_eq (f : C_c(ℝ, ℝ)) (hne : f ≠ 0)
    {L : ℝ} (hL : 0 < L) :
    normalizedArchEnergy (sourceRescale f L⁻¹) =
      ∫ x in Ioi 0, (1 - nyquistNormalizedCorrelation f (x / L)) * archLevySinhWeight x := by
  rw [normalizedArchEnergy_eq_integral]
  exact integral_congr_ae (Eventually.of_forall
    (normalized_source_levy_integrand_eq f hne hL))

/-- Every correlation Lipschitz constant supplies the exact first-moment energy bound. -/
theorem normalizedArchEnergy_broadSource_bounds (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0)
    {A : ℝ≥0} (hA : LipschitzWith A (nyquistNormalizedCorrelation f))
    {L : ℝ} (hL : 0 < L) :
    0 ≤ normalizedArchEnergy (sourceRescale f L⁻¹) ∧
      normalizedArchEnergy (sourceRescale f L⁻¹) ≤ (A : ℝ) * archWeightFirstMoment / L := by
  have hreg := contDiff_sourceRescale hf L⁻¹
  have hcomp := hasCompactSupport_sourceRescale f.hasCompactSupport (inv_pos.mpr hL)
  have hi : IntegrableOn (fun x =>
      (1 - nyquistNormalizedCorrelation f (x / L)) * archLevySinhWeight x) (Ioi 0) := by
    apply ((integrableOn_biScaleLevyIntegrand hreg hcomp).div_const
      (autocorr (sourceRescale f L⁻¹) 0)).congr
    exact Eventually.of_forall (normalized_source_levy_integrand_eq f hne hL)
  rw [normalizedArchEnergy_broadSource_eq f hne hL]
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (sub_nonneg.mpr (le_trans (le_abs_self _)
      (abs_nyquistNormalizedCorrelation_le_one f hne (x / L))))
      (archLevySinhWeight_pos hx).le
  · calc
      _ ≤ ∫ x in Ioi 0, ((A : ℝ) / L) * (x * archLevySinhWeight x) := by
        apply setIntegral_mono_on hi
          (integrableOn_mul_archLevySinhWeight.const_mul ((A : ℝ) / L)) measurableSet_Ioi
        intro x hx
        have hb := abs_nyquistNormalizedCorrelation_scaled_sub_one_le f hne hA hL x
        rw [abs_of_pos (show (0 : ℝ) < x from hx)] at hb
        have hd : 1 - nyquistNormalizedCorrelation f (x / L) ≤ (A : ℝ) * x / L := by
          have hb' := (abs_le.mp hb).1
          linarith only [hb']
        calc
          _ ≤ ((A : ℝ) * x / L) * archLevySinhWeight x :=
            mul_le_mul_of_nonneg_right hd (archLevySinhWeight_pos hx).le
          _ = _ := by ring
      _ = _ := by rw [integral_const_mul]; unfold archWeightFirstMoment; ring

/-- Every source Lipschitz constant gives the explicit `K ∫|f| W/(R L)` energy ceiling. -/
theorem normalizedArchEnergy_broadSource_le_of_source_lipschitz (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) {K : ℝ≥0}
    (hK : LipschitzWith K (f : ℝ → ℝ)) {L : ℝ} (hL : 0 < L) :
    normalizedArchEnergy (sourceRescale f L⁻¹) ≤
      (K : ℝ) * (∫ u, |f u|) * archWeightFirstMoment / (autocorr f 0 * L) := by
  have hb := (normalizedArchEnergy_broadSource_bounds f hf hne
    (lipschitzWith_nyquistNormalizedCorrelation_of_source f hne hK) hL).2
  change normalizedArchEnergy (sourceRescale f L⁻¹) ≤
    ((K : ℝ) * (∫ u, |f u|) / autocorr f 0) * archWeightFirstMoment / L at hb
  convert hb using 1
  ring

/-- Normalized correlations converge uniformly to one on every fixed bounded interval. -/
theorem tendstoUniformlyOn_nyquistNormalizedCorrelation (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (R : ℝ) :
    TendstoUniformlyOn (fun L x => nyquistNormalizedCorrelation f (x / L))
      (fun _ => 1) atTop (Icc (-R) R) := by
  obtain ⟨A, hA⟩ := exists_lipschitzWith_nyquistNormalizedCorrelation f hf hne
  have hb : Tendsto (fun L : ℝ => (A : ℝ) * R / L) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul ((A : ℝ) * R)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hb.eventually (gt_mem_nhds hε)] with L hL hsmall x hx
  rw [Real.dist_eq, abs_sub_comm]
  have hbound : |nyquistNormalizedCorrelation f (x / L) - 1| ≤ (A : ℝ) * R / L :=
    (abs_nyquistNormalizedCorrelation_scaled_sub_one_le f hne hA hL x).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_le.mpr hx) A.coe_nonneg) hL.le)
  exact hbound.trans_lt hsmall

/-- The actual normalized correlations of stretched sources converge uniformly on bounded intervals. -/
theorem tendstoUniformlyOn_normalized_broadSource (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) (R : ℝ) :
    TendstoUniformlyOn (fun L x =>
      autocorr (sourceRescale f L⁻¹) x / autocorr (sourceRescale f L⁻¹) 0)
      (fun _ => 1) atTop (Icc (-R) R) := by
  have hu := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_nyquistNormalizedCorrelation f hf hne R)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hu ε hε] with L hL hclose x hx
  rw [normalized_sourceRescale_eq_nyquistNormalizedCorrelation f hne hL]
  exact hclose x hx

/-- The critical residual has the finite-part limit exactly for ordinary mean-zero sources. -/
theorem tendsto_nyquistCriticalSourceResidual_iff_mean_zero (m : ℕ) (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) :
    Tendsto (nyquistCriticalSourceResidual m f) atTop (𝓝 (nyquistCriticalFinitePart m)) ↔
      (∫ u, f u) = 0 := by
  constructor
  · intro hlim
    by_contra hmean
    have hinf := tendsto_nyquistCriticalSourceResidual_atTop_of_mean_ne_zero m f hf hne hmean
    have he := (hlim.eventually (gt_mem_nhds (by linarith : nyquistCriticalFinitePart m <
      nyquistCriticalFinitePart m + 1))).and
      (hinf.eventually_ge_atTop (nyquistCriticalFinitePart m + 1))
    obtain ⟨L, hL⟩ := he.exists
    exact (not_lt_of_ge hL.2) hL.1
  · exact tendsto_nyquistCriticalSourceResidual_of_mean_zero m f hf hne

end GaloisForLFunctions.BiScaleUncertainty

