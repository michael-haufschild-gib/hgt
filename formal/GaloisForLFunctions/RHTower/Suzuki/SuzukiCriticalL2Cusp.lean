import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Energy
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalTranslatedCusp
import GaloisForLFunctions.HTGeometry.SmoothCompactL2Dense

/-!
# Uniform critical Suzuki cusps for arbitrary real L² sources

The primary cusp is uniformly stable under L² approximation of the source.
Smooth compact density and the exact primary mass extend atom convergence to
all real L² sources, including sources of infinite limiting Lévy energy.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open GaloisForLFunctions.HTGeometry


namespace RHTower
open ArchimedeanAnomaly ArchimedeanExactForm
noncomputable section

/-- Primary cusps depend only on the almost-everywhere source class. -/
theorem suzukiCriticalPrimaryCusp_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) (omega u : ℝ) :
    suzukiCriticalPrimaryCusp f omega u = suzukiCriticalPrimaryCusp g omega u := by
  unfold suzukiCriticalPrimaryCusp
  apply integral_congr_ae
  exact Eventually.of_forall fun t => congrArg
    (fun c => c * suzukiCriticalPrimaryDensity omega t) (autocorr_congr_ae hfg (u+t))

/-- Every L² correlation is absolutely integrable against an admissible primary density. -/
theorem integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {omega : ℝ} (homega : 0 < omega) (homega5 : omega < 5/2) (u : ℝ) :
    IntegrableOn (fun t => autocorr f (u+t) * suzukiCriticalPrimaryDensity omega t)
      (Ioi 0) := by
  apply (integrableOn_suzukiCriticalPrimaryDensity homega homega5).bdd_mul
    (((continuous_autocorr_of_memLp hf).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.add_apply, id_eq] using
      abs_autocorr_le_zero_of_memLp hf (u+t)

/-- The exact kernel mass controls cusp differences uniformly in the translation. -/
theorem abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms (q r : Velocity) {omega : ℝ}
    (homega : 0 < omega) (homega5 : omega < 5/2) (u : ℝ) :
    |suzukiCriticalPrimaryCusp q omega u - suzukiCriticalPrimaryCusp r omega u| ≤
      suzukiCriticalPrimaryMass omega * ((‖q‖ + ‖r‖) * ‖q-r‖) := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hq := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp (Lp.memLp q) homega homega5 u
  have hr := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp (Lp.memLp r) homega homega5 u
  have he : suzukiCriticalPrimaryCusp q omega u - suzukiCriticalPrimaryCusp r omega u =
      ∫ t in Ioi 0, (autocorr q (u+t)-autocorr r (u+t)) *
        suzukiCriticalPrimaryDensity omega t := by
    unfold suzukiCriticalPrimaryCusp
    rw [← integral_sub hq hr]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => (sub_mul _ _ _).symm
  rw [he]
  have hi : IntegrableOn (fun t => (autocorr q (u+t)-autocorr r (u+t)) *
      suzukiCriticalPrimaryDensity omega t) (Ioi 0) := by
    apply (hq.sub hr).congr_fun _ measurableSet_Ioi
    intro t _
    dsimp only [Pi.sub_apply]
    ring
  calc
    _ ≤ ∫ t in Ioi 0, ‖(autocorr q (u+t)-autocorr r (u+t)) *
        suzukiCriticalPrimaryDensity omega t‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => (autocorr q (u+t)-autocorr r (u+t)) * suzukiCriticalPrimaryDensity omega t)
        (μ := volume.restrict (Ioi 0))
    _ ≤ ∫ t in Ioi 0, ((‖q‖+‖r‖)*‖q-r‖) * suzukiCriticalPrimaryDensity omega t := by
      apply integral_mono_ae hi.norm (hB.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (suzukiCriticalPrimaryDensity_pos homega ht).le]
      exact mul_le_mul_of_nonneg_right (autocorr_sub_le_L2_norms q r (u+t))
        (suzukiCriticalPrimaryDensity_pos homega ht).le
    _ = _ := by
      rw [integral_const_mul, integral_suzukiCriticalPrimaryDensity homega homega5, mul_comm]

/-- Smooth compact density extends uniform atom convergence to every L² class. -/
theorem tendstoUniformly_suzukiCriticalPrimaryCusp_L2 (q : Velocity) :
    TendstoUniformly (suzukiCriticalPrimaryCusp q) (autocorr q) (𝓝[>] 0) := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hD : 0 < 2*‖q‖+1 := by positivity
  have hdelta : 0 < min (1 : ℝ) (epsilon / (6*(2*‖q‖+1))) :=
    lt_min (by norm_num) (div_pos hepsilon (mul_pos (by norm_num) hD))
  obtain ⟨r, hr, hqr⟩ := dense_smoothCompactSubmodule.exists_dist_lt q hdelta
  rw [dist_eq_norm] at hqr
  have hqr1 : ‖q-r‖ < 1 := lt_of_lt_of_le hqr (min_le_left _ _)
  have hqr2 : ‖q-r‖ < epsilon / (6*(2*‖q‖+1)) :=
    lt_of_lt_of_le hqr (min_le_right _ _)
  have hrnorm : ‖r‖ ≤ ‖q‖+‖q-r‖ := by
    calc
      _ = ‖q+(r-q)‖ := by rw [add_sub_cancel]
      _ ≤ ‖q‖+‖r-q‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hbound : ‖q‖+‖r‖ ≤ 2*‖q‖+1 := by linarith only [hrnorm, hqr1]
  have herr : (‖q‖+‖r‖)*‖q-r‖ < epsilon/6 := by
    have hx := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<6) hD)).mp hqr2
    have hy := mul_le_mul_of_nonneg_right hbound (norm_nonneg (q-r))
    nlinarith only [hx, hy]
  obtain ⟨g, hrg, hgc, hgd⟩ := hr
  have hg2 : ContDiff ℝ 2 g := hgd.of_le (by
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hgu := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_suzukiCriticalPrimaryCusp hg2 hgc)) (epsilon/3) (by positivity)
  have hM : ∀ᶠ omega : ℝ in 𝓝[>] 0, suzukiCriticalPrimaryMass omega < 2 :=
    (tendsto_suzukiCriticalPrimaryMass.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ)<2))
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<2))
  filter_upwards [self_mem_nhdsWithin, ho, hM, hgu] with omega homega ho hM hgu u
  change 0 < omega at homega
  have hcu : |suzukiCriticalPrimaryCusp r omega u-autocorr r u| < epsilon/3 := by
    rw [suzukiCriticalPrimaryCusp_congr_ae hrg, autocorr_congr_ae hrg]
    simpa only [Real.dist_eq, abs_sub_comm] using hgu u
  have hcorr := autocorr_sub_le_L2_norms q r u
  have hcusps := abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms q r homega (by linarith) u
  have hE : 0 ≤ (‖q‖+‖r‖)*‖q-r‖ := by positivity
  have hmass := mul_le_mul_of_nonneg_right hM.le hE
  rw [Real.dist_eq, abs_sub_comm]
  calc
    _ ≤ |suzukiCriticalPrimaryCusp q omega u-suzukiCriticalPrimaryCusp r omega u| +
        |suzukiCriticalPrimaryCusp r omega u-autocorr r u| +
        |autocorr r u-autocorr q u| := by
      have h1 := abs_sub_le (suzukiCriticalPrimaryCusp q omega u)
        (suzukiCriticalPrimaryCusp r omega u) (autocorr q u)
      have h2 := abs_sub_le (suzukiCriticalPrimaryCusp r omega u) (autocorr r u) (autocorr q u)
      linarith only [h1, h2]
    _ < epsilon := by
      rw [abs_sub_comm (autocorr r u)]
      linarith only [hcusps, hmass, hcu, hcorr, herr, hepsilon]

/-- Every real L² source has uniform primary cusp convergence, without a finite-energy premise. -/
theorem tendstoUniformly_suzukiCriticalPrimaryCusp_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    TendstoUniformly (suzukiCriticalPrimaryCusp f) (autocorr f) (𝓝[>] 0) := by
  have hc : suzukiCriticalPrimaryCusp f = suzukiCriticalPrimaryCusp (hf.toLp f) := by
    funext omega u
    exact suzukiCriticalPrimaryCusp_congr_ae hf.coeFn_toLp.symm omega u
  have ha : autocorr f = autocorr (hf.toLp f) := by
    funext u
    exact autocorr_congr_ae hf.coeFn_toLp.symm u
  rw [hc, ha]
  exact tendstoUniformly_suzukiCriticalPrimaryCusp_L2 (hf.toLp f)

end
end RHTower

