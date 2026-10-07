import GaloisForLFunctions.RHTower.WeilWorkQuantizationKernel
import GaloisForLFunctions.RHTower.WeilFullConeHorizontalPotential

/-!
# Canonical Weil interval phase

The shrinking-width integral of the real part of the canonical Weil continuation
converges to `π` times the canonical boundary measure of an interval. The same
full-Lebesgue-measure endpoint set works for every interval. No atomicity or
meromorphic extension across the boundary is required.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace RHTower.WeilSpectral

/-- The vertical phase integral at any positive distance from the critical line. -/
theorem setIntegral_re_weilContinuation_interval {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) :
    ∫ t in Ioc a b, (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re =
      ∫ r, intervalPhaseKernel η a b r ∂boundaryMeasure hW := by
  set μ := boundaryMeasure hW
  haveI := sFinite_boundaryMeasure hW
  set g : ℝ → ℝ → ℝ := fun t r => η / (η ^ 2 + (r - t) ^ 2)
  have hg0 : ∀ t r, 0 ≤ g t r := fun t r => by dsimp [g]; positivity
  have hpt : ∀ t : ℝ,
      ENNReal.ofReal (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re =
        ∫⁻ r, ENNReal.ofReal (g t r) ∂μ := by
    intro t
    simpa [g] using ofReal_re_weilContinuation_eq hW (1 / 2 + η) t (by linarith)
  have hre0 : ∀ t : ℝ,
      0 ≤ (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re := fun t =>
    re_weilContinuation_nonneg hW (by simp; linarith)
  have hcont : Continuous fun t : ℝ =>
      (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re := by
    refine Complex.continuous_re.comp ?_
    exact (differentiableOn_weilContinuation hW).continuousOn.comp_continuous (by fun_prop)
      fun t => show (1 / 2 : ℝ) < (((1 / 2 + η : ℝ) : ℂ) + t * I).re by simp; linarith
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hre0)
    hcont.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (intervalPhaseKernel_nonneg hη hab))
      (continuous_intervalPhaseKernel η a b).aestronglyMeasurable]
  congr 1
  simp_rw [hpt]
  have hmeas : Measurable (Function.uncurry fun (t : ℝ) (r : ℝ) => ENNReal.ofReal (g t r)) :=
    ENNReal.measurable_ofReal.comp (by dsimp [g]; fun_prop)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hint : IntegrableOn (fun t => g t r) (Ioc a b) :=
    ((continuous_const.div (by fun_prop) (fun t => by positivity) : Continuous fun t : ℝ =>
      η / (η ^ 2 + (r - t) ^ 2)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => hg0 t r),
    ← intervalIntegral.integral_of_le hab]
  dsimp [g]
  rw [integral_poisson_interval hη]

/-- Exact unsmoothed interval recovery at all non-atomic endpoints. -/
theorem tendsto_re_weilContinuation_interval {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {a b : ℝ} (hab : a < b) (ha : boundaryMeasure hW {a} = 0)
    (hb : boundaryMeasure hW {b} = 0) :
    Tendsto (fun η : ℝ => ∫ t in Ioc a b,
      (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re)
      (𝓝[>] 0) (𝓝 (Real.pi * (boundaryMeasure hW).real (Ioc a b))) := by
  refine (tendsto_integral_intervalPhaseKernel (integrable_inv_one_add_sq hW) hab ha hb).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  exact (setIntegral_re_weilContinuation_interval hW hη hab.le).symm

/-- One endpoint set, of full Lebesgue measure, works for every canonical interval limit. -/
theorem exists_fullMeasure_interval_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ Y : Set ℝ, volume Yᶜ = 0 ∧ ∀ a ∈ Y, ∀ b ∈ Y, a < b →
      Tendsto (fun η : ℝ => ∫ t in Ioc a b,
        (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re)
        (𝓝[>] 0) (𝓝 (Real.pi * (boundaryMeasure hW).real (Ioc a b))) := by
  haveI := sFinite_boundaryMeasure hW
  refine ⟨{a | boundaryMeasure hW {a} = 0}, ?_, fun a ha b hb hab =>
    tendsto_re_weilContinuation_interval hW hab ha hb⟩
  have hc : {a : ℝ | 0 < boundaryMeasure hW {a}}.Countable := by
    simpa using (Measure.countable_meas_level_set_pos (μ := boundaryMeasure hW)
      (g := fun r : ℝ => r) measurable_id)
  convert hc.measure_zero volume using 1
  congr 1
  ext a
  simp [pos_iff_ne_zero]

/-- The doubled reflection phase measures interval mass modulo one half. -/
theorem tendsto_exp_four_mul_interval_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {a b : ℝ} (hab : a < b) (ha : boundaryMeasure hW {a} = 0)
    (hb : boundaryMeasure hW {b} = 0) :
    Tendsto (fun η : ℝ => Complex.exp (4 * I * Complex.ofReal (∫ t in Ioc a b,
      (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re)))
      (𝓝[>] 0)
      (𝓝 (Complex.exp (4 * I * Complex.ofReal (Real.pi * (boundaryMeasure hW).real (Ioc a b))))) := by
  simpa only [Function.comp_def] using Complex.continuous_exp.tendsto _ |>.comp
    (((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_re_weilContinuation_interval hW hab ha hb)).const_mul (4 * I))

end RHTower.WeilSpectral
