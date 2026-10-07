import GaloisForLFunctions.RHTower.WeilWorkQuantizationBoundaryPhase
import GaloisForLFunctions.RHTower.WeilBoundaryIntegerCountingRigidity

/-!
# Canonical phase limits at atomic endpoints

The Poisson phase of a bounded interval converges without requiring null endpoints.
Each endpoint contributes half its atom. This supplies the finite phase limits needed
to construct radial boundary traces; it asserts no boundary continuity or quantization.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace RHTower.WeilSpectral

/-- The limiting Poisson window, including its half-weighted endpoints. -/
def endpointPhaseWindow (a b r : ℝ) : ℝ :=
  (Ioo a b).indicator (fun _ => Real.pi) r +
    ({a} : Set ℝ).indicator (fun _ => Real.pi / 2) r +
    ({b} : Set ℝ).indicator (fun _ => Real.pi / 2) r

theorem tendsto_intervalPhaseKernel_endpoints {a b : ℝ} (hab : a < b) (r : ℝ) :
    Tendsto (fun η => intervalPhaseKernel η a b r) (𝓝[>] 0)
      (𝓝 (endpointPhaseWindow a b r)) := by
  by_cases hra : r = a
  · subst r
    simpa [intervalPhaseKernel, endpointPhaseWindow, hab.ne, hab.ne'] using
      (tendsto_arctan_div_pos (sub_pos.mpr hab))
  by_cases hrb : r = b
  · subst r
    have h := (tendsto_arctan_div_neg (sub_neg.mpr hab)).neg
    simpa [intervalPhaseKernel, endpointPhaseWindow, hab.ne, hab.ne'] using h
  have hset : r ∈ Ioc a b ↔ r ∈ Ioo a b := by
    simp only [mem_Ioc, mem_Ioo]
    exact and_congr_right fun _ => le_iff_lt_or_eq.trans (or_iff_left hrb)
  simpa [endpointPhaseWindow, hra, hrb, indicator, hset] using
    tendsto_intervalPhaseKernel hab hra hrb

/-- Stieltjes inversion with the endpoint atoms retained. -/
theorem tendsto_integral_intervalPhaseKernel_endpoints {μ : Measure ℝ}
    (hμ : Integrable (fun r : ℝ => (1 + r ^ 2)⁻¹) μ) {a b : ℝ} (hab : a < b)
    (hfin : μ (Icc a b) ≠ ∞) :
    Tendsto (fun η => ∫ r, intervalPhaseKernel η a b r ∂μ) (𝓝[>] 0)
      (𝓝 (Real.pi * μ.real (Ioo a b) + Real.pi / 2 * μ.real {a} +
        Real.pi / 2 * μ.real {b})) := by
  let C : ℝ := Real.pi * (1 + 4 * (|a| + |b| + 1) ^ 2) + 8 * (b - a)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ᵐ r ∂μ,
      ‖intervalPhaseKernel η a b r‖ ≤ C * (1 + r ^ 2)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with η hη
    exact Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalPhaseKernel_nonneg hη.1 hab.le r)]
      exact intervalPhaseKernel_le_weight hη.1 hη.2.le hab.le r
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun r => C * (1 + r ^ 2)⁻¹)
    (Eventually.of_forall fun η => (continuous_intervalPhaseKernel η a b).aestronglyMeasurable)
    hbound (hμ.const_mul C)
    (Eventually.of_forall (tendsto_intervalPhaseKernel_endpoints hab))
  have hi : Integrable ((Ioo a b).indicator (fun _ : ℝ => Real.pi)) μ :=
    (integrableOn_const (ne_top_of_le_ne_top hfin (measure_mono Ioo_subset_Icc_self))).integrable_indicator
      measurableSet_Ioo
  have ha : Integrable (({a} : Set ℝ).indicator (fun _ : ℝ => Real.pi / 2)) μ :=
    (integrableOn_const (ne_top_of_le_ne_top hfin
      (measure_mono (singleton_subset_iff.mpr (left_mem_Icc.mpr hab.le))))).integrable_indicator
      (measurableSet_singleton a)
  have hb : Integrable (({b} : Set ℝ).indicator (fun _ : ℝ => Real.pi / 2)) μ :=
    (integrableOn_const (ne_top_of_le_ne_top hfin
      (measure_mono (singleton_subset_iff.mpr (right_mem_Icc.mpr hab.le))))).integrable_indicator
      (measurableSet_singleton b)
  simp only [endpointPhaseWindow] at hlim
  have hiha : Integrable (fun r => (Ioo a b).indicator (fun _ => Real.pi) r +
      ({a} : Set ℝ).indicator (fun _ => Real.pi / 2) r) μ := hi.add ha
  rw [integral_add hiha hb, integral_add hi ha] at hlim
  simpa only [
    integral_indicator_const _ measurableSet_Ioo,
    integral_indicator_const _ (measurableSet_singleton a),
    integral_indicator_const _ (measurableSet_singleton b), smul_eq_mul, mul_comm] using hlim

/-- Every canonical interval has a finite phase limit, even at atomic endpoints. -/
theorem tendsto_re_weilContinuation_interval_endpoints {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {a b : ℝ} (hab : a < b) :
    Tendsto (fun η : ℝ => ∫ t in Ioc a b,
      (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re)
      (𝓝[>] 0)
      (𝓝 (Real.pi * (boundaryMeasure hW).real (Ioo a b) +
        Real.pi / 2 * (boundaryMeasure hW).real {a} +
        Real.pi / 2 * (boundaryMeasure hW).real {b})) := by
  have hfin : boundaryMeasure hW (Icc a b) ≠ ∞ :=
    ne_top_of_le_ne_top (boundaryMeasure_Ioo_ne_top hW (a - 1) (b + 1))
      (measure_mono (by intro r hr; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩))
  refine (tendsto_integral_intervalPhaseKernel_endpoints
    (integrable_inv_one_add_sq hW) hab hfin).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  exact (setIntegral_re_weilContinuation_interval hW hη hab.le).symm

end RHTower.WeilSpectral
