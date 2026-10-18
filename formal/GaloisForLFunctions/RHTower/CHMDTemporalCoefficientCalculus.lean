import GaloisForLFunctions.RHTower.CHMDTemporalCosineExtraction

/-!
# Bounded signals with a temporal cosine coefficient

Linearity and dominated integration preserve the exact temporal coefficient.
The boundedness field also controls finite arithmetic approximants.
-/

open MeasureTheory Filter Set Topology

namespace RHTower.CHMDChebyshevTransport

noncomputable section

/-- A bounded measurable signal with its normalized forward cosine coefficient. -/
structure HasTemporalCoefficient (f : ℝ → ℝ) (lam c : ℝ) : Prop where
  measurable : Measurable f
  bound : ∃ C : ℝ, ∀ y : ℝ, |f y| ≤ C
  limit : Tendsto (temporalCosineAverage f lam) atTop (𝓝 c)

namespace HasTemporalCoefficient

theorem integrable {f : ℝ → ℝ} {lam c : ℝ} (h : HasTemporalCoefficient f lam c) (T : ℝ) :
    IntegrableOn (fun t => f (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1) := by
  obtain ⟨C, hC⟩ := h.bound
  exact integrable_temporalCosineIntegrand h.measurable hC lam T

theorem const_mul {f : ℝ → ℝ} {lam c : ℝ} (h : HasTemporalCoefficient f lam c) (a : ℝ) :
    HasTemporalCoefficient (fun y => a * f y) lam (a * c) := by
  refine ⟨measurable_const.mul h.measurable, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bound
    exact ⟨|a| * C, fun y => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC y) (abs_nonneg a)⟩
  · simpa only [← temporalCosineAverage_const_mul] using h.limit.const_mul a

theorem add {f g : ℝ → ℝ} {lam c d : ℝ}
    (hf : HasTemporalCoefficient f lam c) (hg : HasTemporalCoefficient g lam d) :
    HasTemporalCoefficient (fun y => f y + g y) lam (c + d) := by
  refine ⟨hf.measurable.add hg.measurable, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hf.bound
    obtain ⟨D, hD⟩ := hg.bound
    exact ⟨C + D, fun y => (abs_add_le _ _).trans (add_le_add (hC y) (hD y))⟩
  · exact (hf.limit.add hg.limit).congr (fun T =>
      (temporalCosineAverage_add lam T (hf.integrable T) (hg.integrable T)).symm)

theorem sub {f g : ℝ → ℝ} {lam c d : ℝ}
    (hf : HasTemporalCoefficient f lam c) (hg : HasTemporalCoefficient g lam d) :
    HasTemporalCoefficient (fun y => f y - g y) lam (c - d) := by
  refine ⟨hf.measurable.sub hg.measurable, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hf.bound
    obtain ⟨D, hD⟩ := hg.bound
    exact ⟨C + D, fun y => (abs_sub _ _).trans (add_le_add (hC y) (hD y))⟩
  · exact (hf.limit.sub hg.limit).congr (fun T =>
      (temporalCosineAverage_sub lam T (hf.integrable T) (hg.integrable T)).symm)

theorem congr {f g : ℝ → ℝ} {lam c : ℝ} (hf : HasTemporalCoefficient f lam c)
    (hfg : ∀ y, f y = g y) : HasTemporalCoefficient g lam c := by
  exact (funext hfg) ▸ hf

theorem of_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {F : ℝ → α → ℝ} {b L : α → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Integrable b μ)
    (hbound : ∀ y x, |F y x| ≤ b x) {lam : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto (temporalCosineAverage (fun y => F y x) lam) atTop
      (𝓝 (L x))) :
    HasTemporalCoefficient (fun y => ∫ x, F y x ∂μ) lam (∫ x, L x ∂μ) := by
  refine ⟨hF.stronglyMeasurable.integral_prod_right.measurable, ?_,
    temporalCosineAverage_integral_tendsto hF hb hbound hlim⟩
  refine ⟨∫ x, b x ∂μ, fun y => ?_⟩
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hb
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound y x)

theorem finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {c : ι → ℝ} {lam : ℝ}
    (h : ∀ i ∈ s, HasTemporalCoefficient (f i) lam (c i)) :
    HasTemporalCoefficient (fun y => ∑ i ∈ s, f i y) lam (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨measurable_const, ⟨0, by simp⟩, ?_⟩
    change Tendsto (fun T => temporalCosineAverage (fun _ => 0) lam T) atTop (𝓝 0)
    simpa only [temporalCosineAverage, zero_mul, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  | @insert a s ha ih =>
    have hsum := (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using hsum

end HasTemporalCoefficient

end

end RHTower.CHMDChebyshevTransport
