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
  refine ⟨hF.stronglyMeasurable.integral_prod_right'.measurable, ?_,
    temporalCosineAverage_integral_tendsto hF hb hbound hlim⟩
  refine ⟨∫ x, b x ∂μ, fun y => ?_⟩
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (f := F y) hb
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

/-- An absolutely summable positive cosine series retains every frequency mass. -/
theorem hasTemporalCoefficient_tsum_cos {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι] (a w : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (hw : ∀ i, 0 < w i)
    {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient (fun y => ∑' i, a i * Real.cos (w i * y)) lam
      (∑' i, if w i = lam then a i / 2 else 0) := by
  classical
  have hi : Integrable a Measure.count := integrable_count_iff.mpr
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hs)
  have hm : Measurable (fun p : ℝ × ι => a p.2 * Real.cos (w p.2 * p.1)) :=
    ((measurable_of_countable a).comp measurable_snd).mul
      (Real.continuous_cos.measurable.comp
        (((measurable_of_countable w).comp measurable_snd).mul measurable_fst))
  have hb (y : ℝ) (i : ι) : |a i * Real.cos (w i * y)| ≤ a i := by
    rw [abs_mul, abs_of_nonneg (ha i)]
    exact mul_le_of_le_one_right (ha i) (Real.abs_cos_le_one _)
  have h := HasTemporalCoefficient.of_integral
    (F := fun y i => a i * Real.cos (w i * y)) hm hi hb (lam := lam)
    (L := fun i => if w i = lam then a i / 2 else 0)
    (Eventually.of_forall fun i => by
      have h := (temporalCosineAverage_cos_tendsto (hw i) hlam).const_mul (a i)
      have heq : a i * (if w i = lam then (1 / 2 : ℝ) else 0) =
          (if w i = lam then a i / 2 else 0) := by split_ifs <;> ring
      simpa only [← temporalCosineAverage_const_mul, heq] using h)
  have hif (y : ℝ) : Integrable (fun i => a i * Real.cos (w i * y)) Measure.count :=
    hi.mono' (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun i => by simpa only [Real.norm_eq_abs] using hb y i)
  have hiL : Integrable (fun i => if w i = lam then a i / 2 else 0) Measure.count := by
    refine hi.mono' (measurable_of_countable _).aestronglyMeasurable (Eventually.of_forall fun i => ?_)
    rw [Real.norm_eq_abs]
    split_ifs
    · rw [abs_of_nonneg (div_nonneg (ha i) (by norm_num))]
      linarith [ha i]
    · simpa only [abs_zero] using ha i
  have heq (y : ℝ) : (∫ i, a i * Real.cos (w i * y) ∂Measure.count) =
      ∑' i, a i * Real.cos (w i * y) := by
    simpa only [count_real_singleton, one_smul] using integral_countable (hif y)
  have hL : (∫ i, (if w i = lam then a i / 2 else 0) ∂Measure.count) =
      ∑' i, if w i = lam then a i / 2 else 0 := by
    simpa only [count_real_singleton, one_smul] using integral_countable hiL
  simpa only [heq, hL] using h

end

end RHTower.CHMDChebyshevTransport
