import GaloisForLFunctions.HTGeometry.CosineSumNonposZero

/-!
# Temporal cosine coefficients and dominated spectral mixtures

The average over a dilated unit interval has norm at most one on bounded
functions. It extracts half the mass at a positive cosine frequency.
Integrable spectral mixtures commute with the average and its limit.
-/

open MeasureTheory Filter Set Topology

namespace RHTower.CHMDChebyshevTransport

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Forward cosine observation, normalized on a fixed unit interval. -/
def temporalCosineAverage (f : ℝ → ℝ) (lam T : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, f (T * t) * Real.cos (lam * (T * t))

theorem integrable_temporalCosineIntegrand {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ y, |f y| ≤ C) (lam T : ℝ) :
    IntegrableOn (fun t => f (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1) := by
  refine (integrable_const C).mono'
    ((hf.comp (measurable_const.mul measurable_id)).mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hb _)

theorem temporalCosineAverage_add {f g : ℝ → ℝ} (lam T : ℝ)
    (hf : IntegrableOn (fun t => f (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1))
    (hg : IntegrableOn (fun t => g (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1)) :
    temporalCosineAverage (fun y => f y + g y) lam T =
      temporalCosineAverage f lam T + temporalCosineAverage g lam T := by
  simp only [temporalCosineAverage, add_mul]
  exact integral_add hf hg

theorem temporalCosineAverage_sub {f g : ℝ → ℝ} (lam T : ℝ)
    (hf : IntegrableOn (fun t => f (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1))
    (hg : IntegrableOn (fun t => g (T * t) * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1)) :
    temporalCosineAverage (fun y => f y - g y) lam T =
      temporalCosineAverage f lam T - temporalCosineAverage g lam T := by
  simp only [temporalCosineAverage, sub_mul]
  exact integral_sub hf hg

theorem temporalCosineAverage_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (lam T : ℝ)
    (hf : ∀ i ∈ s, IntegrableOn (fun t => f i (T * t) * Real.cos (lam * (T * t)))
      (Ioc (0 : ℝ) 1)) :
    temporalCosineAverage (fun y => ∑ i ∈ s, f i y) lam T =
      ∑ i ∈ s, temporalCosineAverage (f i) lam T := by
  simp only [temporalCosineAverage, Finset.sum_mul]
  exact integral_finsetSum s hf

theorem temporalCosineAverage_const_mul (c : ℝ) (f : ℝ → ℝ) (lam T : ℝ) :
    temporalCosineAverage (fun y => c * f y) lam T =
      c * temporalCosineAverage f lam T := by
  simp only [temporalCosineAverage, mul_assoc, integral_const_mul]

theorem temporalCosineAverage_eq_interval (f : ℝ → ℝ) (lam : ℝ) {T : ℝ}
    (hT : T ≠ 0) :
    temporalCosineAverage f lam T =
      (∫ y in (0 : ℝ)..T, f y * Real.cos (lam * y)) / T := by
  rw [temporalCosineAverage, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_comp_mul_left
    (fun y => f y * Real.cos (lam * y)) hT]
  simp only [mul_zero, mul_one, smul_eq_mul]
  ring

/-- The observation cannot amplify a uniform bound on the forward half-line. -/
theorem abs_temporalCosineAverage_le {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ y : ℝ, 0 ≤ y → |f y| ≤ C) (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    |temporalCosineAverage f lam T| ≤ C := by
  have h := norm_integral_le_of_norm_le
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun t => f (T * t) * Real.cos (lam * (T * t)))
    (integrable_const C) ?_
  · simpa [temporalCosineAverage, Real.norm_eq_abs] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
      (hC _ (mul_nonneg hT ht.1.le))

theorem temporalCosineAverage_cos_tendsto {a lam : ℝ}
    (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => Real.cos (a * y)) lam) atTop
      (𝓝 (if a = lam then (1 / 2 : ℝ) else 0)) := by
  classical
  by_cases h : a = lam
  · subst a
    simp only [if_true]
    refine (tendsto_integral_cos_sq_div hlam).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (temporalCosineAverage_eq_interval _ _ hT.ne').symm
  · simp only [if_neg h]
    refine (tendsto_integral_cos_mul_cos_div_of_ne ha hlam h).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (temporalCosineAverage_eq_interval _ _ hT.ne').symm

section Mixtures

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
  {F : ℝ → α → ℝ} {b : α → ℝ}

private theorem measurable_temporal_integrand
    (hF : Measurable (Function.uncurry F)) (lam T : ℝ) :
    Measurable (fun p : ℝ × α => F (T * p.1) p.2 *
      Real.cos (lam * (T * p.1))) := by
  exact (hF.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)).mul
    (Real.continuous_cos.measurable.comp
      (measurable_const.mul (measurable_const.mul measurable_fst)))

theorem temporalCosineAverage_integral
    (hF : Measurable (Function.uncurry F)) (hb : Integrable b μ)
    (hbound : ∀ y x, |F y x| ≤ b x) (lam T : ℝ) :
    temporalCosineAverage (fun y => ∫ x, F y x ∂μ) lam T =
      ∫ x, temporalCosineAverage (fun y => F y x) lam T ∂μ := by
  have hi : Integrable
      (fun p : ℝ × α => F (T * p.1) p.2 * Real.cos (lam * (T * p.1)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
    refine (hb.comp_snd _).mono' (measurable_temporal_integrand hF lam T).aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
      (hbound _ _)
  unfold temporalCosineAverage
  simp_rw [← integral_mul_const]
  exact integral_integral_swap hi

/-- A dominated temporal mixture retains the exact coefficient of every component. -/
theorem temporalCosineAverage_integral_tendsto
    (hF : Measurable (Function.uncurry F)) (hb : Integrable b μ)
    (hbound : ∀ y x, |F y x| ≤ b x) {lam : ℝ} {L : α → ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto (temporalCosineAverage (fun y => F y x) lam) atTop
      (𝓝 (L x))) :
    Tendsto (temporalCosineAverage (fun y => ∫ x, F y x ∂μ) lam) atTop
      (𝓝 (∫ x, L x ∂μ)) := by
  have hm (T : ℝ) : Measurable (fun x => temporalCosineAverage (fun y => F y x) lam T) :=
    (measurable_temporal_integrand hF lam T).stronglyMeasurable.integral_prod_left'.measurable
  have h := tendsto_integral_filter_of_dominated_convergence b
    (Eventually.of_forall fun T => (hm T).aestronglyMeasurable) ?_ hb hlim
  · exact h.congr (fun T => (temporalCosineAverage_integral hF hb hbound lam T).symm)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_temporalCosineAverage_le (fun y _ => hbound y x) lam hT

/-- A density assigns no temporal atom to a frequency with a null fibre. -/
theorem temporalCosineAverage_spectralIntegral_tendsto_zero
    {a w : α → ℝ} (ha : Measurable a) (hwa : Integrable a μ)
    (hw : Measurable w) (hwpos : ∀ x, 0 < w x) {lam : ℝ} (hlam : 0 < lam)
    (hfibre : ∀ᵐ x ∂μ, w x ≠ lam) :
    Tendsto (temporalCosineAverage
      (fun y => ∫ x, a x * Real.cos (w x * y) ∂μ) lam) atTop (𝓝 0) := by
  have hm : Measurable (fun p : ℝ × α => a p.2 * Real.cos (w p.2 * p.1)) :=
    (ha.comp measurable_snd).mul
      (Real.continuous_cos.measurable.comp ((hw.comp measurable_snd).mul measurable_fst))
  have hb : ∀ y x, |a x * Real.cos (w x * y)| ≤ |a x| := by
    intro y x
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h := temporalCosineAverage_integral_tendsto hm hwa.abs hb (lam := lam)
    (L := fun _ => 0) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [hfibre] with x hx
    have hl := (temporalCosineAverage_cos_tendsto (hwpos x) hlam).const_mul (a x)
    simpa only [if_neg hx, mul_zero, ← temporalCosineAverage_const_mul] using hl

end Mixtures

end

end RHTower.CHMDChebyshevTransport
