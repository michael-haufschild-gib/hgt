import GaloisForLFunctions.HTGeometry.ClockSecondMoment

/-!
# The mean pairwise distance of a half-line law

The four-unit incidence energy of a clock is four times the mean distance between two independent
copies of it.  This file computes that mean distance from the survival function: for laws carried
by the half line,

`E|X - X'| = E X + E X' - 2 ∫₀^∞ S_X(t) S_{X'}(t) dt`,

because the minimum of two independent variables has survival function the product of theirs.
For the mean-one exponential law the integral is `1/2`, so the mean pairwise distance is one, and
the four-unit energy is four.  Convergence in the half-line transport distance transfers both
values to any family of clocks converging to that law.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {μ ν : Measure ℝ}

/-! ### The law of the minimum of two independent variables -/

theorem measurable_min_pair : Measurable fun w : ℝ × ℝ => min w.1 w.2 :=
  measurable_fst.min measurable_snd

/-- The law of the minimum of two independent variables. -/
def minLaw (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun w : ℝ × ℝ => min w.1 w.2) (μ.prod ν)

instance isProbabilityMeasure_minLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (minLaw μ ν) := by
  rw [minLaw]
  exact Measure.isProbabilityMeasure_map measurable_min_pair.aemeasurable

/-- **The survival function of a minimum is the product of the survival functions.** -/
theorem survival_minLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) : survival (minLaw μ ν) t = survival μ t * survival ν t := by
  have hset : (fun w : ℝ × ℝ => min w.1 w.2) ⁻¹' (Ioi t) = (Ioi t) ×ˢ (Ioi t) := by
    ext w
    simp
  rw [minLaw, survival, Measure.real, Measure.map_apply measurable_min_pair measurableSet_Ioi,
    hset, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

/-- A survival function of a law is at most one. -/
theorem survival_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : survival μ t ≤ 1 := by
  have h : μ.real (Ioi t) ≤ μ.real univ := measureReal_mono (subset_univ (Ioi t))
  rwa [probReal_univ] at h

/-! ### Integrability on a product -/

theorem ae_nonneg_fst_prod (μ ν : Measure ℝ) [IsProbabilityMeasure ν] (hsupp : μ (Iio 0) = 0) :
    ∀ᵐ w ∂(μ.prod ν), 0 ≤ w.1 := by
  have hnull : (μ.prod ν) ((Iio (0 : ℝ)) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hsupp, zero_mul]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro w hw
  exact Set.mem_prod.mpr ⟨not_le.mp hw, Set.mem_univ _⟩

theorem ae_nonneg_snd_prod (μ ν : Measure ℝ) [IsProbabilityMeasure ν] (hsupp : ν (Iio 0) = 0) :
    ∀ᵐ w ∂(μ.prod ν), 0 ≤ w.2 := by
  have hnull : (μ.prod ν) ((univ : Set ℝ) ×ˢ (Iio (0 : ℝ))) = 0 := by
    rw [Measure.prod_prod, hsupp, mul_zero]
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro w hw
  exact Set.mem_prod.mpr ⟨Set.mem_univ _, not_le.mp hw⟩

theorem integrable_fst_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hint : Integrable (id : ℝ → ℝ) μ) : Integrable (fun w : ℝ × ℝ => w.1) (μ.prod ν) := by
  have h : Integrable (id : ℝ → ℝ) (Measure.map Prod.fst (μ.prod ν)) := by
    rw [← Measure.fst, Measure.fst_prod]
    exact hint
  exact (integrable_map_measure measurable_id.aestronglyMeasurable measurable_fst.aemeasurable).mp h

theorem integrable_snd_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hint : Integrable (id : ℝ → ℝ) ν) : Integrable (fun w : ℝ × ℝ => w.2) (μ.prod ν) := by
  have h : Integrable (id : ℝ → ℝ) (Measure.map Prod.snd (μ.prod ν)) := by
    rw [← Measure.snd, Measure.snd_prod]
    exact hint
  exact (integrable_map_measure measurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mp h

theorem integral_fst_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ w : ℝ × ℝ, w.1 ∂(μ.prod ν) = ∫ x, x ∂μ := by
  have h : ∫ y : ℝ, y ∂(Measure.map Prod.fst (μ.prod ν)) = ∫ w : ℝ × ℝ, w.1 ∂(μ.prod ν) :=
    integral_map measurable_fst.aemeasurable measurable_id.aestronglyMeasurable
  rw [← Measure.fst, Measure.fst_prod] at h
  exact h.symm

theorem integral_snd_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ w : ℝ × ℝ, w.2 ∂(μ.prod ν) = ∫ x, x ∂ν := by
  have h : ∫ y : ℝ, y ∂(Measure.map Prod.snd (μ.prod ν)) = ∫ w : ℝ × ℝ, w.2 ∂(μ.prod ν) :=
    integral_map measurable_snd.aemeasurable measurable_id.aestronglyMeasurable
  rw [← Measure.snd, Measure.snd_prod] at h
  exact h.symm

theorem integrable_min_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hintμ : Integrable (id : ℝ → ℝ) μ) (hsuppμ : μ (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0) :
    Integrable (fun w : ℝ × ℝ => min w.1 w.2) (μ.prod ν) := by
  refine Integrable.mono (integrable_fst_prod μ ν hintμ)
    measurable_min_pair.aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_fst_prod μ ν hsuppμ, ae_nonneg_snd_prod μ ν hsuppν] with w h1 h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min h1 h2), abs_of_nonneg h1]
  exact min_le_left _ _

theorem integrable_id_minLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hintμ : Integrable (id : ℝ → ℝ) μ) (hsuppμ : μ (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0) :
    Integrable (id : ℝ → ℝ) (minLaw μ ν) := by
  rw [minLaw]
  refine (integrable_map_measure measurable_id.aestronglyMeasurable
    measurable_min_pair.aemeasurable).mpr ?_
  exact integrable_min_prod μ ν hintμ hsuppμ hsuppν

theorem ae_nonneg_id_minLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hsuppμ : μ (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0) : 0 ≤ᵐ[minLaw μ ν] (id : ℝ → ℝ) := by
  rw [minLaw]
  refine (ae_map_iff measurable_min_pair.aemeasurable
    (measurableSet_le measurable_const measurable_id)).mpr ?_
  filter_upwards [ae_nonneg_fst_prod μ ν hsuppμ, ae_nonneg_snd_prod μ ν hsuppν] with w h1 h2
  exact le_min h1 h2

/-! ### The mean pairwise distance -/

/-- **The mean pairwise distance of two independent half-line variables.**  It is the sum of the
means minus twice the integral of the product of the survival functions, since the minimum has the
product survival function. -/
theorem integral_abs_sub_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hintμ : Integrable (id : ℝ → ℝ) μ) (hintν : Integrable (id : ℝ → ℝ) ν)
    (hsuppμ : μ (Iio 0) = 0) (hsuppν : ν (Iio 0) = 0) :
    (∫ w : ℝ × ℝ, |w.1 - w.2| ∂(μ.prod ν))
      = (∫ x, x ∂μ) + (∫ x, x ∂ν)
        - 2 * ∫ t in Ioi (0 : ℝ), survival μ t * survival ν t := by
  have hmin : ∫ w : ℝ × ℝ, min w.1 w.2 ∂(μ.prod ν)
      = ∫ t in Ioi (0 : ℝ), survival μ t * survival ν t := by
    have hmap : ∫ y : ℝ, y ∂(minLaw μ ν) = ∫ w : ℝ × ℝ, min w.1 w.2 ∂(μ.prod ν) := by
      rw [minLaw]
      exact integral_map measurable_min_pair.aemeasurable measurable_id.aestronglyMeasurable
    rw [← hmap, ← integral_survival_eq_mean (integrable_id_minLaw μ ν hintμ hsuppμ hsuppν)
      (ae_nonneg_id_minLaw μ ν hsuppμ hsuppν)]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => survival_minLaw μ ν t
  calc (∫ w : ℝ × ℝ, |w.1 - w.2| ∂(μ.prod ν))
      = ∫ w : ℝ × ℝ, (w.1 + w.2 - 2 * min w.1 w.2) ∂(μ.prod ν) :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => abs_sub_eq_add_sub_two_min _ _)
    _ = (∫ w : ℝ × ℝ, (w.1 + w.2) ∂(μ.prod ν)) - ∫ w : ℝ × ℝ, 2 * min w.1 w.2 ∂(μ.prod ν) :=
        integral_sub ((integrable_fst_prod μ ν hintμ).add (integrable_snd_prod μ ν hintν))
          ((integrable_min_prod μ ν hintμ hsuppμ hsuppν).const_mul 2)
    _ = (∫ x, x ∂μ) + (∫ x, x ∂ν)
          - 2 * ∫ t in Ioi (0 : ℝ), survival μ t * survival ν t := by
        rw [integral_add (integrable_fst_prod μ ν hintμ) (integrable_snd_prod μ ν hintν),
          integral_const_mul, integral_fst_prod, integral_snd_prod, hmin]

/-- The squared survival integral of the mean-one exponential law. -/
theorem integral_survival_sq_expMeasure_one :
    (∫ t in Ioi (0 : ℝ), survival (expMeasure 1) t * survival (expMeasure 1) t) = 1 / 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun t => Real.exp (-(2 * t))) fun t ht => ?_]
  · exact integral_exp_neg_mul_Ioi_zero (by norm_num)
  · have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [survival_expMeasure_one ht0, ← Real.exp_add]
    ring_nf

/-- **The mean pairwise distance of two independent mean-one exponential variables is one.** -/
theorem integral_abs_sub_prod_expMeasure_one :
    (∫ w : ℝ × ℝ, |w.1 - w.2| ∂((expMeasure 1).prod (expMeasure 1))) = 1 := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [integral_abs_sub_prod _ _ integrable_id_expMeasure_one integrable_id_expMeasure_one
    expMeasure_one_Iio_zero expMeasure_one_Iio_zero, integral_id_expMeasure_one,
    integral_survival_sq_expMeasure_one]
  norm_num

/-! ### Transfer along the transport distance -/

/-- The squared survival integral is continuous in the half-line transport distance. -/
theorem tendsto_integral_survival_sq {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable (id : ℝ → ℝ) (μ i)) (hsupp : ∀ i, (μ i) (Iio 0) = 0)
    (hW1 : Tendsto (fun i => halfLineW1 (μ i) (expMeasure 1)) l (𝓝 0)) :
    Tendsto (fun i => ∫ t in Ioi (0 : ℝ), survival (μ i) t * survival (μ i) t) l (𝓝 (1 / 2)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hintν : IntegrableOn (survival (expMeasure 1)) (Ioi (0 : ℝ)) :=
    integrableOn_survival integrable_id_expMeasure_one expMeasure_one_nonneg_ae
  have hnn : ∀ i, 0 ≤ᵐ[μ i] (id : ℝ → ℝ) := fun i => ae_nonneg_of_Iio_zero (hsupp i)
  have hintμ : ∀ i, IntegrableOn (survival (μ i)) (Ioi (0 : ℝ)) :=
    fun i => integrableOn_survival (hint i) (hnn i)
  have hsqInt : ∀ i, IntegrableOn (fun t => survival (μ i) t * survival (μ i) t)
      (Ioi (0 : ℝ)) := by
    intro i
    refine Integrable.mono (hintμ i) (((measurable_survival (μ i)).mul
      (measurable_survival (μ i))).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (survival_nonneg _ _),
      abs_of_nonneg (mul_nonneg (survival_nonneg _ _) (survival_nonneg _ _))]
    nlinarith [survival_nonneg (μ i) t, survival_le_one (μ i) t]
  have hsqIntν : IntegrableOn (fun t => survival (expMeasure 1) t * survival (expMeasure 1) t)
      (Ioi (0 : ℝ)) := by
    refine Integrable.mono hintν (((measurable_survival (expMeasure 1)).mul
      (measurable_survival (expMeasure 1))).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (survival_nonneg _ _),
      abs_of_nonneg (mul_nonneg (survival_nonneg _ _) (survival_nonneg _ _))]
    nlinarith [survival_nonneg (expMeasure 1) t, survival_le_one (expMeasure 1) t]
  have hdiff : ∀ i, |(∫ t in Ioi (0 : ℝ), survival (μ i) t * survival (μ i) t) - 1 / 2|
      ≤ 2 * halfLineW1 (μ i) (expMeasure 1) := by
    intro i
    rw [← integral_survival_sq_expMeasure_one, ← integral_sub (hsqInt i) hsqIntν]
    refine le_trans (abs_integral_le_integral_abs) ?_
    rw [halfLineW1, ← integral_const_mul]
    refine integral_mono_ae (((hsqInt i).sub hsqIntν).abs)
      (((hintμ i).sub hintν).abs.const_mul 2) (Filter.Eventually.of_forall fun t => ?_)
    show |survival (μ i) t * survival (μ i) t
        - survival (expMeasure 1) t * survival (expMeasure 1) t|
      ≤ 2 * |survival (μ i) t - survival (expMeasure 1) t|
    have h1 := survival_nonneg (μ i) t
    have h2 := survival_nonneg (expMeasure 1) t
    have h3 := survival_le_one (μ i) t
    have h4 := survival_le_one (expMeasure 1) t
    have hfac : survival (μ i) t * survival (μ i) t
        - survival (expMeasure 1) t * survival (expMeasure 1) t
        = (survival (μ i) t - survival (expMeasure 1) t)
          * (survival (μ i) t + survival (expMeasure 1) t) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ survival (μ i) t
      + survival (expMeasure 1) t)]
    nlinarith [abs_nonneg (survival (μ i) t - survival (expMeasure 1) t)]
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun i => 2 * halfLineW1 (μ i) (expMeasure 1))
    (fun i => dist_nonneg) (fun i => ?_) (by simpa using hW1.const_mul 2)
  rw [Real.dist_eq]
  exact hdiff i

/-- **The four-unit incidence energy of a critical clock.**  Along a family converging to the
mean-one exponential law in the half-line transport distance and in the mean, the mean pairwise
distance of two independent copies tends to one, so the four-unit energy tends to four. -/
theorem tendsto_integral_abs_sub_prod {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable (id : ℝ → ℝ) (μ i)) (hsupp : ∀ i, (μ i) (Iio 0) = 0)
    (hmean : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 1))
    (hW1 : Tendsto (fun i => halfLineW1 (μ i) (expMeasure 1)) l (𝓝 0)) :
    Tendsto (fun i => ∫ w : ℝ × ℝ, |w.1 - w.2| ∂((μ i).prod (μ i))) l (𝓝 1) := by
  have hlim := (hmean.add hmean).sub
    ((tendsto_integral_survival_sq μ hint hsupp hW1).const_mul 2)
  have hval : (1 : ℝ) + 1 - 2 * (1 / 2) = 1 := by norm_num
  rw [hval] at hlim
  refine hlim.congr fun i => ?_
  exact (integral_abs_sub_prod (μ i) (μ i) (hint i) (hint i) (hsupp i) (hsupp i)).symm

/-- **The four-unit incidence energy.** -/
theorem tendsto_four_mul_integral_abs_sub_prod {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable (id : ℝ → ℝ) (μ i)) (hsupp : ∀ i, (μ i) (Iio 0) = 0)
    (hmean : Tendsto (fun i => ∫ x, x ∂(μ i)) l (𝓝 1))
    (hW1 : Tendsto (fun i => halfLineW1 (μ i) (expMeasure 1)) l (𝓝 0)) :
    Tendsto (fun i => 4 * ∫ w : ℝ × ℝ, |w.1 - w.2| ∂((μ i).prod (μ i))) l (𝓝 4) := by
  simpa using (tendsto_integral_abs_sub_prod μ hint hsupp hmean hW1).const_mul 4

/-! ### Marginals of a product of two laws -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_comp_fst_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ w : α × β, f w.1 ∂(μ.prod ν)) = ∫ x, f x ∂μ := by
  have hmap : Measure.map Prod.fst (μ.prod ν) = μ := by
    rw [← Measure.fst, Measure.fst_prod]
  have h : ∫ x, f x ∂(Measure.map Prod.fst (μ.prod ν)) = ∫ w : α × β, f w.1 ∂(μ.prod ν) :=
    integral_map measurable_fst.aemeasurable (by rwa [hmap])
  rw [hmap] at h
  exact h.symm

theorem integral_comp_snd_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ w : α × β, f w.2 ∂(μ.prod ν)) = ∫ x, f x ∂ν := by
  have hmap : Measure.map Prod.snd (μ.prod ν) = ν := by
    rw [← Measure.snd, Measure.snd_prod]
  have h : ∫ x, f x ∂(Measure.map Prod.snd (μ.prod ν)) = ∫ w : α × β, f w.2 ∂(μ.prod ν) :=
    integral_map measurable_snd.aemeasurable (by rwa [hmap])
  rw [hmap] at h
  exact h.symm

theorem integrable_comp_fst_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Integrable f μ) :
    Integrable (fun w : α × β => f w.1) (μ.prod ν) := by
  have hmap : Measure.map Prod.fst (μ.prod ν) = μ := by
    rw [← Measure.fst, Measure.fst_prod]
  have h : Integrable f (Measure.map Prod.fst (μ.prod ν)) := by rwa [hmap]
  have hmeas : AEStronglyMeasurable f (Measure.map Prod.fst (μ.prod ν)) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  exact (integrable_map_measure hmeas measurable_fst.aemeasurable).mp h

theorem integrable_comp_snd_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : β → ℝ} (hf : Integrable f ν) :
    Integrable (fun w : α × β => f w.2) (μ.prod ν) := by
  have hmap : Measure.map Prod.snd (μ.prod ν) = ν := by
    rw [← Measure.snd, Measure.snd_prod]
  have h : Integrable f (Measure.map Prod.snd (μ.prod ν)) := by rwa [hmap]
  have hmeas : AEStronglyMeasurable f (Measure.map Prod.snd (μ.prod ν)) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  exact (integrable_map_measure hmeas measurable_snd.aemeasurable).mp h

/-! ### The gap of two independent variables -/

/-- The law of the difference of two independent variables. -/
def independentGapLaw (μ ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun w : ℝ × ℝ => w.1 - w.2) (μ.prod ν)

instance isProbabilityMeasure_independentGapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (independentGapLaw μ ν) := by
  rw [independentGapLaw]
  exact Measure.isProbabilityMeasure_map (measurable_fst.sub measurable_snd).aemeasurable

theorem integrable_abs_sub_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν) :
    Integrable (fun w : ℝ × ℝ => |w.1 - w.2|) (μ.prod ν) := by
  have h1 : Integrable (fun w : ℝ × ℝ => w.1) (μ.prod ν) := integrable_fst_prod μ ν hμ
  have h2 : Integrable (fun w : ℝ × ℝ => w.2) (μ.prod ν) := integrable_snd_prod μ ν hν
  exact (h1.sub h2).abs

theorem integral_independentGapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (independentGapLaw μ ν)) :
    (∫ x, f x ∂(independentGapLaw μ ν)) = ∫ w, f (w.1 - w.2) ∂(μ.prod ν) := by
  rw [independentGapLaw] at hf ⊢
  exact integral_map (measurable_fst.sub measurable_snd).aemeasurable hf

theorem integrable_abs_independentGapLaw (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν) :
    Integrable (fun x : ℝ => |x|) (independentGapLaw μ ν) := by
  rw [independentGapLaw]
  refine (integrable_map_measure measurable_id.abs.aestronglyMeasurable
    (measurable_fst.sub measurable_snd).aemeasurable).mpr ?_
  exact integrable_abs_sub_prod μ ν hμ hν

theorem integrable_comp_independentGap (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (independentGapLaw μ ν))
    (hint : Integrable f (independentGapLaw μ ν)) :
    Integrable (fun w : ℝ × ℝ => f (w.1 - w.2)) (μ.prod ν) := by
  rw [independentGapLaw] at hf hint
  exact (integrable_map_measure hf (measurable_fst.sub measurable_snd).aemeasurable).mp hint

/-- **The mean pairwise distance scales with the law.** -/
theorem integral_abs_sub_prod_scaleLaw {c : ℝ} (hc : 0 < c) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ w : ℝ × ℝ, |w.1 - w.2| ∂((scaleLaw c μ).prod (scaleLaw c ν)))
      = c * ∫ w : ℝ × ℝ, |w.1 - w.2| ∂(μ.prod ν) := by
  rw [scaleLaw, scaleLaw, Measure.map_prod_map μ ν (measurable_scale c) (measurable_scale c)]
  have h : ∫ w : ℝ × ℝ, |w.1 - w.2| ∂(Measure.map (Prod.map (fun x : ℝ => c * x)
        (fun x : ℝ => c * x)) (μ.prod ν))
      = ∫ w : ℝ × ℝ, |c * w.1 - c * w.2| ∂(μ.prod ν) :=
    integral_map ((measurable_scale c).prodMap (measurable_scale c)).aemeasurable
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show |c * w.1 - c * w.2| = c * |w.1 - w.2|
  rw [← mul_sub, abs_mul, abs_of_pos hc]

end

end GaloisForLFunctions.HTGeometry
