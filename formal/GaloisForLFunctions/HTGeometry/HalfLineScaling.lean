import GaloisForLFunctions.HTGeometry.SquarefreeClockLaw

/-!
# Rescaling a half-line law

The critical clocks of a Dirichlet weight are read at the thermal scale: the observed variable is
the logarithm of the integer multiplied by the escape parameter.  This file records the rescaled
law and how the three quantities the transport layer consumes — half-line support, Laplace
transform and mean — transform under it.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The law of a rescaling of a law on the line. -/
def scaleLaw (c : ℝ) (μ : Measure ℝ) : Measure ℝ := Measure.map (fun x => c * x) μ

theorem measurable_scale (c : ℝ) : Measurable fun x : ℝ => c * x :=
  measurable_id.const_mul c

instance instIsProbabilityMeasureScaleLaw (c : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (scaleLaw c μ) := by
  rw [scaleLaw]
  exact Measure.isProbabilityMeasure_map (measurable_scale c).aemeasurable

/-- A nonnegative rescaling of a half-line law is a half-line law. -/
theorem scaleLaw_Iio_zero {c : ℝ} (hc : 0 ≤ c) {μ : Measure ℝ} (hsupp : μ (Iio 0) = 0) :
    scaleLaw c μ (Iio 0) = 0 := by
  rw [scaleLaw, Measure.map_apply (measurable_scale c) measurableSet_Iio]
  refine measure_mono_null (fun x hx => ?_) hsupp
  simp only [Set.mem_preimage, Set.mem_Iio] at hx ⊢
  by_contra hcon
  exact absurd hx (not_lt.mpr (mul_nonneg hc (not_lt.mp hcon)))

/-- **Rescaling multiplies the Laplace argument.** -/
theorem integral_exp_neg_scaleLaw (c u : ℝ) (μ : Measure ℝ) :
    (∫ y, Real.exp (-(u * y)) ∂(scaleLaw c μ)) = ∫ x, Real.exp (-((u * c) * x)) ∂μ := by
  rw [scaleLaw]
  have h : ∫ (y : ℝ), Real.exp (-(u * y)) ∂(Measure.map (fun x : ℝ => c * x) μ)
      = ∫ x, Real.exp (-(u * (c * x))) ∂μ :=
    integral_map (measurable_scale c).aemeasurable
      ((Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable)
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring_nf)

/-- **Rescaling multiplies the mean.** -/
theorem integral_id_scaleLaw (c : ℝ) (μ : Measure ℝ) :
    (∫ y, y ∂(scaleLaw c μ)) = c * ∫ x, x ∂μ := by
  rw [scaleLaw]
  have h : ∫ (y : ℝ), y ∂(Measure.map (fun x : ℝ => c * x) μ) = ∫ x, c * x ∂μ :=
    integral_map (measurable_scale c).aemeasurable measurable_id.aestronglyMeasurable
  rw [h, integral_const_mul]

/-- A rescaled law with a finite mean has a finite mean. -/
theorem integrable_id_scaleLaw (c : ℝ) {μ : Measure ℝ} (hint : Integrable (id : ℝ → ℝ) μ) :
    Integrable (id : ℝ → ℝ) (scaleLaw c μ) := by
  rw [scaleLaw]
  refine (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_scale c).aemeasurable).mpr ?_
  exact (hint.const_mul c).congr (Filter.Eventually.of_forall fun x => rfl)

/-- The critical Euler clock, read at the thermal scale. -/
def scaledEulerClockLaw (σ : ℝ) : Measure ℝ := scaleLaw (σ - 1) (eulerClockLaw σ)

/-- The critical squarefree clock, read at the thermal scale. -/
def scaledSquarefreeClockLaw (σ : ℝ) : Measure ℝ := scaleLaw (σ - 1) (squarefreeClockLaw σ)

theorem isProbabilityMeasure_scaledEulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (scaledEulerClockLaw σ) := by
  haveI := isProbabilityMeasure_eulerClockLaw hσ
  exact instIsProbabilityMeasureScaleLaw _ _

theorem isProbabilityMeasure_scaledSquarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    IsProbabilityMeasure (scaledSquarefreeClockLaw σ) := by
  haveI := isProbabilityMeasure_squarefreeClockLaw hσ
  exact instIsProbabilityMeasureScaleLaw _ _

theorem scaledEulerClockLaw_Iio_zero {σ : ℝ} (hσ : 1 < σ) :
    scaledEulerClockLaw σ (Iio 0) = 0 :=
  scaleLaw_Iio_zero (by linarith) (eulerClockLaw_Iio_zero σ)

theorem scaledSquarefreeClockLaw_Iio_zero {σ : ℝ} (hσ : 1 < σ) :
    scaledSquarefreeClockLaw σ (Iio 0) = 0 :=
  scaleLaw_Iio_zero (by linarith) (squarefreeClockLaw_Iio_zero σ)

/-- **The Laplace transform of the scaled Euler clock is the moving ratio of von Mangoldt
currents.** -/
theorem integral_exp_neg_scaledEulerClockLaw {σ : ℝ} (hσ : 1 < σ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(scaledEulerClockLaw σ))
      = (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(σ + u * (σ - 1))))
        / ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) := by
  rw [scaledEulerClockLaw, integral_exp_neg_scaleLaw]
  exact integral_exp_neg_eulerClockLaw hσ (mul_nonneg hu (by linarith))

/-- **The Laplace transform of the scaled squarefree clock is the moving ratio of squarefree
Dirichlet totals.** -/
theorem integral_exp_neg_scaledSquarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(scaledSquarefreeClockLaw σ))
      = dirichletTotal squarefreeWeight (σ + u * (σ - 1))
        / dirichletTotal squarefreeWeight σ := by
  rw [scaledSquarefreeClockLaw, integral_exp_neg_scaleLaw]
  exact integral_exp_neg_squarefreeClockLaw hσ (mul_nonneg hu (by linarith))

/-- **The mean of the scaled Euler clock.** -/
theorem integral_id_scaledEulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    (∫ y, y ∂(scaledEulerClockLaw σ))
      = (σ - 1) * ((∑' n : ℕ, (Real.log n * ArithmeticFunction.vonMangoldt n) * (n : ℝ) ^ (-σ))
        / ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by
  rw [scaledEulerClockLaw, integral_id_scaleLaw, integral_id_eulerClockLaw hσ]

/-- **The mean of the scaled squarefree clock.** -/
theorem integral_id_scaledSquarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    (∫ y, y ∂(scaledSquarefreeClockLaw σ))
      = (σ - 1) * ((∑' n : ℕ, (Real.log n * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ) := by
  rw [scaledSquarefreeClockLaw, integral_id_scaleLaw, integral_id_squarefreeClockLaw hσ]

theorem integrable_id_scaledEulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    Integrable (id : ℝ → ℝ) (scaledEulerClockLaw σ) :=
  integrable_id_scaleLaw _ (integrable_id_eulerClockLaw hσ)

theorem integrable_id_scaledSquarefreeClockLaw {σ : ℝ} (hσ : 1 < σ) :
    Integrable (id : ℝ → ℝ) (scaledSquarefreeClockLaw σ) :=
  integrable_id_scaleLaw _ (integrable_id_squarefreeClockLaw hσ)

/-! ### Quantiles and couplings under rescaling -/

/-- **The distribution function of a positive rescaling.** -/
theorem cdf_scaleLaw {c : ℝ} (hc : 0 < c) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (scaleLaw c μ) x = cdf μ (x / c) := by
  haveI : IsProbabilityMeasure (scaleLaw c μ) := instIsProbabilityMeasureScaleLaw c μ
  have hpre : (fun y : ℝ => c * y) ⁻¹' (Iic x) = Iic (x / c) := by
    ext y
    simp [Set.mem_preimage, le_div_iff₀ hc, mul_comm]
  rw [cdf_eq_real, cdf_eq_real, scaleLaw, Measure.real,
    Measure.real, Measure.map_apply (measurable_scale c) measurableSet_Iic, hpre]

/-- **The quantile of a positive rescaling is the rescaled quantile.** -/
theorem quantile_scaleLaw {c : ℝ} (hc : 0 < c) (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : quantile (scaleLaw c μ) p = c * quantile μ p := by
  haveI : IsProbabilityMeasure (scaleLaw c μ) := instIsProbabilityMeasureScaleLaw c μ
  refine le_antisymm ?_ ?_
  · refine (quantile_le_iff hp0 hp1).mpr ?_
    rw [cdf_scaleLaw hc, mul_div_cancel_left₀ _ (ne_of_gt hc)]
    exact le_cdf_quantile hp0 hp1
  · refine le_csInf (quantileSet_nonempty (μ := scaleLaw c μ) hp1) fun x hx => ?_
    have hcdf : p ≤ cdf μ (x / c) := by
      rw [← cdf_scaleLaw hc]
      exact hx
    have hq : quantile μ p ≤ x / c := (quantile_le_iff hp0 hp1).mpr hcdf
    calc c * quantile μ p ≤ c * (x / c) := by
          exact mul_le_mul_of_nonneg_left hq (le_of_lt hc)
      _ = x := by field_simp

/-- **The transport cost of the monotone coupling scales with the law.** -/
theorem integral_monotoneCoupling_abs_sub_scaleLaw {c : ℝ} (hc : 0 < c) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ z, |z.1 - z.2| ∂(monotoneCoupling (scaleLaw c μ) (scaleLaw c ν)))
      = c * ∫ z, |z.1 - z.2| ∂(monotoneCoupling μ ν) := by
  haveI : IsProbabilityMeasure (scaleLaw c μ) := instIsProbabilityMeasureScaleLaw c μ
  haveI : IsProbabilityMeasure (scaleLaw c ν) := instIsProbabilityMeasureScaleLaw c ν
  rw [integral_monotoneCoupling_abs_sub, integral_monotoneCoupling_abs_sub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun p hp => ?_
  rw [quantile_scaleLaw hc μ hp.1 hp.2, quantile_scaleLaw hc ν hp.1 hp.2, ← mul_sub, abs_mul,
    abs_of_pos hc]

/-! ### Rescaling keeps the atom at the origin -/

/-- A nonzero rescaling preserves the mass at the origin. -/
theorem scaleLaw_singleton_zero {c : ℝ} (hc : c ≠ 0) (μ : Measure ℝ) :
    scaleLaw c μ {(0 : ℝ)} = μ {(0 : ℝ)} := by
  rw [scaleLaw, Measure.map_apply (measurable_scale c) (measurableSet_singleton (0 : ℝ))]
  congr 1
  ext x
  simp [Set.mem_preimage, mul_eq_zero, hc]

/-- **The two thermally scaled clocks are distinct at every finite scale.** -/
theorem scaledSquarefreeClockLaw_ne_scaledEulerClockLaw {σ : ℝ} (hσ : 1 < σ) :
    scaledSquarefreeClockLaw σ ≠ scaledEulerClockLaw σ := by
  intro hcon
  have hne : (σ : ℝ) - 1 ≠ 0 := by
    intro h
    have hone : σ = 1 := by linarith
    exact absurd hone (ne_of_gt hσ)
  have hsq : scaledSquarefreeClockLaw σ {(0 : ℝ)} = squarefreeClockLaw σ {(0 : ℝ)} := by
    rw [scaledSquarefreeClockLaw, scaleLaw_singleton_zero hne]
  have heu : scaledEulerClockLaw σ {(0 : ℝ)} = eulerClockLaw σ {(0 : ℝ)} := by
    rw [scaledEulerClockLaw, scaleLaw_singleton_zero hne]
  have hmass : squarefreeClockLaw σ {(0 : ℝ)} = eulerClockLaw σ {(0 : ℝ)} := by
    rw [← hsq, ← heu, hcon]
  have hzero : eulerClockLaw σ {(0 : ℝ)} = 0 := by
    rw [eulerClockLaw, logClockLaw_singleton_zero (by simp [eulerClockWeight])]
    simp [eulerClockWeight]
  have hpos : 0 < 1 / dirichletTotal squarefreeWeight σ :=
    div_pos one_pos (dirichletTotal_squarefreeWeight_pos hσ)
  rw [squarefreeClockLaw_singleton_zero σ, hzero] at hmass
  exact absurd hmass (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))

end

end GaloisForLFunctions.HTGeometry
