import GaloisForLFunctions.HTGeometry.ExponentialCompactification
import GaloisForLFunctions.HTGeometry.QuantileCoupling

/-!
# Laplace continuity on the half line

Convergence of the Laplace transforms of half-line laws at every natural argument forces pointwise
convergence of their distribution functions to that of the mean-one exponential law.

The exponential substitution carries the tail `(-∞,t]` of a half-line law to the upper set
`{y ≥ e^{-t}}` of the compactified law, whose frontier is a single point.  Since the exponential
law has no atoms, the portmanteau theorem converts the weak convergence of the compactified laws
into convergence of the tails, hence of the distribution functions.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The mean-one exponential law has no atoms. -/
theorem expMeasure_one_singleton (t : ℝ) : (expMeasure 1) {t} = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton t),
    Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]

/-- The compactified image of a tail of the half line. -/
def expTailSet (t : ℝ) : Set (Icc (0 : ℝ) 1) := Subtype.val ⁻¹' Ici (Real.exp (-t))

theorem measurableSet_expTailSet (t : ℝ) : MeasurableSet (expTailSet t) :=
  measurable_subtype_coe measurableSet_Ici

theorem ae_nonneg_of_Iio_zero {μ : Measure ℝ} (hsupp : μ (Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  refine MeasureTheory.ae_iff.mpr ?_
  have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = Iio (0 : ℝ) := by
    ext x
    simp
  rwa [hset]

theorem preimage_expTailSet_ae (μ : Measure ℝ) (hsupp : μ (Iio 0) = 0) (t : ℝ) :
    (expProj ⁻¹' expTailSet t : Set ℝ) =ᵐ[μ] Iic t := by
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [ae_nonneg_of_Iio_zero hsupp] with x hx
  simp only [Set.mem_preimage, expTailSet, Set.mem_Ici, Set.mem_Iic]
  rw [coe_expProj_of_nonneg hx, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem expPush_expTailSet (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (t : ℝ) : (expPush μ) (expTailSet t) = μ (Iic t) := by
  rw [expPush, Measure.map_apply measurable_expProj (measurableSet_expTailSet t)]
  exact measure_congr (preimage_expTailSet_ae μ hsupp t)

theorem frontier_expTailSet_subset (t : ℝ) :
    frontier (expTailSet t) ⊆ Subtype.val ⁻¹' {Real.exp (-t)} := by
  refine (continuous_subtype_val.frontier_preimage_subset _).trans ?_
  rw [frontier_Ici]

/-- The compactified exponential law gives no mass to the boundary of a compactified tail. -/
theorem expPush_frontier_expTailSet (t : ℝ) :
    (expPush (expMeasure 1)) (frontier (expTailSet t)) = 0 := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hmeas : MeasurableSet (Subtype.val ⁻¹' {Real.exp (-t)} : Set (Icc (0 : ℝ) 1)) :=
    measurable_subtype_coe (measurableSet_singleton _)
  have hval : (expPush (expMeasure 1)) (Subtype.val ⁻¹' {Real.exp (-t)}) = 0 := by
    rw [expPush, Measure.map_apply measurable_expProj hmeas]
    have hae : (expProj ⁻¹' (Subtype.val ⁻¹' {Real.exp (-t)}) : Set ℝ)
        =ᵐ[expMeasure 1] ({t} : Set ℝ) := by
      refine Filter.eventuallyEq_set.mpr ?_
      filter_upwards [ae_nonneg_of_Iio_zero expMeasure_one_Iio_zero] with x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [coe_expProj_of_nonneg hx]
      constructor
      · intro h
        exact neg_inj.mp (Real.exp_injective h)
      · rintro rfl
        rfl
    rw [measure_congr hae]
    exact expMeasure_one_singleton t
  exact measure_mono_null (frontier_expTailSet_subset t) hval

/-- **Laplace continuity on the half line.**  Convergence of the Laplace transforms at every
natural argument forces pointwise convergence of the distribution functions to that of the mean-one
exponential law. -/
theorem tendsto_cdf_expMeasure_one_of_tendsto_laplace {ι : Type*} {l : Filter ι}
    (μs : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0)
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (∫ x, Real.exp (-((k : ℝ) * x)) ∂(expMeasure 1)))) (t : ℝ) :
    Tendsto (fun i => cdf (μs i) t) l (𝓝 (cdf (expMeasure 1) t)) := by
  haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hweak := tendsto_expPushProb_of_tendsto_laplace μs (expMeasure 1) hsupp
    expMeasure_one_Iio_zero hlap
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μ := expPushProb (expMeasure 1)) (μs := fun i => expPushProb (μs i)) hweak
    (E := expTailSet t) (by simpa using expPush_frontier_expTailSet t)
  simp only [expPushProb_toMeasure] at hport
  rw [expPush_expTailSet (expMeasure 1) expMeasure_one_Iio_zero t] at hport
  have hport' : Tendsto (fun i => (μs i) (Iic t)) l (𝓝 ((expMeasure 1) (Iic t))) := by
    refine hport.congr fun i => ?_
    exact expPush_expTailSet (μs i) (hsupp i) t
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (expMeasure 1) (Iic t))).comp hport'
  have hcdf : cdf (expMeasure 1) t = ((expMeasure 1) (Iic t)).toReal := by
    rw [cdf_eq_real, Measure.real]
  rw [hcdf]
  refine hreal.congr fun i => ?_
  simp [cdf_eq_real, Measure.real]

/-- **Critical transport from Laplace and moment convergence.**  Half-line laws whose Laplace
transforms converge at every natural argument to those of the mean-one exponential law, and whose
means converge to one, have monotone couplings with vanishing transport cost. -/
theorem tendsto_integral_monotoneCoupling_of_tendsto_laplace {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μs : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hsupp : ∀ i, (μs i) (Iio 0) = 0) (hint : ∀ i, Integrable (id : ℝ → ℝ) (μs i))
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∫ x, Real.exp (-((k : ℝ) * x)) ∂(μs i)) l
      (𝓝 (∫ x, Real.exp (-((k : ℝ) * x)) ∂(expMeasure 1))))
    (hmean : Tendsto (fun i => ∫ x, x ∂(μs i)) l (𝓝 1)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (μs i) (expMeasure 1))) l (𝓝 0) :=
  tendsto_integral_monotoneCoupling_expMeasure_one μs hsupp hint
    (tendsto_cdf_expMeasure_one_of_tendsto_laplace μs hsupp hlap) hmean

end

end GaloisForLFunctions.HTGeometry
