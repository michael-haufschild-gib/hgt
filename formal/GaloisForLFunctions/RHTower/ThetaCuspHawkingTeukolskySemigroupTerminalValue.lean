import GaloisForLFunctions.HTGeometry.UniversalSpectralSemigroupWallCrossingLaw

/-!
# Semigroup terminal value of nonlinear Teukolsky returns

An integrable spectral return of a contraction semigroup has continuous Cesàro limit equal to its
zero-generator component. This remains true for infinitely many modes, damping rates accumulating
at zero, and undamped continuous spectrum. Consequently an atomless threshold spectrum cannot
supply a delay-persistent normalized counterterm at a target QNM pole.
-/

open Complex Real Set Filter Topology MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Continuous Cesàro completion of an integrable semigroup spectral return. -/
def d4BMSemigroupCesaroSpectralReturn {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (amplitude generator : α → ℂ) (duration : ℝ) : ℂ :=
  ∫ x, amplitude x * forwardWindowKernel ((duration : ℂ) * generator x) ∂mu

/-- A contractive exponential window has norm at most one. -/
theorem norm_d4BMSemigroupWindowKernel_le_one
    {duration : ℝ} (hduration : 0 ≤ duration)
    {generator : ℂ} (hgenerator : generator.re ≤ 0) :
    ‖forwardWindowKernel ((duration : ℂ) * generator)‖ ≤ 1 := by
  rcases hduration.eq_or_lt with rfl | hdurationPos
  · simp
  have hdurationNe : duration ≠ 0 := ne_of_gt hdurationPos
  rw [← forwardModeAverage_eq_kernel duration generator hdurationNe]
  unfold forwardModeAverage
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdurationPos]
  have hintegral :
      ‖∫ t : ℝ in 0..duration, Complex.exp (generator * t)‖ ≤ duration := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := duration) (C := (1 : ℝ))
      (f := fun t : ℝ => Complex.exp (generator * t)) (by
        intro t ht
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
        rw [Set.uIoc_of_le hduration] at ht
        exact mul_nonpos_of_nonpos_of_nonneg hgenerator (le_of_lt ht.1))
    simpa [abs_of_pos hdurationPos] using hbound
  rw [inv_mul_eq_div, div_le_one (by positivity)]
  exact hintegral

/-- Cesàro completion retains a mode exactly when its semigroup generator is zero. -/
theorem tendsto_d4BMSemigroupWindowKernel_atTop
    {generator : ℂ} (hgenerator : generator.re ≤ 0) :
    Tendsto
      (fun duration : ℝ =>
        forwardWindowKernel ((duration : ℂ) * generator))
      atTop (nhds (if generator = 0 then 1 else 0)) := by
  by_cases hzero : generator = 0
  · subst generator
    simp
  · rw [if_neg hzero]
    have hnorm : Tendsto
        (fun duration : ℝ => ‖((duration : ℂ) * generator)‖)
        atTop atTop := by
      have h := tendsto_id.atTop_mul_const (norm_pos_iff.mpr hzero)
      apply h.congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with duration hduration
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hduration]
      rfl
    have hre : ∀ᶠ duration : ℝ in atTop,
        (((duration : ℂ) * generator).re ≤ 0) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with duration hduration
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hduration hgenerator
    exact tendsto_forwardWindowKernel_zero_of_norm_atTop hnorm hre

/-- Terminal-value law: every nonzero contractive generator is removed, including arbitrarily
slowly damped and purely oscillatory modes. -/
theorem d4BMSemigroupCesaroSpectralReturn_tendsto_zeroGenerator
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (amplitude generator : α → ℂ)
    (hamplitude : Integrable amplitude mu)
    (hgeneratorMeasurable : Measurable generator)
    (hcontractive : ∀ᵐ x ∂mu, (generator x).re ≤ 0) :
    Tendsto (d4BMSemigroupCesaroSpectralReturn mu amplitude generator) atTop
      (nhds (∫ x in {x | generator x = 0}, amplitude x ∂mu)) := by
  have hzeroMeasurable : MeasurableSet {x | generator x = 0} :=
    hgeneratorMeasurable (measurableSet_singleton (0 : ℂ))
  have hDCT : Tendsto
      (fun duration : ℝ => ∫ x,
        amplitude x *
          forwardWindowKernel ((duration : ℂ) * generator x) ∂mu)
      atTop
      (nhds (∫ x, {x | generator x = 0}.indicator amplitude x ∂mu)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖amplitude x‖) ?_ ?_ hamplitude.norm ?_
    · filter_upwards with duration
      have hkernelMeasurable : Measurable
          (fun x => forwardWindowKernel
            ((duration : ℂ) * generator x)) :=
        continuous_forwardWindowKernel.measurable.comp
          (measurable_const.mul hgeneratorMeasurable)
      exact hamplitude.aestronglyMeasurable.mul
        hkernelMeasurable.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with duration hduration
      filter_upwards [hcontractive] with x hx
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (norm_d4BMSemigroupWindowKernel_le_one hduration hx)
    · filter_upwards [hcontractive] with x hx
      have hkernel := tendsto_d4BMSemigroupWindowKernel_atTop hx
      by_cases hzero : generator x = 0
      · simp [hzero]
      · simpa [hzero] using tendsto_const_nhds.mul hkernel
  rw [MeasureTheory.integral_indicator hzeroMeasurable] at hDCT
  change Tendsto
    (fun duration : ℝ => ∫ x,
      amplitude x * forwardWindowKernel
        ((duration : ℂ) * generator x) ∂mu)
    atTop (nhds (∫ x in {x | generator x = 0}, amplitude x ∂mu))
  exact hDCT

/-- If zero-generator spectral mass vanishes, the completed return tends to zero. -/
theorem d4BMSemigroupCesaroSpectralReturn_tendsto_zero_of_noZeroGenerator
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (amplitude generator : α → ℂ)
    (hamplitude : Integrable amplitude mu)
    (hgeneratorMeasurable : Measurable generator)
    (hcontractive : ∀ᵐ x ∂mu, (generator x).re ≤ 0)
    (hzero : mu {x | generator x = 0} = 0) :
    Tendsto (d4BMSemigroupCesaroSpectralReturn mu amplitude generator)
      atTop (nhds 0) := by
  have h := d4BMSemigroupCesaroSpectralReturn_tendsto_zeroGenerator
    mu amplitude generator hamplitude hgeneratorMeasurable hcontractive
  rw [MeasureTheory.setIntegral_measure_zero _ hzero] at h
  exact h

/-- A persistent semigroup counterterm is carried entirely by the zero-generator sector. -/
theorem d4BMSemigroupCesaroSpectralReturn_zeroGenerator_eq_of_eventually_eq
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (amplitude generator : α → ℂ)
    (hamplitude : Integrable amplitude mu)
    (hgeneratorMeasurable : Measurable generator)
    (hcontractive : ∀ᵐ x ∂mu, (generator x).re ≤ 0)
    (counterterm : ℂ)
    (hcounterterm : ∀ᶠ duration in atTop,
      d4BMSemigroupCesaroSpectralReturn mu amplitude generator duration =
        counterterm) :
    (∫ x in {x | generator x = 0}, amplitude x ∂mu) = counterterm := by
  have hterminal := d4BMSemigroupCesaroSpectralReturn_tendsto_zeroGenerator
    mu amplitude generator hamplitude hgeneratorMeasurable hcontractive
  have hconstant : Tendsto
      (d4BMSemigroupCesaroSpectralReturn mu amplitude generator)
      atTop (nhds counterterm) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hcounterterm] with duration hduration
      exact hduration.symm)
  exact tendsto_nhds_unique hterminal hconstant

/-- A nonzero persistent numerator survives arbitrary transient dynamics and any contractive
spectral return without a zero-generator component. -/
theorem eventually_d4BMPersistentTransientSemigroupNumerator_ne_zero
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) (amplitude generator : α → ℂ)
    (hamplitude : Integrable amplitude mu)
    (hgeneratorMeasurable : Measurable generator)
    (hcontractive : ∀ᵐ x ∂mu, (generator x).re ≤ 0)
    (hzero : mu {x | generator x = 0} = 0)
    (transient : ℝ → ℂ) (htransient : Tendsto transient atTop (nhds 0))
    (persistent : ℂ) (hpersistent : persistent ≠ 0) :
    ∀ᶠ duration in atTop,
      persistent + transient duration +
        d4BMSemigroupCesaroSpectralReturn
          mu amplitude generator duration ≠ 0 := by
  have hremainder : Tendsto
      (fun duration => transient duration +
        d4BMSemigroupCesaroSpectralReturn
          mu amplitude generator duration)
      atTop (nhds 0) := by
    simpa only [add_zero] using htransient.add
      (d4BMSemigroupCesaroSpectralReturn_tendsto_zero_of_noZeroGenerator
        mu amplitude generator hamplitude hgeneratorMeasurable
        hcontractive hzero)
  have hlimit : Tendsto
      (fun duration =>
        persistent + (transient duration +
          d4BMSemigroupCesaroSpectralReturn
            mu amplitude generator duration))
      atTop (nhds persistent) := by
    simpa using tendsto_const_nhds.add hremainder
  have hnonzero := hlimit.eventually (eventually_ne_nhds hpersistent)
  simpa only [add_assoc] using hnonzero

end

end RHTower
