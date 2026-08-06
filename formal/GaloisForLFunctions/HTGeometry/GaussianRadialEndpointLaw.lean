import GaloisForLFunctions.HTGeometry.GaussianRadialContinuousReporter
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The Gaussian endpoint law and its continuity-set limit

The endpoint law of a Gaussian observer at observation time `t` is the pushforward
of the standard Gaussian along the radial evolution of the state curve.  The
radial completion law says that every bounded continuous reporter has convergent
averages, so the endpoint laws converge weakly to any probability measure
realizing the completed-time Haar average; the portmanteau theorem then converts
this into convergence of the mass of every continuity set.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section RealReporter

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Radial completion law, real form.** -/
theorem tendsto_integral_radial_bohrMean_real {m : ℕ} (hm : 0 < m)
    (Ev : ι → ℝ) (w : ι → E) {F : E → ℝ} (hF : Continuous F) :
    Tendsto
      (fun time : ℝ => ∫ x, F (spectralStateCurve Ev w (time * ‖x‖))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (bohrMean fun s : ℝ => F (spectralStateCurve Ev w s))) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hcurve := continuous_spectralStateCurve Ev w
  have hcomplex := tendsto_integral_radial_bohrMean_continuous_reporter (m := m) hm
    Ev w (F := fun z => ((F z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hF)
  have hint : ∀ time : ℝ,
      (∫ x, ((F (spectralStateCurve Ev w (time * ‖x‖)) : ℝ) : ℂ)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
        = ((∫ x, F (spectralStateCurve Ev w (time * ‖x‖))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) : ℝ) : ℂ) := by
    intro time
    exact integral_complex_ofReal
      (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
      (f := fun x => F (spectralStateCurve Ev w (time * ‖x‖)))
  have hmean : (bohrMean fun s : ℝ => ((F (spectralStateCurve Ev w s) : ℝ) : ℂ))
      = ((bohrMean fun s : ℝ => F (spectralStateCurve Ev w s) : ℝ) : ℂ) := by
    refine bohrMean_ofReal (hF.comp hcurve) ?_
    have hK : IsCompact (Metric.closedBall (0 : E) (∑ i, ‖w i‖)) :=
      isCompact_closedBall _ _
    have hrange : ∀ t : ℝ, spectralStateCurve Ev w t
        ∈ Metric.closedBall (0 : E) (∑ i, ‖w i‖) := by
      intro t
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_spectralStateCurve_le Ev w t
    exact isBohrAlmostPeriodic_comp_of_range_subset
      (isBohrAlmostPeriodic_spectralStateCurve Ev w) hK hrange hF.continuousOn
  simp only [hint, hmean] at hcomplex
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp hcomplex

end RealReporter

section EndpointLaw

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]

/-- The endpoint law of the Gaussian observer at observation time `t`. -/
def endpointLaw (m : ℕ) (Ev : ι → ℝ) (w : ι → E) (t : ℝ) : Measure E :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map
    fun x => spectralStateCurve Ev w (t * ‖x‖)

instance isProbabilityMeasure_endpointLaw (m : ℕ) (Ev : ι → ℝ) (w : ι → E)
    (t : ℝ) : IsProbabilityMeasure (endpointLaw m Ev w t) :=
  Measure.isProbabilityMeasure_map
    (((continuous_spectralStateCurve Ev w).comp
      (continuous_const.mul continuous_norm)).measurable.aemeasurable)

/-- The endpoint law as a probability measure. -/
def endpointProbabilityLaw (m : ℕ) (Ev : ι → ℝ) (w : ι → E) (t : ℝ) :
    ProbabilityMeasure E :=
  ⟨endpointLaw m Ev w t, isProbabilityMeasure_endpointLaw m Ev w t⟩

omit [FiniteDimensional ℂ E] in
theorem integral_endpointLaw (m : ℕ) (Ev : ι → ℝ) (w : ι → E) (t : ℝ)
    {F : E → ℝ} (hF : Continuous F) :
    (∫ z, F z ∂(endpointLaw m Ev w t))
      = ∫ x, F (spectralStateCurve Ev w (t * ‖x‖))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  rw [endpointLaw]
  exact integral_map
    (φ := fun x : EuclideanSpace ℝ (Fin m) => spectralStateCurve Ev w (t * ‖x‖))
    (((continuous_spectralStateCurve Ev w).comp
      (continuous_const.mul continuous_norm)).measurable.aemeasurable)
    hF.aestronglyMeasurable

/-- **Weak convergence of the endpoint laws.**  Any probability measure realizing
the completed-time Haar average of every bounded continuous reporter is the weak
limit of the endpoint laws. -/
theorem tendsto_endpointProbabilityLaw {m : ℕ} (hm : 0 < m) (Ev : ι → ℝ)
    (w : ι → E) (mulim : ProbabilityMeasure E)
    (hmulim : ∀ f : BoundedContinuousFunction E ℝ,
      (∫ z, f z ∂(mulim : Measure E))
        = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s)) :
    Tendsto (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop (𝓝 mulim) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f => ?_
  have hcoe : ∀ t : ℝ,
      (∫ z, f z ∂((endpointProbabilityLaw m Ev w t : ProbabilityMeasure E) :
        Measure E))
        = ∫ x, f (spectralStateCurve Ev w (t * ‖x‖))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    intro t
    exact integral_endpointLaw m Ev w t f.continuous
  rw [hmulim f]
  exact Tendsto.congr (fun t => (hcoe t).symm)
    (tendsto_integral_radial_bohrMean_real hm Ev w f.continuous)

/-- **Continuity-set limit.**  For a Borel target whose frontier is null for the
limit law, the endpoint mass converges to the limit mass. -/
theorem tendsto_measure_endpointLaw_of_null_frontier {m : ℕ} (hm : 0 < m)
    (Ev : ι → ℝ) (w : ι → E) (mulim : ProbabilityMeasure E)
    (hmulim : ∀ f : BoundedContinuousFunction E ℝ,
      (∫ z, f z ∂(mulim : Measure E))
        = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s))
    {A : Set E} (hA : (mulim : Measure E) (frontier A) = 0) :
    Tendsto (fun t : ℝ => (endpointProbabilityLaw m Ev w t : Measure E) A) atTop
      (𝓝 ((mulim : Measure E) A)) := by
  refine ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ?_ hA
  exact tendsto_endpointProbabilityLaw hm Ev w mulim hmulim

end EndpointLaw

end

end GaloisForLFunctions.HTGeometry
