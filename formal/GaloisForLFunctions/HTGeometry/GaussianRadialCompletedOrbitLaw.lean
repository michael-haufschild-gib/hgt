import GaloisForLFunctions.HTGeometry.CompletedTimeBohrMean
import GaloisForLFunctions.HTGeometry.GaussianRadialLimitLaw

/-!
# The completed endpoint law is the completed-orbit Haar law

The endpoint laws of a Gaussian observer converge weakly to the image, under the
state map, of Haar measure on the completed time.  This is the literal form of
the observer--spectral action law: the limit is the completed spectral-orbit law,
presented as a Haar measure on a compact group rather than as a mean value.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {k : Type} [Fintype k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Real form of the completed-time Haar average. -/
theorem integral_orbitClosureHaar_eq_bohrMean_real (Ev : ι → ℝ) (w : ι → E)
    (gamma : k → ℝ) (M : ι → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, -Ev i = ∑ j, (M i j : ℝ) * gamma j)
    {F : E → ℝ} (hF : Continuous F) :
    (∫ z, F (torusStateMap w z) ∂(orbitClosureHaar M : Measure (UnitAddTorus ι)))
      = bohrMean fun s : ℝ => F (spectralStateCurve Ev w s) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hcomplex := integral_orbitClosureHaar_eq_bohrMean Ev w gamma M hgamma hM
    (F := fun z => ((F z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hF)
  have hleft : (∫ z, ((F (torusStateMap w z) : ℝ) : ℂ)
        ∂(orbitClosureHaar M : Measure (UnitAddTorus ι)))
      = ((∫ z, F (torusStateMap w z)
        ∂(orbitClosureHaar M : Measure (UnitAddTorus ι)) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hap : HTGeometry.IsBohrAlmostPeriodic
      fun s : ℝ => F (spectralStateCurve Ev w s) := by
    have hK : IsCompact (Metric.closedBall (0 : E) (∑ i, ‖w i‖)) :=
      isCompact_closedBall _ _
    have hrange : ∀ t : ℝ, spectralStateCurve Ev w t
        ∈ Metric.closedBall (0 : E) (∑ i, ‖w i‖) := by
      intro t
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_spectralStateCurve_le Ev w t
    exact isBohrAlmostPeriodic_comp_of_range_subset
      (isBohrAlmostPeriodic_spectralStateCurve Ev w) hK hrange hF.continuousOn
  have hright : (bohrMean fun s : ℝ => ((F (spectralStateCurve Ev w s) : ℝ) : ℂ))
      = ((bohrMean fun s : ℝ => F (spectralStateCurve Ev w s) : ℝ) : ℂ) :=
    bohrMean_ofReal (hF.comp (continuous_spectralStateCurve Ev w)) hap
  rw [hleft, hright] at hcomplex
  exact_mod_cast hcomplex

/-- The completed-orbit law: the image of Haar measure on the completed time
under the state map. -/
def completedOrbitLaw (w : ι → E) (M : ι → k → ℤ) : ProbabilityMeasure E :=
  ProbabilityMeasure.map (orbitClosureHaar M)
    (continuous_torusStateMap w).aemeasurable

/-- **The endpoint law converges to the completed-orbit Haar law.** -/
theorem tendsto_endpointProbabilityLaw_completedOrbitLaw {m : ℕ} (hm : 0 < m)
    (Ev : ι → ℝ) (w : ι → E) (gamma : k → ℝ) (M : ι → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, -Ev i = ∑ j, (M i j : ℝ) * gamma j) :
    Tendsto (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop
      (𝓝 (completedOrbitLaw w M)) := by
  refine tendsto_endpointProbabilityLaw hm Ev w (completedOrbitLaw w M) fun f => ?_
  rw [completedOrbitLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_torusStateMap w).aemeasurable
      f.continuous.aestronglyMeasurable]
  exact integral_orbitClosureHaar_eq_bohrMean_real Ev w gamma M hgamma hM f.continuous

/-- **Completed spectral-orbit law, presentation-free form.**  Every spectral
observer has a completed-time integer presentation, and the endpoint laws
converge weakly to the image of the corresponding completed-time Haar measure
under the state map. -/
theorem exists_tendsto_endpointProbabilityLaw_completedOrbitLaw {m : ℕ} (hm : 0 < m)
    (Ev : ι → ℝ) (w : ι → E) :
    ∃ (n : ℕ) (M : ι → Fin n → ℤ),
      Tendsto (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop
        (𝓝 (completedOrbitLaw w M)) := by
  obtain ⟨n, gamma, M, A, hindep, -, -, hM, -, -⟩ :=
    exists_frequency_integer_basis fun i => -Ev i
  exact ⟨n, M, tendsto_endpointProbabilityLaw_completedOrbitLaw hm Ev w gamma M
    hindep hM⟩

end

end GaloisForLFunctions.HTGeometry
