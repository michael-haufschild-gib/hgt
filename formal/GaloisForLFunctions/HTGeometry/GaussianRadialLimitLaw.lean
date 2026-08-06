import GaloisForLFunctions.HTGeometry.GaussianRadialEndpointLaw
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Existence and uniqueness of the completed endpoint law

Every endpoint law of a Gaussian observer is supported in one fixed closed ball,
so the family is tight and, by Prokhorov's theorem, has compact closure in the
space of probability measures.  A cluster point of that family realizes the
completed-time average of every bounded continuous reporter, hence is the weak
limit of the whole family and is unique.  The continuity-set statement then holds
unconditionally.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℂ E] in
/-- The endpoint law is supported in the ball carrying the whole state curve. -/
theorem endpointLaw_compl_closedBall (m : ℕ) (Ev : ι → ℝ) (w : ι → E) (t : ℝ)
    {r : ℝ} (hr : ∑ i, ‖w i‖ ≤ r) :
    endpointLaw m Ev w t (Metric.closedBall (0 : E) r)ᶜ = 0 := by
  have hmeas : Measurable fun x : EuclideanSpace ℝ (Fin m) =>
      spectralStateCurve Ev w (t * ‖x‖) :=
    ((continuous_spectralStateCurve Ev w).comp
      (continuous_const.mul continuous_norm)).measurable
  rw [endpointLaw, Measure.map_apply hmeas measurableSet_closedBall.compl]
  convert measure_empty (μ := stdGaussian (EuclideanSpace ℝ (Fin m)))
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall,
    dist_zero_right, Set.mem_empty_iff_false, iff_false, not_not]
  exact le_trans (norm_spectralStateCurve_le Ev w (t * ‖x‖)) hr

/-- The family of endpoint laws is tight. -/
theorem isTightMeasureSet_endpointLaw (m : ℕ) (Ev : ι → ℝ) (w : ι → E) :
    IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) |
        μ ∈ Set.range fun t : ℝ => endpointProbabilityLaw m Ev w t} := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := (0 : E)) ?_
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  filter_upwards [eventually_ge_atTop (∑ i, ‖w i‖)] with r hr
  refine (iSup₂_eq_bot.mpr ?_).symm
  rintro μ ⟨ν, ⟨t, rfl⟩, rfl⟩
  exact endpointLaw_compl_closedBall m Ev w t hr

/-- **Existence of the completed endpoint law.**  There is a probability measure
realizing the completed-time average of every bounded continuous reporter. -/
theorem exists_completedEndpointLaw {m : ℕ} (hm : 0 < m) (Ev : ι → ℝ)
    (w : ι → E) :
    ∃ mulim : ProbabilityMeasure E,
      ∀ f : BoundedContinuousFunction E ℝ,
        (∫ z, f z ∂(mulim : Measure E))
          = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  set S : Set (ProbabilityMeasure E) :=
    Set.range fun t : ℝ => endpointProbabilityLaw m Ev w t with hS
  have hcompact : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_endpointLaw m Ev w)
  have hle : Filter.map (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop
      ≤ 𝓟 (closure S) := by
    refine le_principal_iff.mpr ?_
    rw [Filter.mem_map]
    filter_upwards with t
    exact subset_closure ⟨t, rfl⟩
  obtain ⟨mulim, -, hcluster⟩ := hcompact.exists_clusterPt hle
  refine ⟨mulim, fun f => ?_⟩
  have hcont : ContinuousAt (fun μ : ProbabilityMeasure E => ∫ z, f z ∂(μ : Measure E))
      mulim :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).continuousAt
  have hmapped := hcluster.map hcont Filter.tendsto_map
  have hlim : Filter.map
      (fun μ : ProbabilityMeasure E => ∫ z, f z ∂(μ : Measure E))
      (Filter.map (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop)
      ≤ 𝓝 (bohrMean fun s : ℝ => f (spectralStateCurve Ev w s)) := by
    rw [Filter.map_map]
    refine Tendsto.congr (fun t => (integral_endpointLaw m Ev w t f.continuous).symm)
      (tendsto_integral_radial_bohrMean_real hm Ev w f.continuous)
  have hcluster' := hmapped.mono hlim
  by_contra hne
  exact hcluster'.ne (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne))

/-- **Completed endpoint law, continuity-set form.**  Unconditionally, there is a
probability measure whose continuity sets have endpoint masses converging to
their limit mass. -/
theorem exists_completedEndpointLaw_tendsto_measure {m : ℕ} (hm : 0 < m)
    (Ev : ι → ℝ) (w : ι → E) :
    ∃ mulim : ProbabilityMeasure E,
      (∀ f : BoundedContinuousFunction E ℝ,
        (∫ z, f z ∂(mulim : Measure E))
          = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s))
      ∧ Tendsto (fun t : ℝ => endpointProbabilityLaw m Ev w t) atTop (𝓝 mulim)
      ∧ ∀ {A : Set E}, (mulim : Measure E) (frontier A) = 0 →
        Tendsto (fun t : ℝ => (endpointProbabilityLaw m Ev w t : Measure E) A) atTop
          (𝓝 ((mulim : Measure E) A)) := by
  obtain ⟨mulim, hmulim⟩ := exists_completedEndpointLaw hm Ev w
  refine ⟨mulim, hmulim, tendsto_endpointProbabilityLaw hm Ev w mulim hmulim,
    fun {A} hA => ?_⟩
  exact tendsto_measure_endpointLaw_of_null_frontier hm Ev w mulim hmulim hA

omit [FiniteDimensional ℂ E] in
/-- **Uniqueness of the completed endpoint law.**  Two probability measures
realizing the completed-time average of every bounded continuous reporter are
equal. -/
theorem completedEndpointLaw_unique (Ev : ι → ℝ) (w : ι → E)
    {mu nu : ProbabilityMeasure E}
    (hmu : ∀ f : BoundedContinuousFunction E ℝ,
      (∫ z, f z ∂(mu : Measure E))
        = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s))
    (hnu : ∀ f : BoundedContinuousFunction E ℝ,
      (∫ z, f z ∂(nu : Measure E))
        = bohrMean fun s : ℝ => f (spectralStateCurve Ev w s)) :
    mu = nu := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => by
    rw [hmu f, hnu f]

end

end GaloisForLFunctions.HTGeometry
