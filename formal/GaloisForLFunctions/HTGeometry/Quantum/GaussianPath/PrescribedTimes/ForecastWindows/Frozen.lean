import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Physical
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Almost-sure exclusion of summable first-return forecasts on one infinite chain -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
open ShortWindows
noncomputable section

/-- An arbitrary prescribed family of forecast intervals eventually misses
the distinguished first waits on almost every frozen chain if their total
lengths times the square root of the dimension, divided by the travel width, are summable.
Each interval can specify a different return budget. -/
theorem gaussian_eventually_misses_first_wait_forecasts (K : ℕ→ℕ)
    (s : (k : ℕ)→Fin (K k)→ℕ) (t w : (k : ℕ)→Fin (K k)→ℝ)
    (hw : ∀ k i, 0 ≤ w k i)
    (hs : ∀ᶠ k : ℕ in atTop, ∀ i, s k i ≤ nearHilbertContinuousCircuitBudget (k+3)/2)
    (hcost : Summable fun k => 1024*sqrt (Fintype.card (ChainLabel (k+3)))*(∑ i, w k i)/forecastWidth (k+3)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∀ i,
      crossingWait (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (s k i) (prefixPoint k ω)
        ∉ Ioc (t k i) (t k i+w k i) := by
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  let B (k : ℕ) := forecastWidth (k+3)
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp [μ,pathPauliDisorderLaw]; infer_instance
  let E (k : ℕ) := {x | B k < crossingWait (k+1) (P k) (P k/2) x ∧
    ∃ i, crossingWait (k+1) (P k) (s k i) x ∈ Ioc (t k i) (t k i+w k i)}
  have hm (k) : MeasurableSet (E k) := by
    refine (measurableSet_lt measurable_const (measurable_crossingWait ..)).inter ?_
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_Ioc.preimage (measurable_crossingWait _ _ (s k i))
  let A (k : ℕ) := prefixPoint k ⁻¹' E k
  have hmass : Summable (fun k => μ.real (A k)) := by
    apply hcost.of_norm_bounded_eventually_nat
    filter_upwards [hs] with k hk
    rw [Real.norm_of_nonneg measureReal_nonneg]
    have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage (hm k).nullMeasurableSet
    change μ.real (A k) ≤ _
    rw [show μ.real (A k)=_ from he]
    exact late_forecast_union (k+1) (P k) (P k/2) (s k) (t k) (w k) hk (hw k)
      (forecastWidth_pos k)
  have hf : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉A k := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using hmass.tsum_ofReal_ne_top
  filter_upwards [hf,typical_first_wait_lower] with ω hω hh
  filter_upwards [hω,hh] with k hk hlow
  exact fun i hi => hk ⟨hlow,i,hi⟩

#print axioms gaussian_eventually_misses_first_wait_forecasts
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
