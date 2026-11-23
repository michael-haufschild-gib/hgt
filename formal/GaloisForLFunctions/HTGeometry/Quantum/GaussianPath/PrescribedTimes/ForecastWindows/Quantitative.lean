import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Intervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.EarlyTail

/-! # Absolute forecast error for the distinguished return at arbitrary dates -/
open MeasureTheory ProbabilityTheory Set Real Filter
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
open ShortWindows LocalPatches.PhysicalSpeed
noncomputable section

/-- Every finite forecast list pays one Gaussian early-arrival tail plus
its total length divided by the late-time resolution. The splitting time
can be optimized after choosing the list. -/
theorem gaussian_first_wait_forecast_price :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let m := Fintype.card (ChainLabel N)
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      ∀ B > (0:ℝ), ∀ (K : ℕ) (s : Fin K → ℕ) (t w : Fin K → ℝ),
        (∀ i, s i ≤ P/2) → (∀ i, 0 ≤ w i) →
        μ.real {x | ∃ i, crossingWait (k+1) P (s i) x ∈ Ioc (t i) (t i+w i)} ≤
          2*(m:ℝ)*exp (-(travelProduct N/B)^2/2)+1024*sqrt m*(∑ i, w i)/B := by
  filter_upwards [gaussian_early_first_passage_tail] with k hk
  intro N P m μ B hB K s t w hs hw
  apply (first_wait_forecast_union (k+1) P (P/2) s t w hs hw hB).trans
  refine add_le_add ?_ le_rfl
  let E := {x | crossingWait (k+1) P (P/2) x ≤ B}
  have hm : MeasurableSet E := measurableSet_le (measurable_crossingWait ..) measurable_const
  have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage hm.nullMeasurableSet
  change μ.real E ≤ _
  rw [←show pathPauliDisorderLaw.real (prefixPoint k ⁻¹' E) = μ.real E from he]
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  exact (measureReal_mono (fun ω hx => Or.inr ⟨P/2,le_rfl,hx⟩)).trans (hk B hB)

#print axioms gaussian_first_wait_forecast_price
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
