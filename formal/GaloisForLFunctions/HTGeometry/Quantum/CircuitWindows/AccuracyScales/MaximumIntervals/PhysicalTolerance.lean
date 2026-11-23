import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.DatedIntervals

/-! # Long intervals at a maximum for a prescribed physical accuracy -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
noncomputable section

/-- For almost every prescribed accuracy, every window of the stated
length eventually contains an actual maximizer surrounded by an
exponentially wide interval with sub-Hilbert gate deficit. -/
theorem gaussian_prescribed_maximum_intervals :
    ∃ C : ℕ, ∀ᵐ e : ℝ ∂volume, e ∈ Ioc (0:ℝ) (11/25) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∀ a : ℝ, ∃ z ∈ Icc a (a+(2:ℝ)^((2^N:ℕ)^C)),
            (∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val z) → m ≤ j) ∧
            ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (z+t)) →
                m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  obtain ⟨C,hC⟩ := gaussian_dated_same_error_maximum_intervals
  refine ⟨C,?_⟩
  filter_upwards [gaussian_prescribed_regular_tolerances] with e hreg he
  filter_upwards [hC,hreg] with ω hω hgood
  exact hω e he hgood

#print axioms gaussian_prescribed_maximum_intervals
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
