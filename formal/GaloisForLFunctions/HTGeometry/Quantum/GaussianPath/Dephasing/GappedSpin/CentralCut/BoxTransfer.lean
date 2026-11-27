import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.IncrementClock
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NonAbelianClawOnset

/-! # Passing a Gaussian increment sector to the original first clocks -/
open Set MeasureTheory Filter ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- A measurable coefficient sector with uniformly cheap increments
retains its whole Gaussian mass when passed to both first clocks. -/
theorem transfer_increment_sector :
    ∀ᶠ k : ℕ in atTop, let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      let ν := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ (E : Set (PathLabel n→ℝ)) (Q : Set (PrefixIndex n→ℝ)), MeasurableSet E → MeasurableSet Q →
      ∀ T > (0:ℝ), ∀ B : ℕ, 2*B ≤ P →
        (∀ x∈E, (fun i => x (pathCoeffEquiv n i))∈Q ∧ ∀ t : ℝ, |t| ≤ T →
          HasProjectiveCircuitApproximation (n+2) (1/100) B
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t)) →
        ν.real E ≤ μ.real {x | x∈Q ∧ T < crossingOrigin n P (9/80) x ∧
          ∀ s ≤ P/2, T < crossingWait n P s x} := by
  filter_upwards [delay_of_cheap] with k hd
  intro n P μ ν E Q hE hQ T hT B hB hinc
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hY : MeasurePreserving Y pathPauliDisorderLaw ν := measurePreserving_pathDisorder_labels n
  let F := {x | x∈Q ∧ T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x}
  have hw : MeasurableSet {x | ∀ s ≤ P/2, T < crossingWait n P s x} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_crossingWait n P s)
  have hf : MeasurableSet F := hQ.inter ((measurableSet_lt measurable_const (measurable_crossingOrigin ..)).inter hw)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [←hY.measure_preimage hE.nullMeasurableSet,←hX.measure_preimage hf.nullMeasurableSet]
  apply measure_mono_ae
  filter_upwards [hd] with ω hω
  intro he
  obtain ⟨hq,hi⟩ := hinc (Y ω) he
  exact ⟨hq,hω T hT B hB hi⟩

#print axioms transfer_increment_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
