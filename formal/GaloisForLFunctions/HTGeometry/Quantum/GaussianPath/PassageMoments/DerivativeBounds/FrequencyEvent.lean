import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.PhaseWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.PlateauConfidence.ClockBounds

/-! # A first-passage tail is supported on small balanced frequencies -/
open Set MeasureTheory ProbabilityTheory Filter
namespace GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
open SpectralJets PrescribedTimes PrescribedTimes.ResonantDraws.PlateauConfidence
noncomputable section

/-- Localizing the disorder to any measurable set preserves the comparison.
A long first excursion forces a small frequency in the finite Fourier test. -/
theorem passage_tail_on_event :
    ∀ᶠ k : ℕ in atTop, ∀ (S : Set (PrefixIndex (k+1)→ℝ)), MeasurableSet S →
      ∀ (s : ℕ) (δ : ℝ), 0<δ →
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      μ (S ∩ {x | phaseClockPrice k/δ<passageMax k s x}) ≤
        μ (S ∩ smallBalancedMode (k+3) (retainedClockModes k) δ) := by
  filter_upwards [(tendsto_add_atTop_nat 3).eventually
    eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier] with k hent
  intro S hS s δ hδ μ
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let G := phaseClockPrice k/δ
  let F := S ∩ {x | G<passageMax k s x}
  let A := S ∩ smallBalancedMode (k+3) (retainedClockModes k) δ
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law (k+1)
  have hm : MeasurableSet F := hS.inter (measurableSet_lt measurable_const (measurable_passageMax k s))
  have hs : X ⁻¹' F ≤ᵐ[pathPauliDisorderLaw] X ⁻¹' A := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω hx
    refine ⟨hx.1,Classical.byContradiction fun h => ?_⟩
    have hg := clock_bounds_first_passage k ω G hent (phase_cover_of_margin k ω hδ (hω k).injective h)
    have hmono : passageMax k s (X ω)≤passageMax k 0 (X ω) :=
      max_le_max le_rfl (crossingWait_antitone (Nat.zero_le s) _)
    exact hx.2.not_ge (hmono.trans hg)
  change μ F≤μ A
  rw [←hX.measure_preimage hm.nullMeasurableSet]
  apply (measure_mono_ae hs).trans
  simpa only [hX.map_eq] using (Measure.le_map_apply (μ:=pathPauliDisorderLaw) hX.measurable.aemeasurable A)

#print axioms passage_tail_on_event
end
end GaloisForLFunctions.HTGeometry.PassageMoments.DerivativeBounds
