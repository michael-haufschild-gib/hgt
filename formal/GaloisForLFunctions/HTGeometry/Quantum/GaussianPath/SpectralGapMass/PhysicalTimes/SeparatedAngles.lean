import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.UniformCounts
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.SeparatedBins

/-! # Separated physical eigenphases throughout bounded positive times -/
open MeasureTheory Matrix Filter Set
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open ClockSpectrum
noncomputable section

/-- Seventeen small disjoint neighborhoods contain actual eigenphases,
uniformly in the observation date. The chosen phases have pairwise
chord distance greater than twice the physical tolerance. -/
theorem gaussian_seventeen_phases :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0 < a →
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc a T,
        ∃ f : Fin 17 → (Fin (n+2) → Bool), ∀ i j, i ≠ j →
          (21/100:ℝ) ≤ ‖expTurns (physicalTurns (pathPauliDisorderShell ω n) t (f i))-
            expTurns (physicalTurns (pathPauliDisorderShell ω n) t (f j))‖ := by
  filter_upwards [gaussian_uniform_phase_counts] with ω hω
  intro a T ha
  filter_upwards [hω a T ha 17408 (by decide) (1/(4*17408)) (by norm_num)] with n hn
  intro t ht
  exact seventeen_phases_of_cdf _ (D:=(2:ℝ)^(n+2)) (by positivity) (hn t ht)

#print axioms gaussian_seventeen_phases
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
