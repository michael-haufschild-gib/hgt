import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.ExponentialCompiler

/-! # Long physical intervals near the actual maximum at a fixed tolerance -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
open DiagonalSynthesis (Register)
noncomputable section

/-- Outside one zero-dimensional set of tolerances on the frozen chain,
exponentially long intervals recur on which the cost stays within additive
sub-Hilbert slack of the actual maximum at that same tolerance. -/
theorem gaussian_recurrent_same_error_maximum_intervals :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ E : Set ℝ, dimH E = 0 ∧
      ∀ e ∈ Ioc (0:ℝ) (11/25), e ∉ E →
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let u := pathPauliDisorderShell ω (k+1)
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∃ G : ℝ, 0 ≤ G ∧ ∀ a : ℝ, ∃ v ∈ Icc a (a+G),
            ∀ t : ℝ, |t| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val (v+t)) →
                m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  filter_upwards [gaussian_frozen_maximum_clearance,LocalPatches.gaussian_exponential_precision_compiler]
    with ω hω hsim
  refine ⟨chainExceptional ω,dimH_exceptionalTolerances _,?_⟩
  intro e he hreg γ α hγ hγα hα
  obtain ⟨c,hc⟩ := hω e he hreg
  filter_upwards [hc,hsim c γ α hγ hγα hα.le] with k hk hs
  intro N u H
  obtain ⟨m,hmP,hm,hcoarse⟩ := hk
  exact ⟨m,hmP,hm,recurrent_floor_of_compiler H hcoarse hs⟩

#print axioms gaussian_recurrent_same_error_maximum_intervals
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
