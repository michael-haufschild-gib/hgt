import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.QuadraticSurvival
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # Joint seventh-power survival of the first excursion on strong bonds -/
open Filter MeasureTheory ProbabilityTheory Real Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds.SingleCut DiagonalSynthesis
noncomputable section

/-- At each sufficiently large fixed size, all longitudinal bonds can
exceed 1/2 while the first near-Hilbert crossing and all subsequent
half-budget first waits exceed T on Gaussian mass at least c/T⁷. -/
theorem gaussian_strong_bond_seventh_power :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∃ c > (0:ℝ), ∀ T ≥ (1:ℝ), c ≤ T^7*μ.real {x |
        (∀ e : Fin (n+1), 1/2 < x ((pathCoeffEquiv n).symm (.inr (e,(2,2))))) ∧
        T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x} := by
  obtain ⟨C,_,h⟩ := uniform_strong_bond_survival
  filter_upwards [h] with k hk
  intro n P μ
  exact ⟨exp (-C*((n+2:ℕ):ℝ)^2),exp_pos _,hk⟩

#print axioms gaussian_strong_bond_seventh_power
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
