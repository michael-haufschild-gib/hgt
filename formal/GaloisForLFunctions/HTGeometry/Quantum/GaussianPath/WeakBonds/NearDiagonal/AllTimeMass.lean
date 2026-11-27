import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.GaussianSector

/-! # Gaussian mass of an all-time gate cap with every laboratory coefficient strong -/

open Set Finset Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open Dephasing.GappedSpin.CentralCut AccuracyScales.TenthPlateau PrescribedTimes
noncomputable section

/-- At every positive error through one, a measurable sector of the
physical Gaussian law has the diagonal gate cap for the entire orbit.
Only the ten off-diagonal coordinates per added site pay for precision. -/
theorem all_strong_all_time_mass :
    ∃ C > (0:ℝ), ∀ n : ℕ,
      let K := n+2
      let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ ε ∈ Set.Ioc (0:ℝ) 1, ∃ E : Set (PathLabel n → ℝ), MeasurableSet E ∧
        ε^(10*n+12)*exp (-C*(K:ℝ)^2) ≤ μ.real E ∧
        ∀ x ∈ E, (fun i => x (pathCoeffEquiv n i)) ∈ allCoordStrongEvent n (1/100) ∧
          ∀ t : ℝ, HasProjectiveCircuitApproximation K ε (2^K*(2*K+1))
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  obtain ⟨C,hC,h⟩ := linear_cap_gaussian_sector
  refine ⟨C,hC,?_⟩
  intro n K μ ε hε
  obtain ⟨E,hE,hm,hw⟩ := h n ε hε
  refine ⟨E,hE,hm,?_⟩
  intro x hx
  obtain ⟨hstrong,hcap⟩ := hw x hx
  refine ⟨hstrong,?_⟩
  intro t
  obtain ⟨z,hz,Cir,hCir,hfit⟩ := hcap t
  exact ⟨z,hz,Cir,hCir.trans (Nat.mul_le_mul_left _ (by dsimp only [K]; omega)),hfit⟩

#print axioms all_strong_all_time_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
