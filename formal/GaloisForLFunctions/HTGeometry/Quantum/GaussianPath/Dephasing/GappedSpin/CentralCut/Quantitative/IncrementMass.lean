import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointMass

/-! # Gaussian mass of cheap increments in a longitudinal frame -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds.SingleCut
noncomputable section

/-- A longitudinal frame with cheap increments has Gaussian mass
at least exp(−CK²)/T⁷. Every diagonal coefficient is bounded below;
the off-diagonal coordinates stay uniformly small. -/
theorem gaussian_central_increment_box :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set (PathLabel n→ℝ), 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*μ.real E ∧
        ∀ x∈E, (∀ l, IsDiagLabel l → 1/2 < x l) ∧ (∀ l, ¬IsDiagLabel l → |x l| ≤ 1/20000) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  obtain ⟨C,hC,h⟩ := gaussian_joint_central_box
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with k hk
  intro n K P μ T hT
  obtain ⟨B,E,hB,hE,hfloor,he⟩ := hk T hT
  refine ⟨B,E,hB,hE,hfloor,?_⟩
  intro x hx
  obtain ⟨hd,ho,_,hinc⟩ := he x hx
  exact ⟨hd,ho,hinc⟩

#print axioms gaussian_central_increment_box
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
