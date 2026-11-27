import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.Passages.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Passages.Terminal

/-! # Last above-sweep crossing before the original first low return -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks PrecisionReturns SharpOccupation
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K→Bool) (Fin K→Bool) ℂ

/-- The last above-sweep crossing before the first low return and the first
crossing after it bound one maximal open interval below 9/80. Both elapsed
times satisfy the same budget-dependent estimates. Starting at the last
crossing selects the original return. -/
theorem gaussian_coherent_terminal_descent :
    ∃ b>(0:ℝ), ∃ D>(0:ℝ), ∃ L>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let N : ℝ := (k+2:ℕ)
      let H : selfAdjoint (Reg K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      ∃ σ>0, orbitCircuitDistance H P σ=9/80 ∧ (∀ w∈Ico 0 σ, orbitCircuitDistance H P w<9/80) ∧
        ∀ r q : ℕ, let m : ℝ := (2*r+q:ℕ)
          m≤b*N → let v := firstVisit H σ r (1/10)
          let f := orbitCircuitDistance H (k+2+(r+q))
          ∃ a z : ℝ, σ≤a ∧ a<v ∧ v<z ∧ f a=9/80 ∧ f z=9/80 ∧
            (∀ w∈Ioo a z, f w<9/80) ∧ firstVisit H a r (1/10)=v ∧
            ∀ x∈({v-a,z-v} : Set ℝ), L≤(K:ℝ)*x^2 ∧
              x^4≤ max ((D/N^9)^(4/49:ℝ)) (m/(b*N)) := by
  obtain ⟨b,hb,D,hD,L,hL,hw⟩ := gaussian_coherent_first_passage
  refine ⟨b,hb,D,hD,L,hL,?_⟩
  apply terminal_descent_of_passages (p:=4) (fun n m => max ((D/((n+1:ℕ):ℝ)^9)^(4/49:ℝ)) (m/(b*((n+1:ℕ):ℝ)))) hL
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro N H v r q m hm hv
  exact hn v r q hm hv (9/80) ⟨le_rfl,by norm_num⟩

#print axioms gaussian_coherent_terminal_descent
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
