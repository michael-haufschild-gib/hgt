import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.PerturbedClocks.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # One-field perturbations on the unshifted clock through the first physical dip -/

open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
open SharpOccupation
noncomputable section

/-- Keep the first 9/80 crossing and the ensuing first 1/10 dip of the
original register as the first two observations. On this exact arithmetic
clock almost every terminal-field perturbation recovers its own gate law. -/
theorem gaussian_perturbed_first_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ> (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ u∈Ico 0 σ, orbitCircuitDistance H P u<9/80) ∧
        ∀ s≤P/2, ∃ v>σ, IsLeast {u | σ≤u ∧ u∈visitSet H s (1/10)} v ∧
          ∀ᵐ z : ℝ, let G := shiftedGenerator ω k z
            ∀ (b : ℕ) (ε : ℝ), ∃ p : ℝ,
              (∀ u : ℝ → ℝ, Tendsto (fun T => visitFraction G b ε (u T) (u T+T)) atTop (𝓝 p)) ∧
              Tendsto (fun M => (integerClockPrefixLaw (fun i => σ+(i:ℝ)*(v-σ)) M : Measure ℝ).real
                (visitSet G b ε)) atTop (𝓝 p) := by
  obtain ⟨_,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hfirst,gaussian_changed_field_clock] with ω hc hh
  filter_upwards [hc] with k hk
  intro N H P
  have hB : (1:ℝ)≤2^(N-10*N.sqrt) := one_le_pow₀ (by norm_num)
  obtain ⟨σ,hσ,he,hprior,_,hnext⟩ := hk
  refine ⟨σ,zero_lt_one.trans (hB.trans_lt hσ),he,hprior,fun s hs => ?_⟩
  obtain ⟨v,hv,hmin,_,_⟩ := hnext s hs
  have hstep : 1≤v-σ := by linarith only [hB,hv]
  let t (i : ℕ) := σ+(i:ℝ)*(v-σ)
  have ht (i : ℕ) : t i+1 ≤ t (i+1) := by
    dsimp only [t]
    rw [Nat.cast_add_one,add_mul,one_mul]
    linarith only [hstep]
  exact ⟨v,by linarith only [hstep],hmin,(hh k t ht).mono fun _ h => h.2⟩

#print axioms gaussian_perturbed_first_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.PerturbedClocks
