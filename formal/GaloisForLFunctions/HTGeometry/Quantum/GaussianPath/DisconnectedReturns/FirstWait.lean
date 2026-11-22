import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.ScalarStability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ElapsedExponent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ExponentTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GapSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # The sharp precision exponent through the last disconnected gate budget -/
open Matrix MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
open PrecisionReturns

/-- Every budget below N−1 has the same first-return exponent as the
empty circuit, simultaneously on each prefix and from all positive origins. -/
theorem gaussian_disconnected_first_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, 0<a → ∀ s : ℕ, s+1<N →
        Tendsto (fun ε => log (firstVisit H a s ε-a)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_gap_clock,gaussian_disconnected_scalar_return] with ω hspec hc k
  intro N H a ha s hs
  have hd : 3≤(2:ℕ)^N := (by decide : 3≤2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  obtain ⟨e,hg,hy⟩ := hspec k
  obtain ⟨A,hA,h⟩ := hc (k+1)
  have hb : s<k+1+1 := by dsimp [N] at hs; omega
  have he := exponent_of_scalar_control H e s hA (fun t ε => h t ε s hb) hg hy ha
  change Tendsto _ _ (𝓝 ((2^N-3+1:ℕ):ℝ)) at he
  rw [show 2^N-3+1=2^N-2 by omega] at he
  exact elapsed_exponent ha (by exact_mod_cast (show 0<2^N-2 by omega))
    (fun ε hε => (firstVisit_isLeast H a s hε).1.1) he

/-- The observation origin may be the actual first 9/80 crossing after
the identity. The exponent controls its elapsed wait as precision tightens. -/
theorem gaussian_disconnected_crossing_first_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ s : ℕ, s+1<N →
          Tendsto (fun ε => log (firstVisit H σ s ε-σ)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_disconnected_first_wait,LocalPatches.gaussian_first_crossing_local_width] with ω hr hw
  filter_upwards [hw] with k hk
  intro N H P
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hk
  have hpos : 0<σ := (show 0≤LocalPatches.localCrossingWidth N by
    unfold LocalPatches.localCrossingWidth; positivity).trans_lt hσ
  exact ⟨σ,hpos,he,hbefore,hr k σ hpos⟩

#print axioms gaussian_disconnected_crossing_first_wait
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
