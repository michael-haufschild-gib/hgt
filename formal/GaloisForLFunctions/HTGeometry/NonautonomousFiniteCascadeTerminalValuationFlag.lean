import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeTerminalLowerRetention

/-!
# Terminal-inward valuation refinement on the actual cascade branch

The terminal Wiman place retains the complete lower actual branch in residue.  Any valuation of
that lower branch can therefore be prolonged to the residue field and composed with the terminal
place.  This produces one genuinely compatible terminal-inward flag on the actual irreducible
branch field; no independent Puiseux-component selection is used.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

attribute [local instance] cascadeUnitCostDomain cascadeUnitCostRatFuncAlgebra
  cascadeUnitCostComplexAlgebra cascadeUnitCostScalarTower cascadeUnitCostDifferential
  cascadeUnitCostCharZero

/-- Iterating exact residue prolongation produces one valuation on the actual depth-`N` branch
under which every positive-depth cascade state is a pole.  This is the compatible nested flag
asserted in the paper; the clock coordinate is deliberately excluded because it is the base
rational variable. -/
theorem exists_nonautonomousFiniteCascadeWimanValuationFlag
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (N : ℕ)
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ A : ValuationSubring (NonautonomousFiniteCascadeBranchField hfan N),
      ∀ i : Fin (N + 1), 0 < (i : ℕ) →
        nonautonomousFiniteCascadeStateInBranchField hfan N i ∉ A := by
  induction N with
  | zero =>
      refine ⟨⊤, ?_⟩
      intro i hi
      omega
  | succ N ih =>
      obtain ⟨A, hA⟩ := ih (fun k hk => h1 k (by omega))
      obtain ⟨C, hC, hmem, hpole⟩ :=
        exists_nonautonomousFiniteCascadeTerminalWimanLowerBranchResidueEmbedding_pole
          hfan hall N h1 A
      refine ⟨C, ?_⟩
      intro i hi
      by_cases hilast : i = Fin.last (N + 1)
      · subst i
        exact hpole
      · intro hiC
        let j : Fin (N + 1) := ⟨i, by
          have hiLt := i.isLt
          have hiNe : (i : ℕ) ≠ N + 1 := by
            intro hieq
            apply hilast
            apply Fin.ext
            simpa using hieq
          omega⟩
        have hji : j.castSucc = i := by
          apply Fin.ext
          rfl
        have hjC' : nonautonomousFiniteCascadeStateInBranchField hfan N j ∈ A := by
          apply (hmem (nonautonomousFiniteCascadeStateInBranchField hfan N j)).mp
          rw [nonautonomousFiniteCascadeBranchInclusionSucc_state, hji]
          exact hiC
        exact hA j (by simpa [j] using hi) hjC'

end

end GaloisForLFunctions.HTGeometry
