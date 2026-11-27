import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Synthesis
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.UnitaryPhases

/-! # Linear gate cap near a separated computational diagonal -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
open CommutatorBounds
noncomputable section

/-- A commuting unitary at a perturbed diagonal generator admits the
full-register linear phase budget at the same spacing-controlled error. -/
theorem commuting_gate_cap {n : ℕ} (hn : 2 ≤ n) (H U : Register n) (hU : U∈unitary (Register n))
    (hc : H*U=U*H) (d : Config n → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) :
    HasProjectiveCircuitApproximation n (4*sqrt packConstant/g*‖H-diagonal (fun i => (d i:ℂ))‖)
      (2^n*3) U := by
  obtain ⟨v,hv,_,he⟩ := commuting_diagonal_approximation H U hU hc d hg hsep
  obtain ⟨z,hz,C,hC,hfit⟩ := full_register_phases hn v hv
  exact ⟨z,hz,C,hC,hfit ▸ he⟩

theorem all_time_gate_cap {n : ℕ} (hn : 2 ≤ n) (H : selfAdjoint (Register n))
    (d : Config n → ℝ) {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (t : ℝ) :
    HasProjectiveCircuitApproximation n (4*sqrt packConstant/g*‖H.val-diagonal (fun i => (d i:ℂ))‖)
      (2^n*3) (unitaryEvolution H.val t) :=
  commuting_gate_cap hn H.val _ (unitaryEvolution_mem_unitary H.property t)
    (unitaryEvolution_commutes_generator H.val t) d hg hsep

#print axioms all_time_gate_cap
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
