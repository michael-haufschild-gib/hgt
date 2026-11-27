import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations.FullSupport.PairSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.IntermediateComponents.CircuitPairs
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho

/-! # Fixed-error gate price of a rotation with maximal pair signals -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FullPauliRotation
noncomputable section

/-- Even the maximal commutator norm in every ordered direction is
compatible with two gates per wire asymptotically. Every fit below error
one half must carry every signal through the middle of its gate list. -/
theorem parity_gate_price {n : ℕ} (hn : 2≤n) :
    HasProjectiveCircuitApproximation n 0 (2*n+1) (parityRotation n) ∧
    ∀ ε : ℝ, ε<1/2 → ∀ s : ℕ, HasProjectiveCircuitApproximation n ε s (parityRotation n) →
      2*n≤ s+2*Nat.sqrt n+1 := by
  obtain ⟨z,hz,C,hC,hfit⟩ := exact_synthesis hn
  refine ⟨⟨z,hz,C,hC,by rw [hfit,sub_self,norm_zero]⟩,?_⟩
  obtain ⟨X,hX,hsig⟩ := maximal_pair_signals n
  let U : Matrix.unitaryGroup (Fin n→Bool) ℂ :=
    ⟨parityRotation n,unitaryEvolution_mem_unitary (finitePauliMatrix_isHermitian _).isSelfAdjoint _⟩
  intro ε hε s ⟨z,hz,C,hC,he⟩
  let p := C.gateCount/2
  let q := C.gateCount-p
  have hpq : C.gateCount=p+q := by dsimp only [p,q]; omega
  by_contra! h
  have hp : Nat.sqrt n+1≤n-p := by dsimp only [p]; omega
  have hq : Nat.sqrt n+1≤n-q := by dsimp only [p,q]; omega
  have hcut : n<(n-p)*(n-q) := (Nat.lt_succ_sqrt' n).trans_le
    (by simpa only [pow_two] using Nat.mul_le_mul hp hq)
  obtain ⟨i,j,hij,hm⟩ := RepeatedGates.Temporal.missing_pair_of_component_product C p q hpq hcut
  have hdist := SpanningDensity.missing_signal_bound C U z hz (X i) (X j)
    (CStarRing.norm_of_mem_unitary (hX i).2).le (CStarRing.norm_of_mem_unitary (hX j).2).le
    (hm _ _ (hX i).1 (hX j).1)
  change ‖_*X j-X j* _‖≤4*‖parityRotation n-z • C.eval.val‖ at hdist
  rw [hsig i j hij] at hdist
  linarith only [hdist,he,hε]

#print axioms parity_gate_price
end
end GaloisForLFunctions.HTGeometry.FullPauliRotation
