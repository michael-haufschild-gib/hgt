import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.ProbePair
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.TimeOrderedCut

/-! # Robust gate cost of changing one eigenphase, in every basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section

/-- Every short circuit misses a directed pair. A phase change on a
single eigenline therefore costs at least a quarter of its chord in
projective operator error, uniformly over the basis. -/
theorem marked_error_floor {N : ℕ} (hN : 2 ≤ N) (V : Matrix.unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) {z : ℂ} (hz : ‖z‖=1) (C : TwoQubitCircuit N)
    (hc : C.gateCount < N-1+(N-1)/2) (w : ℂ) (hw : ‖w‖=1) :
    ‖1-z‖ ≤ 4*‖twist z (marked V r)-w • C.eval.val‖ := by
  obtain ⟨i,j,hij,hcomm⟩ := RepeatedGates.missing_ordered_pair hN C hc
  obtain ⟨A,B,hs,ht,hA,hB,hsig⟩ := marked_chord_signal V r z hij
  let R : Matrix.unitaryGroup (Fin N→Bool) ℂ :=
    ⟨twist z (marked V r),twist_unitary (marked_self V r) (marked_square V r) z hz⟩
  exact hsig.trans (SpanningDensity.missing_signal_bound C R w hw A B
    (CStarRing.norm_of_mem_unitary hA).le (CStarRing.norm_of_mem_unitary hB).le (hcomm A B hs ht))

/-- The same count survives perturbations of the target, including a
change of every eigenphase by at most the available error margin. -/
theorem marked_robust_gate_count {N : ℕ} (hN : 2 ≤ N) (V : Matrix.unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) {z : ℂ} (hz : ‖z‖=1) (U : Matrix (Fin N→Bool) (Fin N→Bool) ℂ)
    (ε δ : ℝ) (hu : ‖twist z (marked V r)-U‖ ≤ δ) (hgap : 4*(ε+δ) < ‖1-z‖)
    (s : ℕ) (hs : HasProjectiveCircuitApproximation N ε s U) : N-1+(N-1)/2 ≤ s := by
  obtain ⟨w,hw,C,hC,he⟩ := hs
  by_contra! h
  have hf := marked_error_floor hN V r hz C (hC.trans_lt h) w hw
  have hh := norm_sub_le_norm_sub_add_norm_sub (twist z (marked V r)) U (w • C.eval.val)
  linarith only [hf,hh,hu,he,hgap]

#print axioms marked_error_floor
#print axioms marked_robust_gate_count
end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
