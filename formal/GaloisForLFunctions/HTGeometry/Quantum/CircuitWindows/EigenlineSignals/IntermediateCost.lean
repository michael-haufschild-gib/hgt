import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.GateFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.Temporal.IntermediateComponents.CircuitPairs

/-! # Intermediate component constraints for fitting a marked eigenphase -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section

/-- Every temporal cut must carry every input–output pair for a circuit
within a quarter of the chord of the marked eigenphase. -/
theorem marked_component_product {N : ℕ} (V : unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) {z : ℂ} (hz : ‖z‖=1) (C : TwoQubitCircuit N) (w : ℂ) (hw : ‖w‖=1)
    (hfit : 4*‖twist z (marked V r)-w • C.eval.val‖<‖1-z‖)
    (p q : ℕ) (hpq : C.gateCount=p+q) : (N-p)*(N-q)≤N := by
  by_contra! h
  obtain ⟨i,j,hij,hm⟩ := RepeatedGates.Temporal.missing_pair_of_component_product C p q hpq h
  obtain ⟨A,B,hA,hB,hU,hV,hsig⟩ := marked_chord_signal V r z hij
  let R : unitaryGroup (Fin N→Bool) ℂ := ⟨_,twist_unitary (marked_self V r) (marked_square V r) z hz⟩
  exact hfit.not_ge (hsig.trans (SpanningDensity.missing_signal_bound C R w hw A B
    (CStarRing.norm_of_mem_unitary hU).le (CStarRing.norm_of_mem_unitary hV).le (hm A B hA hB)))

/-- A single marked eigenphase in any basis requires at least
2N−2⌊√N⌋−1 gates below a quarter of its chord in error. -/
theorem marked_near_two_per_wire {N : ℕ} (V : unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) {z : ℂ} (hz : ‖z‖=1) (C : TwoQubitCircuit N) (w : ℂ) (hw : ‖w‖=1)
    (hfit : 4*‖twist z (marked V r)-w • C.eval.val‖<‖1-z‖) :
    2*N≤C.gateCount+2*Nat.sqrt N+1 := by
  let p := C.gateCount/2
  let q := C.gateCount-p
  have hpq : C.gateCount=p+q := by dsimp only [p,q]; omega
  have hd := marked_component_product V r hz C w hw hfit p q hpq
  by_contra! h
  have hk : Nat.sqrt N+1≤N-q := by dsimp only [p,q] at *; omega
  have hk' : Nat.sqrt N+1≤N-p := by dsimp only [p,q] at *; omega
  have hh := (Nat.mul_le_mul hk' hk).trans hd
  exact (Nat.lt_succ_sqrt' N).not_ge (by simpa only [pow_two] using hh)

#print axioms marked_component_product
#print axioms marked_near_two_per_wire
end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
