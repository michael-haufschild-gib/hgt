import GaloisForLFunctions.BiScaleUncertainty.CausalExponentialResponseAndLaplaceEnergy
import GaloisForLFunctions.HTGeometry.LinearSystems.StateSpaceBlockPropagation

/-!
# One-state Hankel realization of the prime-polar response beyond its cutoff

After all source terms have entered, the causal exponential response retains
only its cutoff value. Every sampled tail is a one-state realization. Hence
all rectangular Hankel blocks of that tail have rank at most one, uniformly
in the arithmetic cutoff and the number of observations.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar _root_.HTGeometry

noncomputable section

/-- Samples of the response after its arithmetic source cutoff. -/
def sampledCausalTail (N : ℕ) (h : ℝ≥0) (k : ℕ) : ℝ :=
  causalResponse N (cutoff N + (k : ℝ) * h)

/-- All arithmetic history is stored in the single cutoff amplitude. -/
theorem sampledCausalTail_eq_geometric (N : ℕ) (h : ℝ≥0) (k : ℕ) :
    sampledCausalTail N h k =
      causalResponse N (cutoff N) * Real.exp (-(h : ℝ) / 2) ^ k := by
  unfold sampledCausalTail
  rw [causalResponse_tail N (le_add_of_nonneg_right (by positivity : 0 ≤ (k : ℝ) * h))]
  rw [← Real.exp_nat_mul]
  rw [show -(cutoff N + (k : ℝ) * h - cutoff N) / 2 =
    (k : ℝ) * (-(h : ℝ) / 2) by ring]
  exact mul_comm _ _

/-- The tail is a literal one-state response, not merely a rank estimate. -/
theorem sampledCausalTail_eq_stateSpace (N : ℕ) (h : ℝ≥0) :
    sampledCausalTail N h = algebraicStateSpaceResponse
      (Matrix.diagonal (fun _ : Fin 1 => Real.exp (-(h : ℝ) / 2)))
      (fun _ => causalResponse N (cutoff N)) (fun _ => 1) := by
  funext k
  rw [algebraicStateSpaceResponse_diagonal_eq_finiteModalSequence,
    sampledCausalTail_eq_geometric]
  simp [finiteModalSequence]

/-- Every rectangular tail Hankel block has rank at most one. -/
theorem rank_sampledCausalTail_hankel_le_one (N : ℕ) (h : ℝ≥0) (p q : ℕ) :
    (fun (i : Fin p) (j : Fin q) => sampledCausalTail N h (i.val + j.val) :
      Matrix (Fin p) (Fin q) ℝ).rank ≤ 1 := by
  rw [sampledCausalTail_eq_stateSpace]
  exact rank_stateSpacePastFuture_le _ _ _ p q

/-- The first oversized tail Hankel determinant vanishes exactly. -/
theorem det_sampledCausalTail_hankel_two (N : ℕ) (h : ℝ≥0) :
    (algebraicHankelMatrix (sampledCausalTail N h) 2).det = 0 := by
  rw [sampledCausalTail_eq_stateSpace]
  exact det_algebraicHankelMatrix_stateSpaceResponse_succ_eq_zero _ _ _

/-- Advancing the observation origin multiplies the whole tail by one decay factor. -/
theorem sampledCausalTail_add (N : ℕ) (h : ℝ≥0) (k l : ℕ) :
    sampledCausalTail N h (k + l) =
      Real.exp (-(h : ℝ) / 2) ^ l * sampledCausalTail N h k := by
  rw [sampledCausalTail_eq_geometric, sampledCausalTail_eq_geometric, pow_add]
  ring

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_eq_geometric
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_eq_stateSpace
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.rank_sampledCausalTail_hankel_le_one
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.det_sampledCausalTail_hankel_two
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_add
