import GaloisForLFunctions.BiScaleUncertainty.CausalExponentialResponseAndLaplaceEnergy
import GaloisForLFunctions.HTGeometry.LinearSystems.StateSpaceBlockPropagation
import GaloisForLFunctions.HTGeometry.TranscendentalExpOne

/-!
# One-state Hankel realization of the prime-polar response beyond its cutoff

After all source terms have entered, the causal exponential response retains
only its cutoff value. Every sampled tail is a one-state realization.
Transcendence of `e` proves this state never vanishes: every nonempty
rectangular tail Hankel block has rank exactly one, uniformly in the
arithmetic cutoff and the number of observations.
-/

open MeasureTheory
open scoped BigOperators Matrix NNReal

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar _root_.HTGeometry

noncomputable section

/-- A vanishing boundary amplitude would make a positive integral power of `e`
rational, through the identity `ψ(n) = log(lcm(1,…,n))`. -/
theorem causalResponse_cutoff_ne_zero (N : ℕ) : causalResponse N (cutoff N) ≠ 0 := by
  intro hz
  have hn : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  rw [causalResponse_eq_on_window N (cutoff_nonneg N) le_rfl] at hz
  unfold normalizedLogError logError at hz
  rw [show Real.exp (cutoff N) = ((N + 2 : ℕ) : ℝ) from
    Real.exp_log hn] at hz
  have hprod : Real.exp (-cutoff N / 2) *
      (Chebyshev.psi ((N + 2 : ℕ) : ℝ) - ((N + 2 : ℕ) : ℝ) + 1 - cutoff N) = 0 := by
    linear_combination hz
  have hzero := (mul_eq_zero.mp hprod).resolve_left (Real.exp_ne_zero _)
  have hlog : Real.log ((Nat.lcmUpto (N + 2) : ℕ) : ℝ) =
      ((N + 1 : ℕ) : ℝ) + Real.log ((N + 2 : ℕ) : ℝ) := by
    rw [← Chebyshev.psi_eq_log_lcmUpto]
    change Chebyshev.psi ((N + 2 : ℕ) : ℝ) - ((N + 2 : ℕ) : ℝ) + 1 -
      Real.log ((N + 2 : ℕ) : ℝ) = 0 at hzero
    push_cast at hzero ⊢
    linarith only [hzero]
  have hlcm : (0 : ℝ) < ((Nat.lcmUpto (N + 2) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.lcmUpto_pos _)
  have he := congrArg Real.exp hlog
  rw [Real.exp_log hlcm, Real.exp_add, Real.exp_log hn] at he
  have hpow : Real.exp 1 ^ (N + 1) =
      ((Nat.lcmUpto (N + 2) : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
    exact (eq_div_iff hn.ne').mpr he.symm
  apply (GaloisForLFunctions.HTGeometry.transcendental_exp_one.pow (Nat.succ_pos N))
  rw [hpow]
  simpa only [map_div₀, map_natCast] using
    (isAlgebraic_algebraMap (R := ℚ) (A := ℝ)
      ((Nat.lcmUpto (N + 2) : ℚ) / ((N + 2 : ℕ) : ℚ)))

/-- The retained tail always carries strictly positive energy. -/
theorem causalResponse_cutoff_sq_pos (N : ℕ) : 0 < causalResponse N (cutoff N) ^ 2 :=
  sq_pos_of_ne_zero (causalResponse_cutoff_ne_zero N)

/-- Dropping the post-cutoff state strictly underestimates the full Laplace energy. -/
theorem causalWindowEnergy_lt_laplaceEnergy (N : ℕ) :
    (∫ t in Set.Icc 0 (cutoff N),
      (normalizedLogError t + (1 - t) * Real.exp (-t / 2)) ^ 2) < laplaceEnergy N := by
  rw [← integral_sq_causalResponse_eq_laplaceEnergy, integral_sq_causalResponse_eq_window_add_tail]
  exact lt_add_of_pos_right _ (causalResponse_cutoff_sq_pos N)

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

/-- No sample of the post-cutoff tail vanishes. -/
theorem sampledCausalTail_ne_zero (N : ℕ) (h : ℝ≥0) (k : ℕ) :
    sampledCausalTail N h k ≠ 0 := by
  rw [sampledCausalTail_eq_geometric]
  exact mul_ne_zero (causalResponse_cutoff_ne_zero N) (pow_ne_zero _ (Real.exp_ne_zero _))

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
    Matrix.rank (fun (i : Fin p) (j : Fin q) => sampledCausalTail N h (i.val + j.val)) ≤ 1 := by
  rw [sampledCausalTail_eq_stateSpace]
  exact rank_stateSpacePastFuture_le _ _ _ p q

/-- Every nonempty rectangular tail window requires exactly one state. -/
theorem rank_sampledCausalTail_hankel_eq_one (N : ℕ) (h : ℝ≥0) (p q : ℕ) :
    Matrix.rank (fun (i : Fin (p + 1)) (j : Fin (q + 1)) =>
      sampledCausalTail N h (i.val + j.val)) = 1 := by
  let H : Matrix (Fin (p + 1)) (Fin (q + 1)) ℝ :=
    fun i j => sampledCausalTail N h (i.val + j.val)
  let B : Matrix (Fin 1) (Fin 1) ℝ := H.submatrix (fun _ => 0) (fun _ => 0)
  let C : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => (causalResponse N (cutoff N))⁻¹
  have hBC : B * C = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp [B, C, H, Matrix.submatrix, Matrix.mul_apply, sampledCausalTail,
      causalResponse_cutoff_ne_zero]
  have hB : 1 ≤ B.rank := by
    have hr := Matrix.rank_mul_le_left B C
    rw [hBC, Matrix.rank_one, Fintype.card_fin] at hr
    exact hr
  exact le_antisymm (rank_sampledCausalTail_hankel_le_one N h _ _)
    (hB.trans (Matrix.rank_submatrix_le H (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)))

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
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.causalResponse_cutoff_ne_zero
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.causalResponse_cutoff_sq_pos
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.causalWindowEnergy_lt_laplaceEnergy
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_ne_zero
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.rank_sampledCausalTail_hankel_eq_one
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_eq_stateSpace
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.rank_sampledCausalTail_hankel_le_one
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.det_sampledCausalTail_hankel_two
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.sampledCausalTail_add
