import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.TimeAverages.CircuitPrice

/-! # Resolution of energy and local slope differences in a first-wait window -/

open Finset Real
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open Dephasing.PairedFields.SpectralEdge
open private replica_twist_le from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ResolutionBins.AlignedMoment
noncomputable section

/-- Outside this quadratic sublevel set an individual pair is attenuated
by at least exp(-H), uniformly in its phase. -/
theorem resolved_action_le (m u H : ℝ) (c V : ℝ≥0)
    (h : 2*H ≤ (m^2-2*H*V)*c + V*u^2) : ‖timeActionKernel m u c V‖ ≤ exp (-H) := by
  let D := 1+(c:ℝ)*V
  have hD : 1 ≤ D := le_add_of_nonneg_right (mul_nonneg c.coe_nonneg V.coe_nonneg)
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hroot : 1 ≤ sqrt D := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hD
  have hdecay : -(c*m^2+V*u^2)/(2*D) ≤ -H := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hDpos)).mpr
    dsimp only [D]
    linarith only [h]
  rw [norm_time_action]
  exact (mul_le_of_le_one_left (exp_pos _).le (inv_le_one_of_one_le₀ hroot)).trans
    (Real.exp_le_exp.mpr hdecay)

/-- Only replica pairs inside the indicated energy and slope region
contribute to this signed sum. Its slope coefficient is positive when
the squared window center exceeds 2H times the observation variance. -/
def unresolvedTwistSum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ) (q : ℕ) (b m H : ℝ) (V : ℝ≥0) : ℂ := by
  classical
  exact ∑ p ∈ univ.piAntidiag q, ∑ k ∈ univ.piAntidiag q,
    let u := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
    let c := pairVariance v b p k
    if (m^2-2*H*V)*c + V*u^2 < 2*H then
      (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k * timeActionKernel m u c V
    else 0

/-- Discarding all resolved pairs costs at most exp(-H) per circuit,
independently of the number of replica pairs or the replica order. -/
theorem circuit_resolution_error {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) (v : J → I → ℝ)
    (z : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (q : ℕ) (b m H : ℝ) (V : ℝ≥0) :
    ‖windowTwistSum E w v z q b m V - unresolvedTwistSum E w v z q b m H V‖ ≤ exp (-H) := by
  classical
  let B : Finset (I → ℕ) := (univ : Finset I).piAntidiag q
  let u (p k : I → ℕ) := replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k
  let c := pairVariance v b
  let W := fidelityReplicaMultiplicityWeight w
  let f (p k : I → ℕ) := (W p k:ℂ)*replicaMultiplicityTwist z p k*timeActionKernel m (u p k) (c p k) V
  let g (p k : I → ℕ) := if (m^2-2*H*V)*c p k + V*(u p k)^2 < 2*H then f p k else 0
  have hd (p k : I → ℕ) : ‖f p k-g p k‖ ≤ W p k*exp (-H) := by
    have hn : 0 ≤ W p k := fidelityReplicaMultiplicityWeight_nonneg hw p k
    dsimp only [g]
    split_ifs with hnear
    · rw [sub_self,norm_zero]
      exact mul_nonneg hn (exp_pos _).le
    · rw [sub_zero]
      dsimp only [f]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hn]
      exact mul_le_mul (mul_le_of_le_one_right hn (replica_twist_le hz p k))
        (resolved_action_le m (u p k) H (c p k) V (le_of_not_gt hnear)) (norm_nonneg _) hn
  change ‖(∑ p ∈ B, ∑ k ∈ B, f p k)-(∑ p ∈ B, ∑ k ∈ B, g p k)‖ ≤ _
  rw [←sum_sub_distrib]
  simp_rw [←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ p ∈ B, ∑ k ∈ B, W p k*exp (-H) :=
      sum_le_sum fun p _ => (norm_sum_le ..).trans (sum_le_sum fun k _ => hd p k)
    _ = _ := by simp_rw [←sum_mul]; rw [sum_fidelityReplicaMultiplicityWeight_eq_one w q hsum,one_mul]

/-- All unresolved terms can be added across the circuit family before
taking a norm. The error for all excluded pairs is the number of circuits
times exp(-H). -/
theorem circuit_family_resolution {I J ι : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype ι]
    (E w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1) (v : J → I → ℝ)
    (z : ι → I → ℂ) (hz : ∀ j i, ‖z j i‖ ≤ 1) (q : ℕ) (b m H : ℝ) (V : ℝ≥0) :
    ‖((∑ j, windowTwistPrice E w v (z j) q b m V : ℝ):ℂ) -
      ∑ j, unresolvedTwistSum E w v (z j) q b m H V‖ ≤ Fintype.card ι*exp (-H) := by
  have he : ((∑ j, windowTwistPrice E w v (z j) q b m V : ℝ):ℂ) =
      ∑ j, windowTwistSum E w v (z j) q b m V := by
    push_cast
    exact sum_congr rfl fun j _ => (averaged_twist E w v (z j) q b m V).2.symm
  rw [he,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ)
    (fun j _ => circuit_resolution_error E w hw hsum v (z j) (hz j) q b m H V)

#print axioms resolved_action_le
#print axioms circuit_resolution_error
#print axioms circuit_family_resolution
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
