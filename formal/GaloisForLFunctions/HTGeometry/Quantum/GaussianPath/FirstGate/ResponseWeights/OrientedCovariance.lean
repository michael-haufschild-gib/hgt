import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.PauliTrace
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.Variance

/-! # Oriented endpoint-pair weights for the response of one Pauli -/
namespace GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
noncomputable section

/-- For centred energies and marks, orienting each pair by its energy gap
gives the unnormalised covariance once for each unordered pair. -/
theorem oriented_endpoint_sum {I : Type*} [Fintype I] (E z : I→ℝ)
    (hE : ∑ i, E i=0) (hz : ∑ i, z i=0) :
    ∑ p : I×I, max 0 (E p.1-E p.2)*(z p.1-z p.2) =
      (Fintype.card I:ℝ)*∑ i, E i*z i := by
  let F (i j : I) := max 0 (E i-E j)*(z i-z j)
  have hp (i j : I) : F i j+F j i=(E i-E j)*(z i-z j) := by
    rcases le_total (E j) (E i) with h|h
    · simp only [F,max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h),zero_mul,add_zero]
    · simp only [F,max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h),zero_mul,zero_add]
      ring
  have hpair : (∑ i, ∑ j, (E i-E j)*(z i-z j))=2*((Fintype.card I:ℝ)*∑ i, E i*z i) := by
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,←Finset.mul_sum,←Finset.sum_mul,hE,hz,mul_zero,zero_mul,sub_zero,zero_sub]
    ring
  have hswap : (∑ i, ∑ j, F j i)=∑ i, ∑ j, F i j := Finset.sum_comm
  simp_rw [←hp] at hpair
  simp only [Finset.sum_add_distrib,hswap] at hpair
  rw [Fintype.sum_prod_type]
  change (∑ i, ∑ j, F i j)=_
  linarith only [hpair]

/-- For every onsite or bond observable, the signed incoming expectation
difference summed with the physical gap weights equals D² times its coupling. -/
theorem incoming_local_response {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    let E := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues
    let z := localMean p l
    ∑ ij : (Fin (n+2)→Bool) × (Fin (n+2)→Bool), max 0 (-E ij.1- -E ij.2)*(z ij.2-z ij.1) =
      ((2:ℝ)^(n+2))^2*p l := by
  intro E z
  have ht := oriented_endpoint_sum (fun j => -E j) (fun j => -z j)
    (by simpa only [Finset.sum_neg_distrib,neg_eq_zero] using (FluxOccupation.path_spectral_moments p).1)
    (by simpa only [Finset.sum_neg_distrib,neg_eq_zero] using localMean_sum p l)
  simp only [neg_sub_neg,neg_mul_neg,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,
    Nat.cast_ofNat,E,z,localMean_energy_sum] at ht
  simpa only [neg_sub_neg,E,z,sq,mul_assoc] using ht

#print axioms incoming_local_response
end
end GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
