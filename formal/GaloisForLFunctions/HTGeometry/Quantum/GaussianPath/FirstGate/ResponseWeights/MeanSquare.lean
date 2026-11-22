import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.OrientedCovariance

/-! # Quantitative visibility of a preassigned onsite or bond observable -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
noncomputable section

/-- The energy component of a local Pauli gives a lower bound on its
mean squared diagonal expectation at every real path Hamiltonian. -/
theorem localMean_square_floor {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    (2:ℝ)^(n+2)*(p l)^2 ≤ (∑ m : PathLabel n, (p m)^2)*∑ j, (localMean p l j)^2 := by
  let E := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ E (localMean p l)
  rw [show (∑ j, E j*localMean p l j)=_ from localMean_energy_sum p l,
    show (∑ j, E j^2)=_ from (FluxOccupation.path_spectral_moments p).2] at h
  push_cast at h
  exact le_of_mul_le_mul_left (a := (2:ℝ)^(n+2)) (by simpa only [mul_pow,sq,mul_assoc] using h)
    (pow_pos (by norm_num) _)

/-- Total squared endpoint separations for one prescribed Pauli are at
least twice D² times its fraction of the coupling energy. -/
theorem localMean_pair_square_floor {n : ℕ} (p : PathShell n) (l : PathLabel n) :
    let D := (2:ℝ)^(n+2)
    let z := localMean p l
    2*D^2*(p l)^2 ≤ (∑ m : PathLabel n, (p m)^2)*
      ∑ ij : (Fin (n+2) → Bool) × (Fin (n+2) → Bool), (z ij.1-z ij.2)^2 := by
  intro D z
  have hs : ∑ j, z j=0 := localMean_sum p l
  have he : (∑ ij : (Fin (n+2) → Bool) × (Fin (n+2) → Bool), (z ij.1-z ij.2)^2) =
      2*D*∑ j, (z j)^2 := by
    rw [Fintype.sum_prod_type]
    simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,←Finset.mul_sum,hs,mul_zero,sub_zero,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat,D]
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (localMean_square_floor p l) (show 0≤2*D by dsimp [D]; positivity)
  calc
    _ = (2*D)*(D*(p l)^2) := by ring
    _ ≤ _ := h
    _ = _ := by ring

#print axioms localMean_pair_square_floor
end
end GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
