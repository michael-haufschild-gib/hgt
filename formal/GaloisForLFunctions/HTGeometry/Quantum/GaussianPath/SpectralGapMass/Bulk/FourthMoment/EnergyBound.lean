import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.FourthMoment.GroupedSquare

/-! # A fourth-moment bound for every one-dimensional Pauli path -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
noncomputable section

private theorem nonidentity_energy {n : ℕ} (u : PathShell n) (Q : Word n)
    (hQ : Q≠pauliIdentityLabel (n+2)) :
    ‖squareWeight u Q‖^2 ≤ 42*∑ z ∈ factors Q, (u z.1)^2*(u z.2)^2 := by
  let S := factors Q
  let w := pairWeight u
  have htri := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S w) 2
  have hcs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun z => ‖w z‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have hcard : (S.card:ℝ) ≤ 42 := by exact_mod_cast nonidentity_factor_count Q hQ
  apply (htri.trans hcs).trans
  have he : (∑ z ∈ S, ‖w z‖^2) = ∑ z ∈ factors Q, (u z.1)^2*(u z.2)^2 := by
    simp only [S,w,norm_pairWeight,sq_abs,mul_pow]
  rw [he]
  exact mul_le_mul_of_nonneg_right hcard (sum_nonneg fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- In the fourth moment the repeated-label contributions are paid exactly. All other
Pauli coefficients of H² have at most 42 summands, including at the boundary of the path. -/
theorem path_fourth_moment {n : ℕ} (u : PathShell n) :
    let D := (2:ℝ)^(n+2)
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    (∑ j, E j^4)+42*D*(∑ i, u i^4) ≤ 43*D*(∑ i, u i^2)^2 := by
  classical
  intro D E
  let I := pauliIdentityLabel (n+2)
  let A (z : PathLabel n × PathLabel n) := (u z.1)^2*(u z.2)^2
  let V := ∑ i, u i^2
  let F := ∑ i, u i^4
  have hI : (∑ z ∈ factors I, A z)=F := by
    rw [sum_identity]
    exact sum_congr rfl fun i _ => by dsimp only [A]; ring
  have htotal : (∑ Q : Word n, ∑ z ∈ factors Q, A z)=V^2 := by
    rw [sum_factors,Fintype.sum_prod_type,sq]
    simp only [A,V,←mul_sum,←sum_mul]
  have h (Q : Word n) :
      ‖squareWeight u Q‖^2+(if Q=I then 42*F else 0) ≤
        (if Q=I then V^2 else 0)+42*∑ z ∈ factors Q, A z := by
    by_cases hQ : Q=I
    · subst Q
      rw [if_pos rfl,if_pos rfl,identity_weight,Complex.norm_real,Real.norm_eq_abs,sq_abs,hI]
    · simpa only [if_neg hQ,add_zero,zero_add] using nonidentity_energy u Q hQ
  have hsum := sum_le_sum (s:=univ) fun Q _ => h Q
  simp only [sum_add_distrib,Finset.sum_ite_eq',mem_univ,if_true,←mul_sum,htotal] at hsum
  have hd : 0≤D := (pow_pos (by norm_num) _).le
  have he : (∑ j, E j^4)=D*∑ Q, ‖squareWeight u Q‖^2 := fourth_energy u
  rw [he]
  change D*_+42*D*F ≤ 43*D*V^2
  linarith only [mul_le_mul_of_nonneg_left hsum hd]

#print axioms path_fourth_moment
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.FourthMoment
