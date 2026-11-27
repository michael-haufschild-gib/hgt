import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators

/-! # Commutator of two nearest-neighbour Pauli Hamiltonians -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section

private theorem row_mass {n : ℕ} (u : PathShell n) :
    (∑ l : PathLabel n, ∑ _q ∈ pathOverlaps l, (u l)^2) ≤ 42*‖u‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Finset.mul_sum]
  apply sum_le_sum
  intro l _
  simp only [sum_const,nsmul_eq_mul,Real.norm_eq_abs,sq_abs]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast pathOverlaps_card_le l) (sq_nonneg _)

private theorem column_mass {n : ℕ} (v : PathShell n) :
    (∑ l : PathLabel n, ∑ q ∈ pathOverlaps l, (v q)^2) ≤ 42*‖v‖^2 := by
  have hs (l q : PathLabel n) : q ∈ pathOverlaps l ↔ l ∈ pathOverlaps q := by
    rw [mem_pathOverlaps,mem_pathOverlaps,disjoint_comm]
  have h (l : PathLabel n) (f : PathLabel n → ℝ) :
      (∑ q ∈ pathOverlaps l, f q)=∑ q : PathLabel n, if q ∈ pathOverlaps l then f q else 0 := by
    rw [←sum_filter]; simp
  apply le_trans _ (row_mass v)
  apply le_of_eq
  simp_rw [h]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun q _ => if_congr (hs q l) rfl rfl

/-- Each interaction overlaps at most 42 others. The two Hamiltonians
can have different coefficients, and every disjoint pair drops out. -/
theorem path_pair_commutator {n : ℕ} (u v : PathShell n) :
    ‖pathHamiltonian u*pathHamiltonian v-pathHamiltonian v*pathHamiltonian u‖ ≤ 
      42*(‖u‖^2+‖v‖^2) := by
  classical
  let X (w : PathShell n) (l : PathLabel n) := (w l:ℂ) • finitePauliMatrix (pathWord l)
  have hnorm (w : PathShell n) (l : PathLabel n) : ‖X w l‖=|w l| := by
    simp only [X,norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [pathHamiltonian_eq_sum u,pathHamiltonian_eq_sum v]
  apply (LocalErrors.norm_commutator_sums univ univ (X u) (X v)).trans
  have hrow (l : PathLabel n) :
      (∑ q : PathLabel n, ‖X u l*X v q-X v q*X u l‖) ≤ 
        ∑ q ∈ pathOverlaps l, ((u l)^2+(v q)^2) := by
    rw [←sum_subset (subset_univ (pathOverlaps l)) (fun q _ hq => ?_)]
    · apply sum_le_sum
      intro q _
      have hn := (norm_sub_le (X u l*X v q) (X v q*X u l)).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      rw [hnorm,hnorm] at hn
      linarith only [hn,sq_nonneg (|u l|-|v q|),sq_abs (u l),sq_abs (v q)]
    · have hd : Disjoint (labelSupport (pathWord l)) (labelSupport (pathWord q)) := by
        by_contra h
        exact hq (mem_pathOverlaps.mpr h)
      have h := ((commute_finitePauliMatrix_of_disjoint hd).smul_left (u l:ℂ)).smul_right (v q:ℂ)
      rw [show X u l*X v q=X v q*X u l from h.eq,sub_self,norm_zero]
  apply (sum_le_sum (fun l _ => hrow l)).trans
  simp_rw [sum_add_distrib]
  rw [mul_add]
  exact add_le_add (row_mass u) (column_mass v)

#print axioms path_pair_commutator
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
