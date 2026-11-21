import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.PauliPencil
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # A common box for the couplings and all energies -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A characteristic root of a complex matrix with entries bounded by M has
modulus at most (D+1)M, by strict diagonal dominance outside that disk. -/
theorem root_bound_of_entry_bound {D : ℕ} (H : Matrix (Fin D) (Fin D) ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ i j, ‖H i j‖ ≤ M) {z : ℂ} (hz : matrixCharpolyRelation (H,z) = 0) :
    ‖z‖ ≤ ((D:ℝ)+1)*M := by
  by_contra! hn
  apply (det_ne_zero_of_sum_row_lt_diag (A := Matrix.scalar (Fin D) z-H) ?_) hz
  intro i
  let s := Finset.univ.erase i
  have he (j : Fin D) (hj : j ∈ s) : ‖(Matrix.scalar (Fin D) z-H) i j‖ ≤ M := by
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simpa [Matrix.scalar_apply,Ne.symm hji] using hh i j
  have hcount : s.card ≤ D := (Finset.card_le_card (Finset.erase_subset i _)).trans_eq (by simp)
  have hsum : ∑ j ∈ s, ‖(Matrix.scalar (Fin D) z-H) i j‖ ≤ (D:ℝ)*M :=
    (Finset.sum_le_sum he).trans (by
      rw [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) hM)
  apply hsum.trans_lt
  simp only [Matrix.sub_apply,Matrix.scalar_apply,Matrix.diagonal_apply_eq]
  linarith only [hn,hh i i,norm_sub_norm_le z (H i i)]

/-- A single radius contains the couplings and all characteristic roots when
each real Pauli coupling has absolute value at most T. -/
def pathBoxRadius (N : ℕ) (T : ℝ) : ℝ :=
  T + (((2^N : ℕ) : ℝ)+1)*((Fintype.card (ChainLabel N) : ℝ)*T)

theorem pathBoxRadius_ge (N : ℕ) {T : ℝ} (hT : 0 ≤ T) : T ≤ pathBoxRadius N T :=
  le_add_of_nonneg_right (by positivity)

theorem path_root_in_box (N : ℕ) (x : Coordinates N → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hx : ∀ i, ‖x i‖ ≤ T) {z : ℂ}
    (hz : matrixCharpolyRelation (∑ a, x a • chainPauliFin N a,z) = 0) :
    ‖z‖ ≤ pathBoxRadius N T := by
  apply (root_bound_of_entry_bound _ (mul_nonneg (Nat.cast_nonneg _) hT) _ hz).trans
    (le_add_of_nonneg_left hT)
  intro i j
  rw [Matrix.sum_apply]
  apply (norm_sum_le _ _).trans
  have he (a : Coordinates N) : ‖(x a • chainPauliFin N a) i j‖ ≤ T := by
    rw [Matrix.smul_apply,smul_eq_mul,norm_mul]
    exact (mul_le_mul (hx a) (path_entry_le_one N a i j) (norm_nonneg _) hT).trans_eq (mul_one T)
  exact (Finset.sum_le_sum fun a _ => he a).trans_eq (by simp [nsmul_eq_mul,Coordinates])

#print axioms path_root_in_box
end
end GaloisForLFunctions.HTGeometry.SpectralJets
