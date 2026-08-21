import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The cofactor matrix as a permutation sum

`cofSum M i j` is the `(i,j)` cofactor of a square matrix, written as the signed sum over those
permutations that send `j` to `i`.  This is the shape the Piola identity needs: differentiating a
cofactor of a Jacobian matrix then differentiates a product of first order partial derivatives, and
the resulting index set carries a fixed-point-free sign-reversing involution.

The identification `cofSum M i j = M.adjugate j i` transports mathlib's `Matrix.mul_adjugate` into
the row contraction `∑ b, cofSum M i b * M l b = δ (l = i) · det M`, which is the algebraic half of
the divergence form of the Jacobian determinant.
-/

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

open Matrix Finset Equiv

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The `(i,j)` cofactor of `M`, as a signed sum over the permutations sending `j` to `i`. -/
def cofSum (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) : R :=
  ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => σ j = i),
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ k ∈ univ.erase j, M (σ k) k

theorem cofSum_eq_adjugate (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    cofSum M i j = M.adjugate j i := by
  classical
  rw [Matrix.adjugate_apply, Matrix.det_apply', cofSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  set N := M.updateRow i (Pi.single j (1 : R)) with hN
  have hentry : ∀ k : Fin n, N (σ k) k
      = if σ k = i then (Pi.single j (1:R) : Fin n → R) k else M (σ k) k := by
    intro k
    by_cases h : σ k = i
    · simp [hN, h]
    · simp [hN, h]
  have hk0 : σ (σ⁻¹ i) = i := by simp
  have hsplit : (∏ k, N (σ k) k)
      = N (σ (σ⁻¹ i)) (σ⁻¹ i) * ∏ k ∈ univ.erase (σ⁻¹ i), N (σ k) k :=
    (Finset.mul_prod_erase univ (fun k => N (σ k) k) (Finset.mem_univ (σ⁻¹ i))).symm
  have hrest : ∀ k ∈ univ.erase (σ⁻¹ i), N (σ k) k = M (σ k) k := by
    intro k hk
    have hne : k ≠ σ⁻¹ i := (Finset.mem_erase.mp hk).1
    have hnei : σ k ≠ i := by
      intro h
      exact hne (by simp [← h])
    simp [hentry k, hnei]
  rw [hsplit, Finset.prod_congr rfl hrest, hentry (σ⁻¹ i), if_pos hk0]
  by_cases hj : σ j = i
  · have hinv : σ⁻¹ i = j := by rw [← hj]; simp
    rw [hinv, if_pos hj]
    simp
  · rw [if_neg hj]
    have hinv : σ⁻¹ i ≠ j := by
      intro h
      exact hj (by rw [← h]; simp)
    rw [Pi.single_apply, if_neg hinv, zero_mul, mul_zero]

/-- Row contraction: `∑ b, cofSum M i b * M l b = δ (l = i) * det M`. -/
theorem sum_cofSum_mul (M : Matrix (Fin n) (Fin n) R) (i l : Fin n) :
    ∑ b, cofSum M i b * M l b = if l = i then M.det else 0 := by
  classical
  have h := Matrix.mul_adjugate M
  have h2 := congrFun (congrFun h l) i
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h2
  calc ∑ b, cofSum M i b * M l b = ∑ b, M l b * M.adjugate b i := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [cofSum_eq_adjugate]; ring
    _ = if l = i then M.det else 0 := by rw [h2]; split <;> simp

end GaloisForLFunctions.HTGeometry.PoincareHopf
