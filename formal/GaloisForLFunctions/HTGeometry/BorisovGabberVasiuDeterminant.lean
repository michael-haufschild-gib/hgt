import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Multilinear.Basic

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A rank-one perturbation has no determinant terms of order two or higher. -/
theorem bgv_det_add_vecMulVec_rows (A : Matrix ι ι R) (u v : ι → R) :
    (A + vecMulVec u v).det = A.det + ∑ i, u i * (A.updateRow i v).det := by
  let f := (detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand := f.toMultilinearMap.map_add_eq_map_add_linearDeriv_add A
    (fun i => u i • v)
  have hzero (s : Finset ι) (hs : 2 ≤ s.card) :
      f (s.piecewise (fun i => u i • v) A) = 0 := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs
    let B := s.piecewise (fun i => u i • v) A
    have hB : B = Function.update (Function.update B j (u j • v)) i (u i • v) := by
      ext k
      by_cases hki : k = i
      · subst k; simp [B, hi]
      · by_cases hkj : k = j
        · subst k; simp [B, hj, hki]
        · simp [Function.update_of_ne hki, Function.update_of_ne hkj]
    change f B = 0
    rw [hB, f.map_update_smul]
    rw [Function.update_comm hij.symm]
    rw [f.map_update_smul, f.map_update_update _ hij, smul_zero, smul_zero]
  have hsum : (∑ s : Finset ι with 2 ≤ s.card,
      f.toMultilinearMap (s.piecewise (fun i => u i • v) A)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact hzero s (Finset.mem_filter.mp hs).2
  rw [hsum, add_zero, MultilinearMap.linearDeriv_apply] at hexpand
  change (A + vecMulVec u v).det =
    A.det + ∑ i, (A.updateRow i (u i • v)).det at hexpand
  simpa only [det_updateRow_smul] using hexpand

/-- The matrix determinant lemma, including singular matrices. -/
theorem bgv_det_add_vecMulVec (A : Matrix ι ι R) (u v : ι → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  rw [bgv_det_add_vecMulVec_rows]
  simp_rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  simp only [dotProduct, mulVec, transpose_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

/-- Borisov--Gabber--Vasiu, Lemma 21.1; no diagonal entry need be invertible. -/
theorem bgv_det_diagonal_add_vecMulVec (a u v : ι → R) :
    (diagonal a + vecMulVec u v).det =
      (∏ i, a i) + ∑ i, u i * v i * ∏ j ∈ Finset.univ.erase i, a j := by
  rw [bgv_det_add_vecMulVec, det_diagonal, adjugate_diagonal]
  congr 1
  simp only [mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

end GaloisForLFunctions.HTGeometry
