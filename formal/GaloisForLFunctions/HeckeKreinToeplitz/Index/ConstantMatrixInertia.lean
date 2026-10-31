import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# Negative directions of constant matrix perturbations

A constant matrix has rank at most one. Adding it to negative identity removes
at most one negative direction, independently of the matrix size.
-/

open Matrix Finset
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A constant matrix has rank at most one. -/
theorem rank_constant_le_one {ι : Type*} [Fintype ι] (z : ℂ) :
    (Matrix.of (fun _ _ : ι => z)).rank ≤ 1 := by
  have he : Matrix.of (fun _ _ : ι => z) =
      Matrix.vecMulVec (fun _ : ι => z) (fun _ : ι => (1 : ℂ)) := by
    ext i j
    change z = z * 1
    exact (mul_one z).symm
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

/-- A constant perturbation removes at most one negative direction from negative identity. -/
theorem constant_sub_one_index_lower (z : ℂ) (n : ℕ) :
    n ≤ hermNegIndex (Matrix.of (fun _ _ : Fin (n + 1) => z) - 1) := by
  have hn : hermNegIndex (-(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) = n + 1 := by
    have he : -(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        Matrix.diagonal (fun _ => ((-1 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [he, negIndex_diagonal]
    simp
  have h := hermNegIndex_le_add_rank
    (-(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) (Matrix.of (fun _ _ => z))
  have he : -(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Matrix.of (fun _ _ => z) =
      Matrix.of (fun _ _ : Fin (n + 1) => z) - 1 := by abel
  rw [hn, he] at h
  have hr := rank_constant_le_one (ι := Fin (n + 1)) z
  omega

#print axioms rank_constant_le_one
#print axioms constant_sub_one_index_lower
end GaloisForLFunctions.HeckeKreinToeplitz
