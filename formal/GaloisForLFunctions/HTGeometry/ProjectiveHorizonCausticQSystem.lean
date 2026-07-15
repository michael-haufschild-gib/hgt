import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchurCaustic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Q-system constraints on projective-horizon caustics

Rectangular Schur determinants satisfy the `A`-type Q-system.  Applied to the squared reciprocal
jet, this is a static octahedron relation coupling caustics at adjacent pairs of horizon depths.
The resolution indices are not a time variable.

This file certifies the first two nontrivial ranks directly and the integral-domain zero-propagation
consequence.  The all-rank Desnanot--Jacobi identity is retained at paper level until the required
general complementary-minor theorem is available in the local Lean matrix library.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- A central block with one of two possible outer rows and columns adjoined. -/
noncomputable def twoBorderMinor
    {K ι : Type*} [CommRing K]
    (D : Matrix ι ι K) (B : Matrix ι (Fin 2) K)
    (C : Matrix (Fin 2) ι K) (E : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 2) : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) K :=
  Matrix.fromBlocks D (fun r _ => B r j) (fun _ c => C i c) (fun _ _ => E i j)

/-- Schur-complement evaluation of a one-row, one-column border around an invertible center. -/
theorem det_twoBorderMinor
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι K) (B : Matrix ι (Fin 2) K)
    (C : Matrix (Fin 2) ι K) (E : Matrix (Fin 2) (Fin 2) K)
    (i j : Fin 2) [Invertible D] :
    (twoBorderMinor D B C E i j).det =
      D.det * (E i j - (C * D⁻¹ * B) i j) := by
  rw [← Matrix.invOf_eq_nonsing_inv D]
  rw [twoBorderMinor, Matrix.det_fromBlocks₁₁]
  congr 1
  simp [Matrix.mul_apply]

/-- Desnanot--Jacobi for a matrix with an invertible central block and two border directions.
This is the all-rank determinant engine behind the rectangular horizon Q-system. -/
theorem det_fromBlocks_twoBorder_mul_center
    {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι K) (B : Matrix ι (Fin 2) K)
    (C : Matrix (Fin 2) ι K) (E : Matrix (Fin 2) (Fin 2) K)
    [Invertible D] :
    (Matrix.fromBlocks D B C E).det * D.det =
      (twoBorderMinor D B C E 0 0).det * (twoBorderMinor D B C E 1 1).det -
        (twoBorderMinor D B C E 0 1).det * (twoBorderMinor D B C E 1 0).det := by
  rw [Matrix.det_fromBlocks₁₁]
  simp only [det_twoBorderMinor]
  rw [← Matrix.invOf_eq_nonsing_inv D]
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply]
  ring

/-- The rectangular Schur Q-system at rank one. -/
theorem rectangularSchurQSystem_rank_one
    {K : Type*} [CommRing K] (h : ℕ → K) {n : ℕ} (hn : 0 < n) :
    (rectangularSchurToeplitz h n 1).det ^ 2 =
      (rectangularSchurToeplitz h (n - 1) 1).det *
          (rectangularSchurToeplitz h (n + 1) 1).det +
        (rectangularSchurToeplitz h n 0).det *
          (rectangularSchurToeplitz h n 2).det := by
  have hn' : 1 ≤ n := hn
  simp [rectangularSchurToeplitz, Matrix.det_fin_two, hn', pow_two]

/-- The first genuinely three-by-three rectangular Schur Q-system instance. -/
theorem rectangularSchurQSystem_rank_two
    {K : Type*} [CommRing K] (h : ℕ → K) {n : ℕ} (hn : 2 ≤ n) :
    (rectangularSchurToeplitz h n 2).det ^ 2 =
      (rectangularSchurToeplitz h (n - 1) 2).det *
          (rectangularSchurToeplitz h (n + 1) 2).det +
        (rectangularSchurToeplitz h n 1).det *
          (rectangularSchurToeplitz h n 3).det := by
  have hn1 : 1 ≤ n := by omega
  have hnsub : 1 ≤ n - 1 := by omega
  simp [rectangularSchurToeplitz, Matrix.det_fin_two, Matrix.det_fin_three,
    hn, hn1, hnsub, pow_two, Nat.sub_sub]
  ring

/-- In a domain, two adjacent zero Q-system amplitudes force a zero in one transverse direction.
This is the local algebraic propagation rule for adjacent horizon caustics. -/
theorem qSystem_zero_propagation
    {K : Type*} [CommRing K] [IsDomain K]
    {center left right up down : K}
    (hq : center ^ 2 = left * right + up * down)
    (hcenter : center = 0) (hleft : left = 0) :
    up = 0 ∨ down = 0 := by
  have hud : up * down = 0 := by
    simpa [hcenter, hleft] using hq.symm
  exact mul_eq_zero.mp hud

end GaloisForLFunctions.HTGeometry
