import GaloisForLFunctions.HTGeometry.ComplexSchurPosDef
import Mathlib.Analysis.Matrix.LDL

/-!
# Jacobi decomposition of positive Hermitian matrices

Mathlib's LDL construction is generic over `RCLike`, but the corpus previously exposed only its
real Jacobi consequence.  Normalizing the complex lower factor and inverting it gives the exact
Hermitian analogue `A = Uᴴ D U`, with `U` complex upper unipotent and `D` positive diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

theorem blockTriangular_of_lower_complex {M : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j : Fin n, i < j → M i j = 0) :
    M.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
  fun i j hij => h i j (by simpa using hij)

theorem lower_of_blockTriangular_complex {M : Matrix (Fin n) (Fin n) ℂ}
    (h : M.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)) :
    ∀ i j : Fin n, i < j → M i j = 0 :=
  fun i j hij => h (by simpa using hij)

theorem lower_mul_diag_complex {M N : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ i j : Fin n, i < j → M i j = 0)
    (hN : ∀ i j : Fin n, i < j → N i j = 0) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_)
    (fun hcon => absurd (Finset.mem_univ i) hcon)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hN k i h, mul_zero]
  · rw [hM i k h, zero_mul]

theorem lowerTriangular_diag_ne_zero_complex
    {M : Matrix (Fin n) (Fin n) ℂ} [Invertible M]
    (hM : ∀ i j : Fin n, i < j → M i j = 0) (i : Fin n) : M i i ≠ 0 := by
  have hinv : ∀ a b : Fin n, a < b → M⁻¹ a b = 0 :=
    lower_of_blockTriangular_complex (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower_complex hM))
  have h1 : (M⁻¹ * M) i i = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible M)]
    simp
  rw [lower_mul_diag_complex hinv hM] at h1
  intro hcon
  rw [hcon, mul_zero] at h1
  exact zero_ne_one h1

theorem unitTriangular_inv_diag_complex
    {M : Matrix (Fin n) (Fin n) ℂ} [Invertible M]
    (hM : ∀ i j : Fin n, i < j → M i j = 0)
    (hdiag : ∀ i, M i i = 1) (i : Fin n) : M⁻¹ i i = 1 := by
  have hinv : ∀ a b : Fin n, a < b → M⁻¹ a b = 0 :=
    lower_of_blockTriangular_complex (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower_complex hM))
  have h1 : (M⁻¹ * M) i i = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible M)]
    simp
  rw [lower_mul_diag_complex hinv hM, hdiag i, mul_one] at h1
  exact h1

/-- A positive-definite Hermitian matrix is `Uᴴ D U` with complex upper-unipotent `U` and a
positive diagonal `D`. -/
theorem exists_complex_jacobi_decomposition
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      (∀ i, 0 < d i) ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧
      A = Uᴴ * Matrix.diagonal d * U := by
  classical
  set V : Matrix (Fin n) (Fin n) ℂ := LDL.lowerInv hA with hV
  haveI : Invertible V := by rw [hV]; exact LDL.invertibleLowerInv hA
  have hVlow : ∀ i j : Fin n, i < j → V i j = 0 :=
    fun i j hij => LDL.lowerInv_triangular hA hij
  have hVne : ∀ i, V i i ≠ 0 := fun i => lowerTriangular_diag_ne_zero_complex hVlow i
  set c : Fin n → ℂ := fun i => (V i i)⁻¹ with hc
  have hcne : ∀ i, c i ≠ 0 := fun i => inv_ne_zero (hVne i)
  haveI : Invertible (Matrix.diagonal c) :=
    Matrix.invertibleOfIsUnitDet _ (by
      rw [Matrix.det_diagonal]
      exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hcne i))
  set W : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal c * V with hW
  haveI : Invertible W := by
    refine Matrix.invertibleOfIsUnitDet _ ?_
    rw [hW, Matrix.det_mul]
    exact (isUnit_det_of_invertible (Matrix.diagonal c)).mul (isUnit_det_of_invertible V)
  have hWlow : ∀ i j : Fin n, i < j → W i j = 0 := by
    intro i j hij
    rw [hW, Matrix.diagonal_mul, hVlow i j hij, mul_zero]
  have hWdiag : ∀ i, W i i = 1 := by
    intro i
    rw [hW, Matrix.diagonal_mul, hc]
    exact inv_mul_cancel₀ (hVne i)
  have hVA : V * A * Vᴴ = LDL.diag hA := by
    exact (LDL.diag_eq_lowerInv_conj hA).symm
  set e : Fin n → ℂ := LDL.diagEntries hA with he
  have hdiagE : LDL.diag hA = Matrix.diagonal e := rfl
  set d : Fin n → ℂ := fun i => c i * e i * star (c i) with hd
  have hWA : W * A * Wᴴ = Matrix.diagonal d := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    calc
      Matrix.diagonal c * V * A * (Vᴴ * Matrix.diagonal (star c)) =
          Matrix.diagonal c * (V * A * Vᴴ) * Matrix.diagonal (star c) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal c * Matrix.diagonal e * Matrix.diagonal (star c) := by
        rw [hVA, hdiagE]
      _ = Matrix.diagonal d := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, hd]
        apply congrArg Matrix.diagonal
        funext i
        rfl
  have hWinj : Function.Injective W.vecMul :=
    Matrix.vecMul_injective_of_isUnit (isUnit_of_invertible W)
  have hDpos : (Matrix.diagonal d).PosDef := by
    rw [← hWA]
    exact hA.mul_mul_conjTranspose_same hWinj
  have hdpos : ∀ i, 0 < d i := Matrix.posDef_diagonal_iff.1 hDpos
  set L : Matrix (Fin n) (Fin n) ℂ := W⁻¹ with hL
  have hLlow : ∀ i j : Fin n, i < j → L i j = 0 :=
    lower_of_blockTriangular_complex (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower_complex hWlow))
  have hLdiag : ∀ i, L i i = 1 :=
    fun i => unitTriangular_inv_diag_complex hWlow hWdiag i
  have hWu : IsUnit W.det := isUnit_det_of_invertible W
  have hWHu : IsUnit (Wᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact hWu.star
  have hAeq : A = L * Matrix.diagonal d * Lᴴ := by
    rw [hL, Matrix.conjTranspose_nonsing_inv, ← hWA, Matrix.mul_assoc W A Wᴴ,
      ← Matrix.mul_assoc W⁻¹ W (A * Wᴴ), Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWHu, Matrix.mul_one]
  refine ⟨Lᴴ, d, hdpos, ?_, ?_, ?_⟩
  · intro i j hji
    simp [Matrix.conjTranspose_apply, hLlow j i hji]
  · intro i
    simp [Matrix.conjTranspose_apply, hLdiag i]
  · rw [Matrix.conjTranspose_conjTranspose]
    exact hAeq

end GaloisForLFunctions.HTGeometry
