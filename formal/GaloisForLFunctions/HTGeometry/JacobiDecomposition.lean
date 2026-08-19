import Mathlib.Analysis.Matrix.LDL
import GaloisForLFunctions.HTGeometry.PositiveDefiniteCone

/-!
# Jacobi's decomposition of a real positive definite form

Every real positive definite matrix is `Uᵀ D U` with `U` unipotent upper triangular and `D`
positive diagonal.  These are the coordinates in which Siegel sets are defined, so this is the first
step of reduction theory.

The decomposition is mathlib's `LDL`, normalised and transposed: Gram–Schmidt on the standard basis
in the inner product of the form produces an invertible lower triangular matrix, whose diagonal is
scaled to one and whose inverse is again unit lower triangular.

* `lowerTriangular_diag_ne_zero` : an invertible lower triangular matrix has nonzero diagonal.
* `unitTriangular_inv_diag` : the inverse of a unit lower triangular matrix has unit diagonal.
* `exists_jacobi_decomposition` : **the decomposition.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- Lower triangularity in the form mathlib's block-triangularity takes. -/
theorem blockTriangular_of_lower {M : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j : Fin n, i < j → M i j = 0) :
    M.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ) :=
  fun i j hij => h i j (by simpa using hij)

theorem lower_of_blockTriangular {M : Matrix (Fin n) (Fin n) ℝ}
    (h : M.BlockTriangular (OrderDual.toDual : Fin n → (Fin n)ᵒᵈ)) :
    ∀ i j : Fin n, i < j → M i j = 0 :=
  fun i j hij => h (by simpa using hij)

/-- The `(i,i)` entry of a product of two lower triangular matrices is the product of the entries. -/
theorem lower_mul_diag {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j : Fin n, i < j → M i j = 0) (hN : ∀ i j : Fin n, i < j → N i j = 0) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun hcon => absurd (Finset.mem_univ i) hcon)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hN k i h, mul_zero]
  · rw [hM i k h, zero_mul]

/-- **An invertible lower triangular matrix has nonzero diagonal.** -/
theorem lowerTriangular_diag_ne_zero {M : Matrix (Fin n) (Fin n) ℝ} [Invertible M]
    (hM : ∀ i j : Fin n, i < j → M i j = 0) (i : Fin n) : M i i ≠ 0 := by
  have hinv : ∀ a b : Fin n, a < b → M⁻¹ a b = 0 :=
    lower_of_blockTriangular (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower hM))
  have h1 : (M⁻¹ * M) i i = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible M)]
    simp
  rw [lower_mul_diag hinv hM] at h1
  intro hcon
  rw [hcon, mul_zero] at h1
  exact zero_ne_one h1

/-- **The inverse of a unit lower triangular matrix has unit diagonal.** -/
theorem unitTriangular_inv_diag {M : Matrix (Fin n) (Fin n) ℝ} [Invertible M]
    (hM : ∀ i j : Fin n, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1) (i : Fin n) :
    M⁻¹ i i = 1 := by
  have hinv : ∀ a b : Fin n, a < b → M⁻¹ a b = 0 :=
    lower_of_blockTriangular (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower hM))
  have h1 : (M⁻¹ * M) i i = 1 := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_invertible M)]
    simp
  rw [lower_mul_diag hinv hM, hdiag i, mul_one] at h1
  exact h1

/-- **Jacobi's decomposition.**  A real positive definite matrix is `Uᵀ D U` with `U` unipotent
upper triangular and `D` positive diagonal. -/
theorem exists_jacobi_decomposition {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      (∀ i, 0 < d i) ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧
      A = Uᵀ * Matrix.diagonal d * U := by
  classical
  set V : Matrix (Fin n) (Fin n) ℝ := LDL.lowerInv hA with hV
  haveI : Invertible V := by rw [hV]; exact LDL.invertibleLowerInv hA
  have hVlow : ∀ i j : Fin n, i < j → V i j = 0 := fun i j hij => LDL.lowerInv_triangular hA hij
  have hVne : ∀ i, V i i ≠ 0 := fun i => lowerTriangular_diag_ne_zero hVlow i
  set c : Fin n → ℝ := fun i => (V i i)⁻¹ with hc
  have hcne : ∀ i, c i ≠ 0 := fun i => inv_ne_zero (hVne i)
  haveI : Invertible (Matrix.diagonal c) :=
    Matrix.invertibleOfIsUnitDet _ (by
      rw [Matrix.det_diagonal]
      exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hcne i))
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal c * V with hW
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
  -- the conjugate is diagonal
  have hVA : V * A * Vᵀ = LDL.diag hA := by
    rw [LDL.diag_eq_lowerInv_conj hA, Matrix.conjTranspose_eq_transpose_of_trivial]
  set e : Fin n → ℝ := LDL.diagEntries hA with he
  have hdiagE : LDL.diag hA = Matrix.diagonal e := rfl
  set d : Fin n → ℝ := fun i => c i * e i * c i with hd
  have hWA : W * A * Wᵀ = Matrix.diagonal d := by
    rw [hW, Matrix.transpose_mul, Matrix.diagonal_transpose]
    calc Matrix.diagonal c * V * A * (Vᵀ * Matrix.diagonal c)
        = Matrix.diagonal c * (V * A * Vᵀ) * Matrix.diagonal c := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal c * Matrix.diagonal e * Matrix.diagonal c := by
          rw [hVA, hdiagE]
      _ = Matrix.diagonal d := by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  -- positivity
  have hWinj : Function.Injective (Wᵀ).mulVec := by
    have : Invertible (Wᵀ) := Matrix.invertibleTranspose W
    exact Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible _)
  have hDpos : (Matrix.diagonal d).PosDef := by
    rw [← hWA]
    have hcast : Wᵀᴴ * A * Wᵀ = W * A * Wᵀ := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    rw [← hcast]
    exact hA.conjTranspose_mul_mul_same hWinj
  have hdpos : ∀ i, 0 < d i := Matrix.posDef_diagonal_iff.1 hDpos
  -- invert
  set L : Matrix (Fin n) (Fin n) ℝ := W⁻¹ with hL
  have hLlow : ∀ i j : Fin n, i < j → L i j = 0 :=
    lower_of_blockTriangular (Matrix.blockTriangular_inv_of_blockTriangular
      (blockTriangular_of_lower hWlow))
  have hLdiag : ∀ i, L i i = 1 := fun i => unitTriangular_inv_diag hWlow hWdiag i
  have hWu : IsUnit W.det := isUnit_det_of_invertible W
  have hWTu : IsUnit (Wᵀ).det := by rw [Matrix.det_transpose]; exact hWu
  have hAeq : A = L * Matrix.diagonal d * Lᵀ := by
    rw [hL, Matrix.transpose_nonsing_inv, ← hWA, Matrix.mul_assoc W A Wᵀ,
      ← Matrix.mul_assoc W⁻¹ W (A * Wᵀ), Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hWTu, Matrix.mul_one]
  refine ⟨Lᵀ, d, hdpos, ?_, ?_, ?_⟩
  · intro i j hji
    exact hLlow j i hji
  · intro i
    exact hLdiag i
  · rw [Matrix.transpose_transpose]
    exact hAeq

/-- **The quadratic form in Jacobi coordinates**: `A[v] = ∑ dᵢ (Uv)ᵢ²`.  This is the identity that
makes a Siegel set a set of explicit inequalities. -/
theorem quadForm_jacobi {A U : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (h : A = Uᵀ * Matrix.diagonal d * U) (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = ∑ i, d i * ((U *ᵥ v) i) ^ 2 := by
  classical
  have hstep : A *ᵥ v = Uᵀ *ᵥ (Matrix.diagonal d *ᵥ (U *ᵥ v)) := by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hstep, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

end GaloisForLFunctions.HTGeometry
