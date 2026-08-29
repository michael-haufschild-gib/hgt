import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-!
# Finite Hermitian shifted resolvents

Spectral formulas and positivity facts for regularized inverses of finite Hermitian matrices.
These lemmas isolate the finite-dimensional cutoff calculus used in matrix-valued Ward limits.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral formula for a real scalar shift of a finite Hermitian matrix. -/
theorem shiftedHermitian_inv_eq_spectral {H : Matrix n n ℂ} (hH : H.IsHermitian) (c : ℝ)
    (hc : ∀ i, hH.eigenvalues i + c ≠ 0) :
    (H + (c : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
      (hH.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) *
        (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  change (H + (c : ℂ) • (1 : Matrix n n ℂ))⁻¹ =
    U * diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) * Uᴴ
  apply Matrix.inv_eq_right_inv
  have hspec : H =
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by
    simpa [U, Matrix.star_eq_conjTranspose] using isHermitian_eq_conj_diagonal hH
  have hUU : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.eigenvectorUnitary.property).1
  have hUU' : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.mem_iff.mp hH.eigenvectorUnitary.property).2
  have hshift :
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (1 : Matrix n n ℂ) =
        U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ := by
    calc
      U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (1 : Matrix n n ℂ) =
        U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ +
          (c : ℂ) • (U * Uᴴ) := by rw [hUU']
      _ = U * (diagonal (fun i => (hH.eigenvalues i : ℂ)) +
          (c : ℂ) • (1 : Matrix n n ℂ)) * Uᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul]
      _ = U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
  have hshiftH : H + (c : ℂ) • (1 : Matrix n n ℂ) =
      U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)) * Uᴴ :=
    (congrArg (fun Z => Z + (c : ℂ) • (1 : Matrix n n ℂ)) hspec).trans hshift
  rw [hshiftH]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc
      (U * diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ))) Uᴴ U,
    show Uᴴ * U = 1 from hUU, Matrix.mul_one,
    Matrix.mul_assoc U
      (diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ)))
      (diagonal (fun i => (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ))),
    Matrix.diagonal_mul_diagonal]
  have hdiag :
      diagonal (fun i => ((hH.eigenvalues i + c : ℝ) : ℂ) *
        (((hH.eigenvalues i + c)⁻¹ : ℝ) : ℂ)) = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq, one_apply_eq, Complex.ofReal_inv,
        Complex.ofReal_add]
      exact mul_inv_cancel₀ (by exact_mod_cast hc i)
    · simp [hij]
  rw [hdiag, Matrix.mul_one, hUU']

end

end GaloisForLFunctions.HTGeometry
