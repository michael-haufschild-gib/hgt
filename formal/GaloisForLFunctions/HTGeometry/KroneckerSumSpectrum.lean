import GaloisForLFunctions.HTGeometry.SiteFactorLiftedSpectrum

/-!
# Spectrum of a Kronecker sum

Two non-interacting subsystems combine into `X ⊗ I + I ⊗ Y`.  Diagonalizing the
two blocks separately diagonalizes the sum, so its spectrum is exactly the set
of sums of one eigenvalue from each block.

The proof is determinantal: conjugating by the Kronecker product of the two
eigenvector unitaries turns the Kronecker sum into a real diagonal matrix whose
entries are the pairwise sums, and conjugation by a unitary leaves the
characteristic determinant unchanged.
-/

open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem scalar_eq_smul_one {n : Type*} [Fintype n] [DecidableEq n] (μ : ℂ) :
    Matrix.scalar n μ = μ • (1 : Matrix n n ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

omit [Fintype I] [Fintype J] in
theorem isHermitian_kroneckerSum {X : Matrix I I ℂ} {Y : Matrix J J ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (kroneckerSum X Y).IsHermitian := by
  show (kroneckerSum X Y)ᴴ = _
  simp only [kroneckerSum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [hX, hY]

theorem eigenvectorUnitary_mul_conjTranspose {M : Matrix I I ℂ}
    (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix I I ℂ) *
      (hM.eigenvectorUnitary : Matrix I I ℂ)ᴴ = 1 := by
  have h := hM.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- Conjugating a Kronecker sum by the Kronecker product of the two eigenvector
unitaries diagonalizes it. -/
theorem kroneckerSum_eq_conj_diagonal {X : Matrix I I ℂ} {Y : Matrix J J ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    kroneckerSum X Y =
      ((hX.eigenvectorUnitary : Matrix I I ℂ) ⊗ₖ
          (hY.eigenvectorUnitary : Matrix J J ℂ)) *
        Matrix.diagonal (fun p : I × J =>
          ((hX.eigenvalues p.1 : ℂ) + (hY.eigenvalues p.2 : ℂ))) *
        ((hX.eigenvectorUnitary : Matrix I I ℂ) ⊗ₖ
          (hY.eigenvectorUnitary : Matrix J J ℂ))ᴴ := by
  have hU := eigenvectorUnitary_mul_conjTranspose hX
  have hW := eigenvectorUnitary_mul_conjTranspose hY
  have hXeq : X = (hX.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) *
      (hX.eigenvectorUnitary : Matrix I I ℂ)ᴴ := hX.spectral_theorem
  have hYeq : Y = (hY.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun j => (hY.eigenvalues j : ℂ)) *
      (hY.eigenvectorUnitary : Matrix J J ℂ)ᴴ := hY.spectral_theorem
  rw [Matrix.conjTranspose_kronecker,
    ← kroneckerSum_diagonal (fun i => (hX.eigenvalues i : ℂ))
      (fun j => (hY.eigenvalues j : ℂ)),
    kroneckerSum, kroneckerSum, Matrix.mul_add, Matrix.add_mul]
  congr 1
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hW, ← hXeq]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hU, ← hYeq]

/-- **Spectrum of a non-interacting combination.**  The eigenvalues of
`X ⊗ I + I ⊗ Y` are exactly the sums of one eigenvalue of `X` and one of
`Y`. -/
theorem range_eigenvalues_kroneckerSum {X : Matrix I I ℂ} {Y : Matrix J J ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Set.range (isHermitian_kroneckerSum hX hY).eigenvalues =
      Set.range (fun p : I × J =>
        hX.eigenvalues p.1 + hY.eigenvalues p.2) := by
  classical
  set P : Matrix (I × J) (I × J) ℂ :=
    (hX.eigenvectorUnitary : Matrix I I ℂ) ⊗ₖ
      (hY.eigenvectorUnitary : Matrix J J ℂ) with hPdef
  set D : Matrix (I × J) (I × J) ℂ :=
    Matrix.diagonal (fun p : I × J =>
      ((hX.eigenvalues p.1 : ℂ) + (hY.eigenvalues p.2 : ℂ))) with hDdef
  have hP1 : P * Pᴴ = 1 := by
    rw [hPdef, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      eigenvectorUnitary_mul_conjTranspose hX,
      eigenvectorUnitary_mul_conjTranspose hY, Matrix.one_kronecker_one]
  have hdetP : P.det * Pᴴ.det = 1 := by
    rw [← Matrix.det_mul, hP1, Matrix.det_one]
  have hconj : kroneckerSum X Y = P * D * Pᴴ :=
    kroneckerSum_eq_conj_diagonal hX hY
  ext μ
  rw [mem_range_hermitianEigenvalues_iff]
  have hshift : Matrix.scalar (I × J) (μ : ℂ) - kroneckerSum X Y =
      P * (Matrix.scalar (I × J) (μ : ℂ) - D) * Pᴴ := by
    rw [hconj, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    rw [scalar_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hP1]
  have hdiag : Matrix.scalar (I × J) (μ : ℂ) - D =
      Matrix.diagonal (fun p : I × J =>
        (μ : ℂ) - ((hX.eigenvalues p.1 : ℂ) + (hY.eigenvalues p.2 : ℂ))) := by
    rw [hDdef]
    ext x y
    by_cases h : x = y <;>
      simp [Matrix.scalar_apply, h]
  have hdet :
      (Matrix.scalar (I × J) (μ : ℂ) - kroneckerSum X Y).det =
        ∏ p : I × J,
          ((μ : ℂ) -
            ((hX.eigenvalues p.1 : ℂ) + (hY.eigenvalues p.2 : ℂ))) := by
    rw [hshift, Matrix.det_mul, Matrix.det_mul, hdiag, Matrix.det_diagonal]
    calc
      P.det * (∏ p : I × J,
            ((μ : ℂ) -
              ((hX.eigenvalues p.1 : ℂ) + (hY.eigenvalues p.2 : ℂ)))) *
          Pᴴ.det
          = (P.det * Pᴴ.det) *
            ∏ p : I × J,
              ((μ : ℂ) -
                ((hX.eigenvalues p.1 : ℂ) +
                  (hY.eigenvalues p.2 : ℂ))) := by ring
      _ = _ := by rw [hdetP, one_mul]
  rw [hdet, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, -, hp⟩
    refine ⟨p, ?_⟩
    have hval := sub_eq_zero.mp hp
    exact_mod_cast hval.symm
  · rintro ⟨p, rfl⟩
    refine ⟨p, Finset.mem_univ p, ?_⟩
    push_cast
    ring

end

end GaloisForLFunctions.HTGeometry
