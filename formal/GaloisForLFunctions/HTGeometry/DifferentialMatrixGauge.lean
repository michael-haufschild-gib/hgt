import Mathlib

/-!
# Matrix calculus for a derivation, and the Galois cocycle of a fundamental matrix

Componentwise differentiation of matrices obeys the Leibniz rule, so a constant matrix passes
through it.  The consequence used by differential Galois theory is the *cocycle*: if `M` is a
fundamental matrix of `δ Y = Y A` with `det M = 1` and `φ` is a differential automorphism of the
ring fixing `A`, then `φ` moves `M` by left multiplication with a constant matrix of determinant
one.  Conversely a constant gauge sends solutions to solutions.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- Componentwise differentiation of a matrix. -/
def matDeriv {m n : Type*} (M : Matrix m n R) : Matrix m n R :=
  Matrix.of fun i j => (M i j)′

@[simp] theorem matDeriv_apply {m n : Type*} (M : Matrix m n R) (i : m) (j : n) :
    matDeriv M i j = (M i j)′ := rfl

/-- **Leibniz rule for matrix multiplication.** -/
theorem matDeriv_mul {m n p : Type*} [Fintype n] (M : Matrix m n R) (P : Matrix n p R) :
    matDeriv (M * P) = matDeriv M * P + M * matDeriv P := by
  ext i j
  simp only [matDeriv_apply, Matrix.mul_apply, Matrix.add_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

/-- A constant matrix passes through componentwise differentiation. -/
theorem matDeriv_const_mul {m n p : Type*} [Fintype n] (g : Matrix m n R)
    (hg : ∀ i j, (g i j)′ = 0) (M : Matrix n p R) :
    matDeriv (g * M) = g * matDeriv M := by
  rw [matDeriv_mul]
  have hz : matDeriv g = 0 := by
    ext i j
    simp [hg i j]
  rw [hz, Matrix.zero_mul, zero_add]

/-- A differential ring homomorphism commutes with componentwise differentiation. -/
theorem matDeriv_map {m n : Type*} (M : Matrix m n R) (φ : R →+* R)
    (hφ : ∀ x : R, φ (x′) = (φ x)′) : matDeriv (M.map φ) = (matDeriv M).map φ := by
  ext i j
  simp [Matrix.map_apply, hφ]

/-- **A constant gauge preserves the solutions of a linear system.** -/
theorem matDeriv_gauge {N : ℕ} (M A g : Matrix (Fin N) (Fin N) R)
    (hM : matDeriv M = M * A) (hg : ∀ i j, (g i j)′ = 0) :
    matDeriv (g * M) = (g * M) * A := by
  rw [matDeriv_const_mul g hg, hM, Matrix.mul_assoc]

/-- **The Galois cocycle.**  A differential automorphism fixing the system matrix moves a
normalized fundamental matrix by left multiplication with a constant matrix of determinant one. -/
theorem exists_constantGauge_of_differentialAut {N : ℕ} (M A : Matrix (Fin N) (Fin N) R)
    (hM : matDeriv M = M * A) (hdet : M.det = 1)
    (φ : R ≃+* R) (hφ : ∀ x : R, φ (x′) = (φ x)′) (hA : A.map (φ : R →+* R) = A) :
    ∃ Z : Matrix (Fin N) (Fin N) R,
      (∀ i j, (Z i j)′ = 0) ∧ M.map (φ : R →+* R) = Z * M ∧ Z.det = 1 := by
  classical
  have hunit : IsUnit M.det := by rw [hdet]; exact isUnit_one
  refine ⟨M.map (φ : R →+* R) * M⁻¹, ?_, ?_, ?_⟩
  · -- constancy
    have hZM : (M.map (φ : R →+* R) * M⁻¹) * M = M.map (φ : R →+* R) := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
    have h1 : matDeriv ((M.map (φ : R →+* R) * M⁻¹) * M)
        = matDeriv (M.map (φ : R →+* R) * M⁻¹) * M
          + (M.map (φ : R →+* R) * M⁻¹) * (M * A) := by
      rw [matDeriv_mul, hM]
    have h2 : matDeriv (M.map (φ : R →+* R)) = (M.map (φ : R →+* R)) * A := by
      rw [matDeriv_map M (φ : R →+* R) hφ, hM, Matrix.map_mul, hA]
    have h3 : matDeriv (M.map (φ : R →+* R) * M⁻¹) * M = 0 := by
      have := h1
      rw [hZM, h2] at this
      have hassoc : (M.map (φ : R →+* R) * M⁻¹) * (M * A)
          = (M.map (φ : R →+* R)) * A := by
        rw [← Matrix.mul_assoc, hZM]
      rw [hassoc] at this
      have h6 := congrArg
        (fun X : Matrix (Fin N) (Fin N) R => X - (M.map (φ : R →+* R)) * A) this
      simp only [add_sub_cancel_right, sub_self] at h6
      exact h6.symm
    have h4 : matDeriv (M.map (φ : R →+* R) * M⁻¹) = 0 := by
      have := congrArg (fun X => X * M⁻¹) h3
      simp only [Matrix.zero_mul] at this
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one] at this
    intro i j
    have := congrFun (congrFun h4 i) j
    simpa using this
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  · have hmapdet : (M.map (φ : R →+* R)).det = 1 := by
      have hd : (φ : R →+* R) M.det = (M.map (φ : R →+* R)).det := by
        rw [RingHom.map_det (φ : R →+* R) M, RingHom.mapMatrix_apply]
      rw [← hd, hdet, map_one]
    have hinvdet : (M⁻¹).det = 1 := by
      rw [Matrix.det_nonsing_inv, hdet]
      simp
    rw [Matrix.det_mul, hmapdet, hinvdet, one_mul]

end

end GaloisForLFunctions.HTGeometry
