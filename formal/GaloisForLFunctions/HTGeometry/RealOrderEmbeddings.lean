import GaloisForLFunctions.HTGeometry.BlockJacobiData

/-!
# Real embeddings diagonalise the regular representation

For an order with `d` real embeddings whose evaluation matrix `Ω` on a `ℤ`-basis is invertible, the
regular representation of a ring element is conjugate by `Ω` to the diagonal matrix of its
embeddings.  Consequently a `d × d` real matrix commutes with every regular representation exactly
when `Ω⁻ᵀ · − · Ω⁻¹` of it is diagonal, which is the coordinate description of the forms on which
multiplication by the order is self-adjoint.

* `RealOrderData` : a `ℤ`-basis together with `d` real embeddings with invertible evaluation matrix.
* `embMatrix_mul_orderEntry` : **the embeddings diagonalise the regular representation.**
* `diagonal_of_commute_diagonal` : a matrix commuting with all diagonal matrices is diagonal.
* `exists_diagonal_of_selfAdjoint` : **the self-adjointness locus is the pullback of the
  diagonal forms along the embedding matrix.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {d : ℕ} {R : Type*} [CommRing R]

/-- A `ℤ`-basis of an order together with `d` real embeddings whose evaluation matrix is
invertible. -/
structure RealOrderData (R : Type*) [CommRing R] (d : ℕ) where
  /-- The `ℤ`-basis. -/
  basis : Module.Basis (Fin d) ℤ R
  /-- The real embeddings. -/
  emb : Fin d → (R →+* ℝ)
  /-- The evaluation matrix is invertible. -/
  invertible : IsUnit (Matrix.of fun v k => emb v (basis k) : Matrix (Fin d) (Fin d) ℝ).det

namespace RealOrderData

variable (T : RealOrderData R d)

/-- The evaluation matrix of the embeddings on the basis. -/
noncomputable def embMatrix : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun v k => T.emb v (T.basis k)

/-- The regular representation of a ring element, over `ℝ`. -/
noncomputable def entryRep (α : R) : Matrix (Fin d) (Fin d) ℝ :=
  (Algebra.leftMulMatrix T.basis α).map (fun z : ℤ => (z : ℝ))

theorem entryRep_apply (α : R) (k' k : Fin d) :
    T.entryRep α k' k = ((T.basis.repr (α * T.basis k) k' : ℤ) : ℝ) := by
  show ((Algebra.leftMulMatrix T.basis α k' k : ℤ) : ℝ) = _
  congr 1
  rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rfl

/-- **The embeddings diagonalise the regular representation.** -/
theorem embMatrix_mul_entryRep (α : R) :
    T.embMatrix * T.entryRep α = Matrix.diagonal (fun v => T.emb v α) * T.embMatrix := by
  classical
  ext v k
  have hL : (T.embMatrix * T.entryRep α) v k
      = ∑ k', T.emb v (T.basis k') * ((T.basis.repr (α * T.basis k) k' : ℤ) : ℝ) := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k' _ => by rw [entryRep_apply]; rfl
  have hR : (Matrix.diagonal (fun v => T.emb v α) * T.embMatrix) v k
      = T.emb v α * T.emb v (T.basis k) := by
    rw [Matrix.mul_apply,
      Finset.sum_eq_single v
        (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hp), zero_mul])
        (fun hcon => absurd (Finset.mem_univ v) hcon),
      Matrix.diagonal_apply_eq]
    rfl
  have hsum : (α * T.basis k) = ∑ k', (T.basis.repr (α * T.basis k) k') • T.basis k' :=
    (T.basis.sum_repr (α * T.basis k)).symm
  have hemb : T.emb v (α * T.basis k)
      = ∑ k', ((T.basis.repr (α * T.basis k) k' : ℤ) : ℝ) * T.emb v (T.basis k') := by
    conv_lhs => rw [hsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k' _ => by
      rw [map_zsmul, zsmul_eq_mul]
  rw [hL, hR, ← map_mul]
  rw [hemb]
  exact Finset.sum_congr rfl fun k' _ => by ring

end RealOrderData

/-- **A matrix commuting with every diagonal matrix is diagonal.** -/
theorem diagonal_of_commute_diagonal {C : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ x : Fin d → ℝ, Matrix.diagonal x * C = C * Matrix.diagonal x) :
    C = Matrix.diagonal (fun v => C v v) := by
  classical
  ext v w
  by_cases hvw : v = w
  · subst hvw
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hvw]
    have hx := congrFun (congrFun (h (Pi.single v 1)) v) w
    have hL : (Matrix.diagonal (Pi.single v (1 : ℝ)) * C) v w = C v w := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single v
          (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hp), zero_mul])
          (fun hcon => absurd (Finset.mem_univ v) hcon),
        Matrix.diagonal_apply_eq]
      simp
    have hR : (C * Matrix.diagonal (Pi.single v (1 : ℝ))) v w = 0 := by
      rw [Matrix.mul_apply,
        Finset.sum_eq_single w
          (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
          (fun hcon => absurd (Finset.mem_univ w) hcon),
        Matrix.diagonal_apply_eq]
      simp [Ne.symm hvw]
    rw [hL, hR] at hx
    exact hx

namespace RealOrderData

variable (T : RealOrderData R d)

theorem entryRep_eq (α : R) :
    T.entryRep α = T.embMatrix⁻¹ * Matrix.diagonal (fun v => T.emb v α) * T.embMatrix := by
  have h := T.embMatrix_mul_entryRep α
  have hu : IsUnit T.embMatrix.det := T.invertible
  calc T.entryRep α = (T.embMatrix⁻¹ * T.embMatrix) * T.entryRep α := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = T.embMatrix⁻¹ * (T.embMatrix * T.entryRep α) := by rw [Matrix.mul_assoc]
    _ = T.embMatrix⁻¹ * (Matrix.diagonal (fun v => T.emb v α) * T.embMatrix) := by rw [h]
    _ = T.embMatrix⁻¹ * Matrix.diagonal (fun v => T.emb v α) * T.embMatrix := by
        rw [Matrix.mul_assoc]

theorem transpose_entryRep_eq (α : R) :
    (T.entryRep α)ᵀ
      = T.embMatrixᵀ * Matrix.diagonal (fun v => T.emb v α) * (T.embMatrixᵀ)⁻¹ := by
  have hu : IsUnit T.embMatrix.det := T.invertible
  rw [entryRep_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.transpose_nonsing_inv]
  rw [Matrix.mul_assoc]

end RealOrderData

/-- **The forms for which multiplication by the order is self-adjoint are exactly the pullbacks of
diagonal forms along the embedding matrix.** -/
theorem exists_diagonal_of_selfAdjoint {T : RealOrderData R d} {B : Matrix (Fin d) (Fin d) ℝ}
    (h : ∀ α : R, (T.entryRep α)ᵀ * B = B * T.entryRep α) :
    ∃ c : Fin d → ℝ, B = T.embMatrixᵀ * Matrix.diagonal c * T.embMatrix := by
  classical
  have hu : IsUnit T.embMatrix.det := T.invertible
  have huT : IsUnit (T.embMatrixᵀ).det := by rw [Matrix.det_transpose]; exact hu
  set C : Matrix (Fin d) (Fin d) ℝ := (T.embMatrixᵀ)⁻¹ * B * T.embMatrix⁻¹ with hC
  have hstep : ∀ α : R, Matrix.diagonal (fun v => T.emb v α) * C
      = C * Matrix.diagonal (fun v => T.emb v α) := by
    intro α
    have hα := h α
    rw [T.transpose_entryRep_eq α, T.entryRep_eq α] at hα
    calc Matrix.diagonal (fun v => T.emb v α) * C
        = ((T.embMatrixᵀ)⁻¹ * (T.embMatrixᵀ * Matrix.diagonal (fun v => T.emb v α)
            * (T.embMatrixᵀ)⁻¹ * B)) * T.embMatrix⁻¹ := by
          rw [hC]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ((T.embMatrixᵀ)⁻¹) (T.embMatrixᵀ), Matrix.nonsing_inv_mul _ huT,
            Matrix.one_mul]
      _ = ((T.embMatrixᵀ)⁻¹ * (B * (T.embMatrix⁻¹ * Matrix.diagonal (fun v => T.emb v α)
            * T.embMatrix))) * T.embMatrix⁻¹ := by rw [hα]
      _ = C * Matrix.diagonal (fun v => T.emb v α) := by
          rw [hC]
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hrows : ∀ v w : Fin d, v ≠ w → ∃ α : R, T.emb v α ≠ T.emb w α := by
    intro v w hvw
    by_contra hcon
    push Not at hcon
    have hrow : T.embMatrix v = T.embMatrix w := funext fun k => hcon (T.basis k)
    exact hu.ne_zero (Matrix.det_zero_of_row_eq hvw hrow)
  have hCoff : ∀ v w : Fin d, v ≠ w → C v w = 0 := by
    intro v w hvw
    obtain ⟨α, hα⟩ := hrows v w hvw
    have h1 := congrFun (congrFun (hstep α) v) w
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have hne : T.emb v α - T.emb w α ≠ 0 := sub_ne_zero.2 hα
    have hzero : (T.emb v α - T.emb w α) * C v w = 0 := by linarith [h1]
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hne
    · exact h
  have hdiagC : C = Matrix.diagonal (fun v => C v v) := by
    ext v w
    by_cases hvw : v = w
    · subst hvw
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hvw]
      exact hCoff v w hvw
  refine ⟨fun v => C v v, ?_⟩
  rw [← hdiagC, hC]
  symm
  calc T.embMatrixᵀ * ((T.embMatrixᵀ)⁻¹ * B * T.embMatrix⁻¹) * T.embMatrix
      = (T.embMatrixᵀ * (T.embMatrixᵀ)⁻¹) * B * (T.embMatrix⁻¹ * T.embMatrix) := by
        simp only [Matrix.mul_assoc]
    _ = B := by
        rw [Matrix.mul_nonsing_inv _ huT, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
          Matrix.mul_one]

end GaloisForLFunctions.HTGeometry
