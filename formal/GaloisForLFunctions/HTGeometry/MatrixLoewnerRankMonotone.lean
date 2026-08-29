import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone

/-!
# Rank monotonicity on the finite positive cone

Loewner domination of finite positive-semidefinite matrices implies domination of algebraic
matrix rank.  The proof is kernel inclusion plus rank-nullity and works on arbitrary finite index
types.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The range of matrix multiplication is exactly the span of its columns. -/
theorem range_mulVecLin_eq_span_cols (A : Matrix n n ℂ) :
    A.mulVecLin.range = Submodule.span ℂ (Set.range A.col) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [show A.mulVecLin x = ∑ j, x j • A.col j by
      ext i
      simp [Matrix.mulVec, dotProduct,
        Matrix.col_apply, mul_comm]]
    apply Submodule.sum_mem
    intro j _hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let e : n → ℂ := fun i => if i = j then 1 else 0
    refine ⟨e, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, e,
      Matrix.col_apply]

/-- Matrix rank is the finite dimension of the `mulVec` range. -/
theorem matrix_rank_eq_finrank_range_mulVecLin (A : Matrix n n ℂ) :
    A.rank = Module.finrank ℂ A.mulVecLin.range := by
  rw [range_mulVecLin_eq_span_cols]
  exact Matrix.rank_eq_finrank_span_cols A

/-- Left multiplication by an invertible square matrix preserves rank. -/
theorem rank_mul_eq_of_isUnit_left (C D : Matrix n n ℂ) (hC : IsUnit C) :
    (C * D).rank = D.rank := by
  have hdet : IsUnit C.det := C.isUnit_iff_isUnit_det.mp hC
  have hrecover : C⁻¹ * (C * D) = D := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul C hdet, Matrix.one_mul]
  have hlower := Matrix.rank_mul_le_right C⁻¹ (C * D)
  rw [hrecover] at hlower
  exact le_antisymm (Matrix.rank_mul_le_right C D) hlower

/-- Right multiplication by an invertible square matrix preserves rank. -/
theorem rank_mul_eq_of_isUnit_right (D C : Matrix n n ℂ) (hC : IsUnit C) :
    (D * C).rank = D.rank := by
  have hdet : IsUnit C.det := C.isUnit_iff_isUnit_det.mp hC
  have hrecover : (D * C) * C⁻¹ = D := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv C hdet, Matrix.mul_one]
  have hlower := Matrix.rank_mul_le_left (D * C) C⁻¹
  rw [hrecover] at hlower
  exact le_antisymm (Matrix.rank_mul_le_left D C) hlower

/-- Invertible congruence preserves matrix rank. -/
theorem rank_mul_mul_conjTranspose_eq_of_isUnit
    (C D : Matrix n n ℂ) (hC : IsUnit C) :
    (C * D * Cᴴ).rank = D.rank := by
  rw [rank_mul_eq_of_isUnit_right (C * D) Cᴴ hC.star,
    rank_mul_eq_of_isUnit_left C D hC]

/-- Loewner domination is rank monotone on finite positive-semidefinite matrices. -/
theorem rank_le_rank_of_posSemidef_sub
    {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hsub : (B - A).PosSemidef) :
    A.rank ≤ B.rank := by
  have hker : B.mulVecLin.ker ≤ A.mulVecLin.ker := by
    intro x hx
    have hBx : B *ᵥ x = 0 := hx
    have hqB : star x ⬝ᵥ B *ᵥ x = 0 := by rw [hBx]; simp
    have hqA_nonneg : 0 ≤ star x ⬝ᵥ A *ᵥ x := hA.dotProduct_mulVec_nonneg x
    have hqsub_nonneg : 0 ≤ star x ⬝ᵥ (B - A) *ᵥ x :=
      hsub.dotProduct_mulVec_nonneg x
    have hqsub : star x ⬝ᵥ (B - A) *ᵥ x =
        (star x ⬝ᵥ B *ᵥ x) - (star x ⬝ᵥ A *ᵥ x) := by
      simp [dotProduct, Matrix.sub_mulVec, Finset.sum_sub_distrib, mul_sub]
    rw [hqsub, hqB, zero_sub] at hqsub_nonneg
    have hqA_nonpos : star x ⬝ᵥ A *ᵥ x ≤ 0 := neg_nonneg.mp hqsub_nonneg
    have hqA : star x ⬝ᵥ A *ᵥ x = 0 := le_antisymm hqA_nonpos hqA_nonneg
    exact (hA.dotProduct_mulVec_zero_iff x).mp hqA
  have hkerFin : Module.finrank ℂ B.mulVecLin.ker ≤
      Module.finrank ℂ A.mulVecLin.ker := Submodule.finrank_mono hker
  have hA_nullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hB_nullity := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [← matrix_rank_eq_finrank_range_mulVecLin] at hA_nullity hB_nullity
  omega

end

end GaloisForLFunctions.HTGeometry
