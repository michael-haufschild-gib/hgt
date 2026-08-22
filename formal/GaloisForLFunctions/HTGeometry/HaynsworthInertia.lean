import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Block additivity and Haynsworth inertia additivity

The inertia of a block-diagonal Hermitian matrix is the sum of the inertias of its blocks, and for
an invertible Hermitian corner `A` the Haynsworth additivity formula

`In [[A, B], [Bᴴ, C]] = In A + In (C - Bᴴ A⁻¹ B)`

holds, because the block matrix is congruent to `diag(A, C - Bᴴ A⁻¹ B)` through the unit upper
triangular block matrix `[[1, A⁻¹B],[0,1]]`.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [Fintype n] [Fintype m] in
theorem fromBlocks_diagonal (μ : n → ℝ) (ν : m → ℝ) :
    fromBlocks (diagonal fun i => ((μ i : ℝ) : ℂ)) 0 0 (diagonal fun j => ((ν j : ℝ) : ℂ))
      = diagonal fun x : n ⊕ m => ((Sum.elim μ ν x : ℝ) : ℂ) := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.diagonal, Sum.elim, Matrix.fromBlocks]

theorem isUnit_fromBlocks_zero {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : IsUnit A)
    (hD : IsUnit D) : IsUnit (fromBlocks A 0 0 D) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det A).mp hA).mul ((Matrix.isUnit_iff_isUnit_det D).mp hD)

omit [DecidableEq n] [DecidableEq m] in
theorem fromBlocks_congr (S₁ : Matrix n n ℂ) (S₂ : Matrix m m ℂ) (H₁ : Matrix n n ℂ)
    (H₂ : Matrix m m ℂ) :
    (fromBlocks S₁ 0 0 S₂)ᴴ * fromBlocks H₁ 0 0 H₂ * fromBlocks S₁ 0 0 S₂
      = fromBlocks (S₁ᴴ * H₁ * S₁) 0 0 (S₂ᴴ * H₂ * S₂) := by
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- Every Hermitian matrix is congruent to the real diagonal matrix of its eigenvalues. -/
theorem exists_congr_diagonal {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ S : Matrix n n ℂ, IsUnit S ∧
      Sᴴ * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * S = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : U * Uᴴ = 1 := by
    have h := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [hUdef, Matrix.star_eq_conjTranspose] using h
  refine ⟨Uᴴ, isUnit_conjTranspose (isUnit_eigenvectorUnitary hH), ?_⟩
  rw [← conjTranspose_mul_mul_eigenvectorUnitary hH]
  calc (Uᴴ)ᴴ * (Uᴴ * H * U) * Uᴴ = (U * Uᴴ) * H * (U * Uᴴ) := by
        rw [Matrix.conjTranspose_conjTranspose]
        noncomm_ring
    _ = H := by rw [hU, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq n] [DecidableEq m] in
theorem card_filter_sum_elim_pos (μ : n → ℝ) (ν : m → ℝ) :
    ({x : n ⊕ m | 0 < Sum.elim μ ν x} : Finset (n ⊕ m)).card
      = ({i | 0 < μ i} : Finset n).card + ({j | 0 < ν j} : Finset m).card := by
  classical
  have h : ({x : n ⊕ m | 0 < Sum.elim μ ν x} : Finset (n ⊕ m))
      = (({i | 0 < μ i} : Finset n).disjSum ({j | 0 < ν j} : Finset m)) := by
    ext x
    cases x <;> simp
  rw [h, Finset.card_disjSum]

/-- **Block additivity of the positive index.** -/
theorem posIndex_fromBlocks_zero {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) :
    hermPosIndex (fromBlocks A 0 0 D) = hermPosIndex A + hermPosIndex D := by
  obtain ⟨S₁, hS₁, hA'⟩ := exists_congr_diagonal hA
  obtain ⟨S₂, hS₂, hD'⟩ := exists_congr_diagonal hD
  have hblock : fromBlocks A 0 0 D
      = (fromBlocks S₁ 0 0 S₂)ᴴ *
        (diagonal fun x : n ⊕ m => ((Sum.elim hA.eigenvalues hD.eigenvalues x : ℝ) : ℂ)) *
        fromBlocks S₁ 0 0 S₂ := by
    rw [← fromBlocks_diagonal, fromBlocks_congr, hA', hD']
  rw [hblock, posIndex_conjugate _ (isUnit_fromBlocks_zero hS₁ hS₂), posIndex_diagonal,
    card_filter_sum_elim_pos, ← posIndex_eq_card_pos_eigenvalues hA,
    ← posIndex_eq_card_pos_eigenvalues hD]

/-- **Block additivity of the negative index.** -/
theorem negIndex_fromBlocks_zero {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) :
    hermNegIndex (fromBlocks A 0 0 D) = hermNegIndex A + hermNegIndex D := by
  have hneg : -(fromBlocks A 0 0 D) = fromBlocks (-A) 0 0 (-D) := by
    ext x y
    cases x <;> cases y <;> simp
  rw [hermNegIndex, hneg, posIndex_fromBlocks_zero hA.neg hD.neg, hermNegIndex, hermNegIndex]

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem isHermitian_fromBlocks_zero {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) : (fromBlocks A 0 0 D).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.eq, hD.eq]
  simp

/-- **Block additivity of the null index.** -/
theorem nullIndex_fromBlocks_zero {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) :
    hermNullIndex (fromBlocks A 0 0 D) = hermNullIndex A + hermNullIndex D := by
  have hfull := posIndex_add_negIndex_add_nullIndex (isHermitian_fromBlocks_zero hA hD)
  have hAf := posIndex_add_negIndex_add_nullIndex hA
  have hDf := posIndex_add_negIndex_add_nullIndex hD
  have hcard : Fintype.card (n ⊕ m) = Fintype.card n + Fintype.card m := by simp
  rw [posIndex_fromBlocks_zero hA hD, negIndex_fromBlocks_zero hA hD, hcard] at hfull
  omega

/-- The Hermitian inverse of a Hermitian unit. -/
theorem isHermitian_nonsing_inv {A : Matrix n n ℂ} (hA : A.IsHermitian) : (A⁻¹).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv, hA.eq]

/-- The Schur congruence realizing Haynsworth additivity. -/
theorem fromBlocks_schur_congr {A : Matrix n n ℂ} (hAu : IsUnit A) (hA : A.IsHermitian)
    (B : Matrix n m ℂ) (C : Matrix m m ℂ) :
    (fromBlocks 1 (A⁻¹ * B) 0 1)ᴴ * fromBlocks A 0 0 (C - Bᴴ * A⁻¹ * B) *
        fromBlocks 1 (A⁻¹ * B) 0 1
      = fromBlocks A B Bᴴ C := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hstar : (A⁻¹ * B)ᴴ = Bᴴ * A⁻¹ := by
    rw [Matrix.conjTranspose_mul, (isHermitian_nonsing_inv hA).eq]
  rw [Matrix.fromBlocks_conjTranspose, hstar]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.mul_assoc (Bᴴ) A⁻¹ A, hinvA, Matrix.mul_one,
    ← Matrix.mul_assoc A A⁻¹ B, hAinv, Matrix.one_mul, ← Matrix.mul_assoc Bᴴ A⁻¹ B]
  congr 1
  abel

theorem isUnit_fromBlocks_one_upper (X : Matrix n m ℂ) :
    IsUnit (fromBlocks (1 : Matrix n n ℂ) X 0 (1 : Matrix m m ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  simp

omit [Fintype m] [DecidableEq m] in
theorem isHermitian_schurComplement {A : Matrix n n ℂ} (hA : A.IsHermitian) (B : Matrix n m ℂ)
    {C : Matrix m m ℂ} (hC : C.IsHermitian) : (C - Bᴴ * A⁻¹ * B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hC.eq]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (isHermitian_nonsing_inv hA).eq, Matrix.mul_assoc]

/-- **Haynsworth inertia additivity, positive index.** -/
theorem haynsworth_posIndex {A : Matrix n n ℂ} (hAu : IsUnit A) (hA : A.IsHermitian)
    (B : Matrix n m ℂ) {C : Matrix m m ℂ} (hC : C.IsHermitian) :
    hermPosIndex (fromBlocks A B Bᴴ C)
      = hermPosIndex A + hermPosIndex (C - Bᴴ * A⁻¹ * B) := by
  rw [← fromBlocks_schur_congr hAu hA B C,
    posIndex_conjugate _ (isUnit_fromBlocks_one_upper (A⁻¹ * B)),
    posIndex_fromBlocks_zero hA (isHermitian_schurComplement hA B hC)]

/-- **Haynsworth inertia additivity, negative index.** -/
theorem haynsworth_negIndex {A : Matrix n n ℂ} (hAu : IsUnit A) (hA : A.IsHermitian)
    (B : Matrix n m ℂ) {C : Matrix m m ℂ} (hC : C.IsHermitian) :
    hermNegIndex (fromBlocks A B Bᴴ C)
      = hermNegIndex A + hermNegIndex (C - Bᴴ * A⁻¹ * B) := by
  rw [← fromBlocks_schur_congr hAu hA B C,
    negIndex_conjugate _ (isUnit_fromBlocks_one_upper (A⁻¹ * B)),
    negIndex_fromBlocks_zero hA (isHermitian_schurComplement hA B hC)]

/-- **Haynsworth inertia additivity, null index.** -/
theorem haynsworth_nullIndex {A : Matrix n n ℂ} (hAu : IsUnit A) (hA : A.IsHermitian)
    (B : Matrix n m ℂ) {C : Matrix m m ℂ} (hC : C.IsHermitian) :
    hermNullIndex (fromBlocks A B Bᴴ C)
      = hermNullIndex A + hermNullIndex (C - Bᴴ * A⁻¹ * B) := by
  rw [← fromBlocks_schur_congr hAu hA B C,
    nullIndex_conjugate _ (isUnit_fromBlocks_one_upper (A⁻¹ * B)),
    nullIndex_fromBlocks_zero hA (isHermitian_schurComplement hA B hC)]

end GaloisForLFunctions.HTGeometry
