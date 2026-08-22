import GaloisForLFunctions.HTGeometry.HaynsworthInertia
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia

/-!
# Positive rescaling, block swaps, and full positive index

Three elementary consequences of Sylvester's law that are needed when computing inertias of
explicit block matrices: the inertia is unchanged by multiplication with a positive real scalar,
by the block swap congruence `[[0,1],[1,0]]`, and a matrix whose positive index is the full
dimension is positive definite on the whole space.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] in
theorem hermQuad_smul (c : ℝ) (H : Matrix n n ℂ) (x : n → ℂ) :
    hermQuad ((c : ℂ) • H) x = c * hermQuad H x := by
  simp only [hermQuad, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [DecidableEq n] in
/-- Positive rescaling preserves the positive index. -/
theorem posIndex_smul_pos {c : ℝ} (hc : 0 < c) (H : Matrix n n ℂ) :
    hermPosIndex ((c : ℂ) • H) = hermPosIndex H := by
  have hset : hermPosIndexSet ((c : ℂ) • H) = hermPosIndexSet H := by
    ext d
    constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W, rfl, fun x hx hx0 => ?_⟩
      have := hW x hx hx0
      rw [hermQuad_smul] at this
      nlinarith
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W, rfl, fun x hx hx0 => ?_⟩
      rw [hermQuad_smul]
      exact mul_pos hc (hW x hx hx0)
  rw [hermPosIndex, hermPosIndex, hset]

omit [DecidableEq n] in
/-- Positive rescaling preserves the negative index. -/
theorem negIndex_smul_pos {c : ℝ} (hc : 0 < c) (H : Matrix n n ℂ) :
    hermNegIndex ((c : ℂ) • H) = hermNegIndex H := by
  have h : -((c : ℂ) • H) = (c : ℂ) • (-H) := by rw [smul_neg]
  rw [hermNegIndex, h, posIndex_smul_pos hc, hermNegIndex]

section Reindex

variable {n' : Type*} [Fintype n'] [DecidableEq n']

/-- The matrix of a bijection between index types. -/
def equivMatrix (e : n' ≃ n) : Matrix n n' ℂ := (1 : Matrix n n ℂ).submatrix id e

omit [Fintype n] [Fintype n'] [DecidableEq n'] in
theorem equivMatrix_conjTranspose (e : n' ≃ n) :
    (equivMatrix e)ᴴ = (1 : Matrix n n ℂ).submatrix e id := by
  ext i a
  simp [equivMatrix, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

omit [DecidableEq n'] in
theorem equivMatrix_mul_conjTranspose (e : n' ≃ n) :
    equivMatrix e * (equivMatrix e)ᴴ = 1 := by
  rw [equivMatrix_conjTranspose, equivMatrix]
  have h := Matrix.submatrix_mul_equiv (1 : Matrix n n ℂ) (1 : Matrix n n ℂ)
    (Equiv.refl n) e (Equiv.refl n)
  simp

omit [Fintype n'] [DecidableEq n'] in
theorem conjTranspose_mul_mul_equivMatrix (H : Matrix n n ℂ) (e : n' ≃ n) :
    (equivMatrix e)ᴴ * H * equivMatrix e = H.submatrix e e := by
  rw [equivMatrix_conjTranspose, equivMatrix]
  have h1 := Matrix.submatrix_mul_equiv (1 : Matrix n n ℂ) H (e : n' ≃ n) (Equiv.refl n)
    (Equiv.refl n)
  have h2 := Matrix.submatrix_mul_equiv H (1 : Matrix n n ℂ) (e : n' ≃ n) (Equiv.refl n) e
  simp only [Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.one_mul] at h1
  simp only [Equiv.coe_refl, Matrix.mul_one] at h2
  rw [h1, h2]

omit [DecidableEq n'] in
/-- **Reindexing by a bijection preserves the positive index.** -/
theorem posIndex_submatrix_equiv (H : Matrix n n ℂ) (e : n' ≃ n) :
    hermPosIndex (H.submatrix e e) = hermPosIndex H := by
  rw [← conjTranspose_mul_mul_equivMatrix H e]
  have hiso : ((equivMatrix e)ᴴ)ᴴ * (equivMatrix e)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact equivMatrix_mul_conjTranspose e
  have := posIndex_isometric_congr (C := (equivMatrix e)ᴴ) hiso H
  rw [Matrix.conjTranspose_conjTranspose] at this
  exact this

omit [DecidableEq n'] in
/-- **Reindexing by a bijection preserves the negative index.** -/
theorem negIndex_submatrix_equiv (H : Matrix n n ℂ) (e : n' ≃ n) :
    hermNegIndex (H.submatrix e e) = hermNegIndex H := by
  have h : -(H.submatrix e e) = (-H).submatrix e e := by ext i j; simp
  rw [hermNegIndex, h, posIndex_submatrix_equiv, hermNegIndex]

/-- **The block swap preserves the positive index.** -/
theorem posIndex_swapBlocks (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) :
    hermPosIndex (fromBlocks D C B A) = hermPosIndex (fromBlocks A B C D) := by
  have hsub : (fromBlocks A B C D).submatrix (Equiv.sumComm m n) (Equiv.sumComm m n)
      = fromBlocks D C B A := by
    ext x y
    cases x <;> cases y <;> rfl
  rw [← hsub, posIndex_submatrix_equiv]

/-- **The block swap preserves the negative index.** -/
theorem negIndex_swapBlocks (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (D : Matrix m m ℂ) :
    hermNegIndex (fromBlocks D C B A) = hermNegIndex (fromBlocks A B C D) := by
  have hsub : (fromBlocks A B C D).submatrix (Equiv.sumComm m n) (Equiv.sumComm m n)
      = fromBlocks D C B A := by
    ext x y
    cases x <;> cases y <;> rfl
  rw [← hsub, negIndex_submatrix_equiv]

end Reindex

omit [DecidableEq n] in
/-- A matrix whose positive index is the full dimension is positive definite. -/
theorem isPosDefOn_top_of_posIndex_eq_card {H : Matrix n n ℂ}
    (h : hermPosIndex H = Fintype.card n) : IsPosDefOn H ⊤ := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex H
  have htop : W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrank, h, Module.finrank_fintype_fun_eq_card]
  rw [htop] at hW
  exact hW

omit [DecidableEq n] in
/-- An invertible matrix has trivial null index. -/
theorem nullIndex_eq_zero_of_isUnit [DecidableEq n] {H : Matrix n n ℂ} (h : IsUnit H) :
    hermNullIndex H = 0 := by
  have hker : LinearMap.ker H.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact mulVecLin_injective h
  rw [hermNullIndex, hker]
  simp

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem isHermitian_fromBlocks {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) (B : Matrix n m ℂ) : (fromBlocks A B Bᴴ D).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose, hA.eq, hD.eq,
    Matrix.conjTranspose_conjTranspose]

/-- **The block swap preserves the null index of a Hermitian block matrix.** -/
theorem nullIndex_swapBlocks {A : Matrix n n ℂ} {D : Matrix m m ℂ} (hA : A.IsHermitian)
    (hD : D.IsHermitian) (B : Matrix n m ℂ) :
    hermNullIndex (fromBlocks D (Bᴴ) B A) = hermNullIndex (fromBlocks A B (Bᴴ) D) := by
  have hswap : fromBlocks D (Bᴴ) B A = fromBlocks D (Bᴴ) ((Bᴴ)ᴴ) A := by
    rw [Matrix.conjTranspose_conjTranspose]
  have h1 := posIndex_add_negIndex_add_nullIndex (isHermitian_fromBlocks hA hD B)
  have h2 := posIndex_add_negIndex_add_nullIndex (hswap ▸ isHermitian_fromBlocks hD hA (Bᴴ))
  have hp := posIndex_swapBlocks A B (Bᴴ) D
  have hn := negIndex_swapBlocks A B (Bᴴ) D
  have hcard : Fintype.card (m ⊕ n) = Fintype.card (n ⊕ m) := by simp [Nat.add_comm]
  rw [hcard] at h2
  omega

omit [DecidableEq n] in
theorem nullIndex_neg (H : Matrix n n ℂ) : hermNullIndex (-H) = hermNullIndex H := by
  have hker : LinearMap.ker (-H).mulVecLin = LinearMap.ker H.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.neg_mulVec, neg_eq_zero]
  rw [hermNullIndex, hermNullIndex, hker]

end GaloisForLFunctions.HTGeometry
