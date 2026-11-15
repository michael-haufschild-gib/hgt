import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFullMomentFrames

/-!
# Centered affine frames on nonconstant binary moments

Removing the constant coordinate from the full affine matrix gives the
linear map on centered moments. Its diagonal blocks are the homogeneous
shears, so translation leaves both its determinant and the selected
diagonal-block determinants unchanged.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Nonconstant binary monomials, ordered by total degree and then vertical degree. -/
abbrev BinaryIndex (k : ℕ) := Σ d : Fin k, Fin (d.val + 2)
abbrev FlatBinarySpace (k : ℕ) := BinaryIndex k → ℝ

/-- Include a positive-degree monomial in the full monomial index. -/
def positiveBinaryIndex {k : ℕ} (a : BinaryIndex k) : FullBinaryIndex k :=
  ⟨a.1.succ, a.2⟩

/-- The full nonconstant moment map in scalar coordinates. -/
def flatBinaryMoment (k : ℕ) (x z : ℝ) : FlatBinarySpace k :=
  fun a => x ^ (a.1.val + 1 - a.2.val) * z ^ a.2.val

private theorem sum_fullBinaryIndex {R : Type*} [AddCommMonoid R] (k : ℕ)
    (f : FullBinaryIndex k → R) :
    ∑ a, f a = f ⟨0, 0⟩ + ∑ a : BinaryIndex k, f (positiveBinaryIndex a) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_succ]
  rw [Fintype.sum_sigma]
  apply congrArg₂ (· + ·)
  · exact Fin.sum_univ_one (fun j : Fin 1 => f ⟨0, j⟩)
  · rfl

/-- Restrict the full affine matrix to nonconstant monomials. -/
def affineBinaryMatrix (k : ℕ) (θ t : ℝ) : Matrix (BinaryIndex k) (BinaryIndex k) ℝ :=
  (fullAffineMatrix k θ t).submatrix positiveBinaryIndex positiveBinaryIndex

private theorem restrict_full_mulVec (k : ℕ) (M : Matrix (FullBinaryIndex k) (FullBinaryIndex k) ℝ)
    (x z : ℝ) (a : BinaryIndex k) :
    (M *ᵥ (fullBinaryMoment k x z - fullBinaryMoment k 0 0)) (positiveBinaryIndex a) =
      (M.submatrix positiveBinaryIndex positiveBinaryIndex *ᵥ flatBinaryMoment k x z) a := by
  change (∑ b, M (positiveBinaryIndex a) b *
    (fullBinaryMoment k x z b - fullBinaryMoment k 0 0 b)) = _
  rw [sum_fullBinaryIndex]
  have hconst (u v : ℝ) : fullBinaryMoment k u v ⟨0, 0⟩ = 1 := by
    simp only [fullBinaryMoment, Fin.val_zero, Nat.zero_sub, pow_zero, mul_one]
  have hzero (b : BinaryIndex k) : fullBinaryMoment k 0 0 (positiveBinaryIndex b) = 0 := by
    rw [fullBinaryMoment_zero]
    apply if_neg
    change b.1.val + 1 ≠ 0
    omega
  simp only [hconst, hzero, sub_self, mul_zero, zero_add, sub_zero]
  rfl

/-- The restricted matrix implements the actual affine action after subtracting its base point. -/
theorem affineBinaryMatrix_moment (k : ℕ) (θ t x z : ℝ) :
    affineBinaryMatrix k θ t *ᵥ flatBinaryMoment k x z =
      flatBinaryMoment k x (z + θ * x + t) - flatBinaryMoment k 0 t := by
  have h : fullAffineMatrix k θ t *ᵥ
      (fullBinaryMoment k x z - fullBinaryMoment k 0 0) =
      fullBinaryMoment k x (z + θ * x + t) - fullBinaryMoment k 0 t := by
    change Matrix.toLin' (fullAffineMatrix k θ t) _ = _
    rw [map_sub]
    change fullAffineMatrix k θ t *ᵥ fullBinaryMoment k x z -
      fullAffineMatrix k θ t *ᵥ fullBinaryMoment k 0 0 = _
    rw [fullAffine_moment, fullAffine_moment]
    simp only [mul_zero, add_zero, zero_add]
  funext a
  have ha := congrFun h (positiveBinaryIndex a)
  rw [restrict_full_mulVec] at ha
  exact ha

/-- Higher-degree columns vanish in every lower-degree row. -/
theorem affineBinaryMatrix_lower (k : ℕ) (θ t : ℝ) :
    ∀ a b : BinaryIndex k, a.1 < b.1 → affineBinaryMatrix k θ t a b = 0 := by
  intro a b hab
  apply fullAffine_lower k θ t (positiveBinaryIndex a) (positiveBinaryIndex b)
  change a.1.val + 1 < b.1.val + 1
  have hab' : a.1.val < b.1.val := hab
  omega

/-- Translation leaves each homogeneous diagonal block equal to its pure shear. -/
theorem affineBinaryMatrix_diagonalBlock (k : ℕ) (θ t : ℝ) (d : Fin k) :
    diagonalBlock (affineBinaryMatrix k θ t) d = shearBlock (d.val + 2) θ :=
  fullAffine_diagonalBlock k θ t d.succ

/-- Centering and removing the constant coordinate preserve determinant one. -/
theorem det_affineBinaryMatrix (k : ℕ) (θ t : ℝ) : (affineBinaryMatrix k θ t).det = 1 := by
  rw [det_of_lower _ (affineBinaryMatrix_lower k θ t)]
  simp only [affineBinaryMatrix_diagonalBlock, det_shearBlock, Finset.prod_const_one]

/-- Without vertical translation the centered affine matrix is the direct sum of pure shears. -/
theorem affineBinaryMatrix_zero_translation (k : ℕ) (θ : ℝ) :
    affineBinaryMatrix k θ 0 =
      Matrix.blockDiagonal' (fun d : Fin k => shearBlock (d.val + 2) θ) := by
  classical
  unfold affineBinaryMatrix fullAffineMatrix
  rw [fullTranslation_zero, one_mul]
  ext ⟨d, i⟩ ⟨e, j⟩
  change Matrix.blockDiagonal' (fun d : Fin (k + 1) => shearBlock (d.val + 1) θ)
      ⟨d.succ, i⟩ ⟨e.succ, j⟩ = _
  by_cases h : d = e
  · subst e
    simp only [Matrix.blockDiagonal'_apply_eq, Fin.val_succ]
  · have h' : d.succ ≠ e.succ := by
      intro he
      apply h
      apply Fin.ext
      exact Nat.succ.inj (congrArg Fin.val he)
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne _ _ _ h]

#print axioms affineBinaryMatrix_moment
#print axioms affineBinaryMatrix_lower
#print axioms affineBinaryMatrix_diagonalBlock
#print axioms det_affineBinaryMatrix
#print axioms affineBinaryMatrix_zero_translation

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
