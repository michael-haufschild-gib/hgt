import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovFullAxisFrames

/-!
# Centered affine coordinate-direction frames in every dimension

Restricting the full affine matrix to positive total degrees gives the
actual centered moment action. Its homogeneous blocks are the binary-chain
shears, independently of vertical translation, and its determinant is one.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Scalar coordinates for all nonconstant moments in `r+2` variables through degree `k`. -/
abbrev AffineAxisIndex (r k : ℕ) := Σ d : Fin k, HomogeneousAxisIndex r (d.val + 1)
abbrev AffineAxisSpace (r k : ℕ) := AffineAxisIndex r k → ℝ

def positiveAxisIndex {r k : ℕ} (a : AffineAxisIndex r k) : FullAxisIndex r k :=
  ⟨a.1.succ, a.2⟩

/-- The nonconstant polynomial moment map in scalar coordinates. -/
def affineAxisMoment (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ) : AffineAxisSpace r k :=
  fun a => fullAxisMoment r k y x z (positiveAxisIndex a)

/-- The nonconstant principal matrix of the full affine moment action. -/
def affineAxisMatrix (r k : ℕ) (θ t : ℝ) : Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ :=
  (fullAxisAffineMatrix r k θ t).submatrix positiveAxisIndex positiveAxisIndex

/-- Removing the constant input coordinate is the principal restriction on centered moment vectors. -/
theorem restrict_fullAxis_mulVec (r k : ℕ)
    (M : Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ)
    (y : Fin r → ℝ) (x z : ℝ) (a : AffineAxisIndex r k) :
    (M *ᵥ (fullAxisMoment r k y x z - fullAxisMoment r k 0 0 0)) (positiveAxisIndex a) =
      (M.submatrix positiveAxisIndex positiveAxisIndex *ᵥ affineAxisMoment r k y x z) a := by
  change (∑ b, M (positiveAxisIndex a) b *
    (fullAxisMoment r k y x z b - fullAxisMoment r k 0 0 0 b)) =
      ∑ b : AffineAxisIndex r k, M (positiveAxisIndex a) (positiveAxisIndex b) * affineAxisMoment r k y x z b
  rw [Fintype.sum_sigma, Fin.sum_univ_succ]
  have hconst (y' : Fin r → ℝ) (x' z' : ℝ) (b : HomogeneousAxisIndex r 0) :
      fullAxisMoment r k y' x' z' ⟨0, b⟩ = 1 := fullAxisMoment_degree_zero r k y' x' z' _ rfl
  have hzero (d : Fin k) (b : HomogeneousAxisIndex r (d.val + 1)) :
      fullAxisMoment r k 0 0 0 ⟨d.succ, b⟩ = 0 := by
    rw [fullAxisMoment_zero]
    apply if_neg
    change d.val + 1 ≠ 0
    omega
  simp only [hconst, hzero, sub_self, mul_zero, Finset.sum_const_zero, zero_add, sub_zero]
  conv_rhs => rw [Fintype.sum_sigma]
  rfl

/-- The matrix realizes the physical affine action after subtracting its base point. -/
theorem affineAxisMatrix_moment (r k : ℕ) (θ t : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    affineAxisMatrix r k θ t *ᵥ affineAxisMoment r k y x z =
      affineAxisMoment r k y x (z + θ * x + t) - affineAxisMoment r k 0 0 t := by
  have h : fullAxisAffineMatrix r k θ t *ᵥ
      (fullAxisMoment r k y x z - fullAxisMoment r k 0 0 0) =
      fullAxisMoment r k y x (z + θ * x + t) - fullAxisMoment r k 0 0 t := by
    change Matrix.toLin' (fullAxisAffineMatrix r k θ t) _ = _
    rw [map_sub]
    change fullAxisAffineMatrix r k θ t *ᵥ fullAxisMoment r k y x z -
      fullAxisAffineMatrix r k θ t *ᵥ fullAxisMoment r k 0 0 0 = _
    rw [fullAxisAffine_moment, fullAxisAffine_moment]
    simp only [mul_zero, add_zero, zero_add]
  funext a
  have ha := congrFun h (positiveAxisIndex a)
  rw [restrict_fullAxis_mulVec] at ha
  exact ha

theorem affineAxisMatrix_lower (r k : ℕ) (θ t : ℝ) :
    ∀ a b : AffineAxisIndex r k, a.1 < b.1 → affineAxisMatrix r k θ t a b = 0 := by
  intro a b hab
  apply fullAxisAffine_lower r k θ t (positiveAxisIndex a) (positiveAxisIndex b)
  change a.1.val + 1 < b.1.val + 1
  have hab' : a.1.val < b.1.val := hab
  omega

/-- The homogeneous diagonal blocks retain their binary chain decomposition under every shift. -/
theorem affineAxisMatrix_diagonalBlock (r k : ℕ) (θ t : ℝ) (d : Fin k) :
    diagonalBlock (affineAxisMatrix r k θ t) d = homogeneousAxisShearMatrix r (d.val + 1) θ :=
  fullAxisAffine_diagonalBlock r k θ t d.succ

theorem det_affineAxisMatrix (r k : ℕ) (θ t : ℝ) : (affineAxisMatrix r k θ t).det = 1 := by
  rw [det_of_lower _ (affineAxisMatrix_lower r k θ t)]
  simp only [affineAxisMatrix_diagonalBlock, homogeneousAxisShearMatrix,
    GaloisForLFunctions.HTGeometry.det_blockDiagonal', det_shearBlock, Finset.prod_const_one]

/-- Zero vertical shift leaves a direct sum of homogeneous shear matrices. -/
theorem affineAxisMatrix_zero_translation (r k : ℕ) (θ : ℝ) :
    affineAxisMatrix r k θ 0 =
      Matrix.blockDiagonal' (fun d : Fin k => homogeneousAxisShearMatrix r (d.val + 1) θ) := by
  unfold affineAxisMatrix fullAxisAffineMatrix
  rw [fullAxisTranslation_zero, one_mul]
  ext ⟨d, a⟩ ⟨e, b⟩
  change Matrix.blockDiagonal' (fun d : Fin (k + 1) => homogeneousAxisShearMatrix r d.val θ)
      ⟨d.succ, a⟩ ⟨e.succ, b⟩ = _
  by_cases h : d = e
  · subst e
    simp only [Matrix.blockDiagonal'_apply_eq, Fin.val_succ]
  · have h' : d.succ ≠ e.succ := by
      intro he
      apply h
      apply Fin.ext
      exact Nat.succ.inj (congrArg Fin.val he)
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne _ _ _ h]

#print axioms restrict_fullAxis_mulVec
#print axioms affineAxisMatrix_moment
#print axioms affineAxisMatrix_lower
#print axioms affineAxisMatrix_diagonalBlock
#print axioms det_affineAxisMatrix
#print axioms affineAxisMatrix_zero_translation

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
