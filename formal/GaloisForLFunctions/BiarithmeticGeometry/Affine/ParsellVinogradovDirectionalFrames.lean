import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovTailShearMatrices
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisFrames

/-!
# Moment frames for arbitrary horizontal shear directions

The distinguished horizontal coefficient acts inside binary chains. All
other horizontal coefficients strictly lower their binary degree, while
vertical translation lowers total degree. These two filtrations retain the
same binary diagonal blocks for every affine shear direction.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Homogeneous moment action of a general horizontal shear. -/
def homogeneousDirectionalMatrix (r d : ℕ) (θ : ℝ) (η : Fin r → ℝ) :
    Matrix (HomogeneousAxisIndex r d) (HomogeneousAxisIndex r d) ℝ :=
  tailProduct r d η * homogeneousAxisShearMatrix r d θ

theorem homogeneousDirectional_rankLower (r d : ℕ) (θ : ℝ) (η : Fin r → ℝ) :
    RankLower (fun a : HomogeneousChain r d => chainDegree a)
      (homogeneousDirectionalMatrix r d θ η) :=
  (tailProduct_rankLower r d η).mul (rankLower_blockDiagonal _ _)

/-- Arbitrary transverse coefficients preserve the distinguished binary shear blocks. -/
theorem homogeneousDirectional_diagonalBlock (r d : ℕ) (θ : ℝ) (η : Fin r → ℝ)
    (a : HomogeneousChain r d) :
    diagonalBlock (homogeneousDirectionalMatrix r d θ η) a = shearBlock (chainDegree a + 1) θ := by
  rw [homogeneousDirectionalMatrix, homogeneousAxisShearMatrix,
    diagonalBlock_mul_blockDiagonal, tailProduct_diagonalBlock, one_mul]

theorem homogeneousDirectional_moment (r d : ℕ) (θ : ℝ) (η y : Fin r → ℝ) (x z : ℝ) :
    homogeneousDirectionalMatrix r d θ η *ᵥ homogeneousAxisMoment r d y x z =
      homogeneousAxisMoment r d y x (z + θ * x + ∑ i, η i * y i) := by
  have hs : homogeneousAxisShearMatrix r d θ *ᵥ homogeneousAxisMoment r d y x z =
      homogeneousAxisMoment r d y x (z + θ * x) := by
    funext a
    rcases a with ⟨a, j⟩
    rw [homogeneousAxisShearMatrix, blockDiagonal_mulVec]
    exact congrFun (shearLinear_chainMoment r d θ y x z a) j
  rw [homogeneousDirectionalMatrix, ← Matrix.mulVec_mulVec, hs, tailProduct_moment]

theorem homogeneousDirectional_zero_tail (r d : ℕ) (θ : ℝ) :
    homogeneousDirectionalMatrix r d θ 0 = homogeneousAxisShearMatrix r d θ := by
  rw [homogeneousDirectionalMatrix, tailProduct_zero, one_mul]

/-- All homogeneous degrees, including constants, under an arbitrary horizontal shear. -/
def fullDirectionalShearMatrix (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) :
    Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ :=
  Matrix.blockDiagonal' (fun d : Fin (k + 1) => homogeneousDirectionalMatrix r d.val θ η)

theorem fullDirectionalShear_moment (r k : ℕ) (θ : ℝ) (η y : Fin r → ℝ) (x z : ℝ) :
    fullDirectionalShearMatrix r k θ η *ᵥ fullAxisMoment r k y x z =
      fullAxisMoment r k y x (z + θ * x + ∑ i, η i * y i) := by
  funext a
  rcases a with ⟨d, a⟩
  rw [fullDirectionalShearMatrix, blockDiagonal_mulVec]
  exact congrFun (homogeneousDirectional_moment r d.val θ η y x z) a

/-- Full affine moment action with arbitrary horizontal and vertical parameters. -/
def fullDirectionalAffineMatrix (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) :
    Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ :=
  fullAxisTranslationMatrix r k t * fullDirectionalShearMatrix r k θ η

theorem fullDirectionalAffine_moment (r k : ℕ) (θ : ℝ) (η y : Fin r → ℝ) (t x z : ℝ) :
    fullDirectionalAffineMatrix r k θ η t *ᵥ fullAxisMoment r k y x z =
      fullAxisMoment r k y x (z + θ * x + ∑ i, η i * y i + t) := by
  rw [fullDirectionalAffineMatrix, ← Matrix.mulVec_mulVec,
    fullDirectionalShear_moment, fullAxisTranslation_moment]

theorem fullDirectionalAffine_lower (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) :
    ∀ a b : FullAxisIndex r k, a.1 < b.1 → fullDirectionalAffineMatrix r k θ η t a b = 0 :=
  mul_blockDiagonal_lower _ (fullAxisTranslation_lower r k t) _

theorem fullDirectionalAffine_diagonalBlock (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ)
    (t : ℝ) (d : Fin (k + 1)) :
    diagonalBlock (fullDirectionalAffineMatrix r k θ η t) d =
      homogeneousDirectionalMatrix r d.val θ η := by
  rw [fullDirectionalAffineMatrix, fullDirectionalShearMatrix,
    diagonalBlock_mul_blockDiagonal, fullAxisTranslation_diagonalBlock, one_mul]

/-- Centered action on every nonconstant monomial through degree `k`. -/
def directionalAffineMatrix (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) :
    Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ :=
  (fullDirectionalAffineMatrix r k θ η t).submatrix positiveAxisIndex positiveAxisIndex

theorem directionalAffine_moment (r k : ℕ) (θ : ℝ) (η y : Fin r → ℝ) (t x z : ℝ) :
    directionalAffineMatrix r k θ η t *ᵥ affineAxisMoment r k y x z =
      affineAxisMoment r k y x (z + θ * x + ∑ i, η i * y i + t) -
        affineAxisMoment r k 0 0 t := by
  have h : fullDirectionalAffineMatrix r k θ η t *ᵥ
      (fullAxisMoment r k y x z - fullAxisMoment r k 0 0 0) =
      fullAxisMoment r k y x (z + θ * x + ∑ i, η i * y i + t) -
        fullAxisMoment r k 0 0 t := by
    change Matrix.toLin' (fullDirectionalAffineMatrix r k θ η t) _ = _
    rw [map_sub]
    change fullDirectionalAffineMatrix r k θ η t *ᵥ fullAxisMoment r k y x z -
      fullDirectionalAffineMatrix r k θ η t *ᵥ fullAxisMoment r k 0 0 0 = _
    rw [fullDirectionalAffine_moment, fullDirectionalAffine_moment]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  funext a
  have ha := congrFun h (positiveAxisIndex a)
  rw [restrict_fullAxis_mulVec] at ha
  exact ha

theorem directionalAffine_lower (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) :
    ∀ a b : AffineAxisIndex r k, a.1 < b.1 → directionalAffineMatrix r k θ η t a b = 0 := by
  intro a b hab
  apply fullDirectionalAffine_lower r k θ η t (positiveAxisIndex a) (positiveAxisIndex b)
  change a.1.val + 1 < b.1.val + 1
  have hab' : a.1.val < b.1.val := hab
  omega

theorem directionalAffine_diagonalBlock (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ)
    (t : ℝ) (d : Fin k) :
    diagonalBlock (directionalAffineMatrix r k θ η t) d =
      homogeneousDirectionalMatrix r (d.val + 1) θ η :=
  fullDirectionalAffine_diagonalBlock r k θ η t d.succ

/-- Every affine directional frame preserves volume in moment-coordinate space. -/
theorem det_directionalAffineMatrix (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) :
    (directionalAffineMatrix r k θ η t).det = 1 := by
  rw [det_of_lower _ (directionalAffine_lower r k θ η t)]
  simp only [directionalAffine_diagonalBlock]
  have hd (d : Fin k) : (homogeneousDirectionalMatrix r (d.val + 1) θ η).det = 1 := by
    rw [det_of_rankLower _ (homogeneousDirectional_rankLower r (d.val + 1) θ η)]
    simp only [homogeneousDirectional_diagonalBlock, det_shearBlock, Finset.prod_const_one]
  simp only [hd, Finset.prod_const_one]

theorem directionalAffine_zero_tail (r k : ℕ) (θ t : ℝ) :
    directionalAffineMatrix r k θ 0 t = affineAxisMatrix r k θ t := by
  unfold directionalAffineMatrix affineAxisMatrix fullDirectionalAffineMatrix
    fullAxisAffineMatrix fullDirectionalShearMatrix fullAxisShearMatrix
  simp only [homogeneousDirectional_zero_tail]

#print axioms homogeneousDirectional_rankLower
#print axioms homogeneousDirectional_diagonalBlock
#print axioms homogeneousDirectional_moment
#print axioms fullDirectionalAffine_moment
#print axioms directionalAffine_moment
#print axioms directionalAffine_diagonalBlock
#print axioms det_directionalAffineMatrix
#print axioms directionalAffine_zero_tail

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
