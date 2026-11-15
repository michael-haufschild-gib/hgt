import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisTranslationColumns
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockAlgebra
import GaloisForLFunctions.HTGeometry.BlockDiagonalDeterminant

/-!
# Affine coordinate-direction frames in every dimension

The explicit binomial translation matrix lowers total degree and has
identity diagonal blocks. The physical shear is block diagonal on the
binary chains. Their product therefore realizes `z ↦ z+θx+t` on every
multivariate monomial, with unchanged homogeneous blocks and determinant one.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Binomial translation on all moment coordinates, including the constant. -/
def fullAxisTranslationMatrix (r k : ℕ) (t : ℝ) : Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ :=
  fun a b => ∑ j : Fin (a.2.2.val + 1),
    if axisTranslationColumn a j = b then
      (Nat.choose a.2.2.val j.val : ℝ) * t ^ (a.2.2.val - j.val) else 0

theorem fullAxisTranslation_mulVec (r k : ℕ) (t : ℝ) (v : FullAxisSpace r k)
    (a : FullAxisIndex r k) :
    (fullAxisTranslationMatrix r k t *ᵥ v) a =
      ∑ j : Fin (a.2.2.val + 1), (Nat.choose a.2.2.val j.val : ℝ) *
        t ^ (a.2.2.val - j.val) * v (axisTranslationColumn a j) := by
  change (∑ b, fullAxisTranslationMatrix r k t a b * v b) = _
  simp only [fullAxisTranslationMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single (axisTranslationColumn a j)]
  · simp only [ite_true]
  · intro b _ hb
    simp only [if_neg hb.symm]
  · simp

/-- Translation lowers total degree in arbitrary dimension. -/
theorem fullAxisTranslation_lower (r k : ℕ) (t : ℝ) :
    ∀ a b : FullAxisIndex r k, a.1 < b.1 → fullAxisTranslationMatrix r k t a b = 0 := by
  intro a b hab
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  intro h
  have hd := congrArg (fun c : FullAxisIndex r k => c.1.val) h
  rw [axisTranslationColumn_total] at hd
  have ha := fullAxisIndex_degree r k a
  have hj := j.isLt
  have hab' : a.1.val < b.1.val := hab
  omega

/-- The homogeneous diagonal blocks of translation are identity matrices. -/
theorem fullAxisTranslation_diagonalBlock (r k : ℕ) (t : ℝ) (d : Fin (k + 1)) :
    diagonalBlock (fullAxisTranslationMatrix r k t) d = 1 := by
  ext a b
  change (∑ j : Fin (a.2.val + 1),
    if axisTranslationColumn (Sigma.mk d a) j = Sigma.mk d b then
      (Nat.choose a.2.val j.val : ℝ) * t ^ (a.2.val - j.val) else 0) =
        (1 : Matrix (HomogeneousAxisIndex r d.val) (HomogeneousAxisIndex r d.val) ℝ) a b
  rw [Finset.sum_eq_single (Fin.last a.2.val)]
  · rw [axisTranslationColumn_last]
    change (if (Sigma.mk d a : FullAxisIndex r k) = Sigma.mk d b then
      (Nat.choose a.2.val a.2.val : ℝ) * t ^ (a.2.val - a.2.val) else 0) = _
    simp [Matrix.one_apply]
  · intro j _ hj
    apply if_neg
    intro h
    have hd := congrArg (fun c : FullAxisIndex r k => c.1.val) h
    rw [axisTranslationColumn_total] at hd
    change d.val - a.2.val + j.val = d.val at hd
    have ha := fullAxisIndex_degree r k (Sigma.mk d a)
    change (∑ i, chainExponent a.1 i) + (chainDegree a.1 - a.2.val) + a.2.val = d.val at ha
    apply hj
    apply Fin.ext
    change j.val = a.2.val
    have hj' := j.isLt
    omega
  · simp

/-- The matrix translation equals physical translation of the full polynomial moment map. -/
theorem fullAxisTranslation_moment (r k : ℕ) (t : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    fullAxisTranslationMatrix r k t *ᵥ fullAxisMoment r k y x z =
      fullAxisMoment r k y x (z + t) := by
  funext a
  rw [fullAxisTranslation_mulVec]
  simp only [fullAxisMoment_translationColumn]
  change (∑ j : Fin (a.2.2.val + 1), (Nat.choose a.2.2.val j.val : ℝ) *
    t ^ (a.2.2.val - j.val) * ((∏ i, y i ^ chainExponent a.2.1 i) *
      (x ^ (chainDegree a.2.1 - a.2.2.val) * z ^ j.val))) =
    (∏ i, y i ^ chainExponent a.2.1 i) *
      (x ^ (chainDegree a.2.1 - a.2.2.val) * (z + t) ^ a.2.2.val)
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (Nat.choose a.2.2.val j : ℝ) *
    t ^ (a.2.2.val - j) * ((∏ i, y i ^ chainExponent a.2.1 i) *
      (x ^ (chainDegree a.2.1 - a.2.2.val) * z ^ j))) (a.2.2.val + 1), add_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Zero translation is the identity in every dimension and degree. -/
theorem fullAxisTranslation_zero (r k : ℕ) : fullAxisTranslationMatrix r k 0 = 1 := by
  ext a b
  change (∑ j : Fin (a.2.2.val + 1),
    if axisTranslationColumn a j = b then
      (Nat.choose a.2.2.val j.val : ℝ) * (0 : ℝ) ^ (a.2.2.val - j.val) else 0) = _
  rw [Finset.sum_eq_single (Fin.last a.2.2.val)]
  · rw [axisTranslationColumn_last]
    simp only [Fin.val_last, Nat.choose_self, Nat.cast_one, Nat.sub_self,
      pow_zero, mul_one, Matrix.one_apply]
  · intro j _ hj
    have hpow : a.2.2.val - j.val ≠ 0 := by
      intro hzero
      apply hj
      apply Fin.ext
      change j.val = a.2.2.val
      have := j.isLt
      omega
    simp only [zero_pow hpow, mul_zero, ite_self]
  · simp

/-- The homogeneous shear is the direct sum of its binary chain blocks. -/
def homogeneousAxisShearMatrix (r d : ℕ) (θ : ℝ) :
    Matrix (HomogeneousAxisIndex r d) (HomogeneousAxisIndex r d) ℝ :=
  Matrix.blockDiagonal' (fun a : HomogeneousChain r d => shearBlock (chainDegree a + 1) θ)

/-- Pure shear preserves total degree as well as every untouched-variable exponent. -/
def fullAxisShearMatrix (r k : ℕ) (θ : ℝ) : Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ :=
  Matrix.blockDiagonal' (fun d : Fin (k + 1) => homogeneousAxisShearMatrix r d.val θ)

theorem fullAxisShear_moment (r k : ℕ) (θ : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    fullAxisShearMatrix r k θ *ᵥ fullAxisMoment r k y x z =
      fullAxisMoment r k y x (z + θ * x) := by
  funext a
  rcases a with ⟨d, a, i⟩
  rw [fullAxisShearMatrix, blockDiagonal_mulVec, homogeneousAxisShearMatrix, blockDiagonal_mulVec]
  exact congrFun (shearLinear_chainMoment r d.val θ y x z a) i

/-- Translation after shear on the full moment space. -/
def fullAxisAffineMatrix (r k : ℕ) (θ t : ℝ) : Matrix (FullAxisIndex r k) (FullAxisIndex r k) ℝ :=
  fullAxisTranslationMatrix r k t * fullAxisShearMatrix r k θ

/-- Every monomial transforms by the same physical affine map, in every dimension. -/
theorem fullAxisAffine_moment (r k : ℕ) (θ t : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    fullAxisAffineMatrix r k θ t *ᵥ fullAxisMoment r k y x z =
      fullAxisMoment r k y x (z + θ * x + t) := by
  rw [fullAxisAffineMatrix, ← Matrix.mulVec_mulVec, fullAxisShear_moment, fullAxisTranslation_moment]

theorem fullAxisAffine_lower (r k : ℕ) (θ t : ℝ) :
    ∀ a b : FullAxisIndex r k, a.1 < b.1 → fullAxisAffineMatrix r k θ t a b = 0 :=
  mul_blockDiagonal_lower _ (fullAxisTranslation_lower r k t) _

/-- The homogeneous diagonal blocks are independent of vertical translation. -/
theorem fullAxisAffine_diagonalBlock (r k : ℕ) (θ t : ℝ) (d : Fin (k + 1)) :
    diagonalBlock (fullAxisAffineMatrix r k θ t) d = homogeneousAxisShearMatrix r d.val θ := by
  rw [fullAxisAffineMatrix, fullAxisShearMatrix, diagonalBlock_mul_blockDiagonal,
    fullAxisTranslation_diagonalBlock, one_mul]

/-- All coordinate-direction affine moment frames have determinant one. -/
theorem det_fullAxisAffineMatrix (r k : ℕ) (θ t : ℝ) : (fullAxisAffineMatrix r k θ t).det = 1 := by
  rw [det_of_lower _ (fullAxisAffine_lower r k θ t)]
  simp only [fullAxisAffine_diagonalBlock, homogeneousAxisShearMatrix,
    GaloisForLFunctions.HTGeometry.det_blockDiagonal', det_shearBlock, Finset.prod_const_one]

#print axioms fullAxisTranslation_mulVec
#print axioms fullAxisTranslation_lower
#print axioms fullAxisTranslation_diagonalBlock
#print axioms fullAxisTranslation_moment
#print axioms fullAxisTranslation_zero
#print axioms fullAxisShear_moment
#print axioms fullAxisAffine_moment
#print axioms fullAxisAffine_diagonalBlock
#print axioms det_fullAxisAffineMatrix

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
