import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockAlgebra
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovHomogeneousMoments

/-!
# Affine frames on all binary monomials, including the constant

Translation expands a vertical power by the binomial theorem and preserves
the horizontal power. Its matrix lowers total degree and has identity
diagonal blocks. Composing with homogeneous shear gives the physical action
`(x,z) ↦ (x,z+θx+t)` and leaves the diagonal blocks equal to the pure shears.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- All monomials of total degree at most `k`, including degree zero. -/
abbrev FullBinaryIndex (k : ℕ) := Σ d : Fin (k + 1), Fin (d.val + 1)
abbrev FullBinarySpace (k : ℕ) := FullBinaryIndex k → ℝ

/-- The full moment vector, indexed by total and vertical degrees. -/
def fullBinaryMoment (k : ℕ) (x z : ℝ) : FullBinarySpace k :=
  fun a => x ^ (a.1.val - a.2.val) * z ^ a.2.val

theorem fullBinaryIndex_ext {k : ℕ} {a b : FullBinaryIndex k}
    (hd : a.1.val = b.1.val) (hv : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨d, i⟩
  rcases b with ⟨e, j⟩
  have hde : d = e := Fin.ext hd
  subst e
  have hij : i = j := Fin.ext hv
  subst j
  rfl

/-- Retain the horizontal degree and replace the vertical degree by `j`. -/
def translationColumn {k : ℕ} (a : FullBinaryIndex k) (j : Fin (a.2.val + 1)) :
    FullBinaryIndex k :=
  ⟨⟨a.1.val - a.2.val + j.val, by have := a.1.isLt; have := a.2.isLt; have := j.isLt; omega⟩,
    ⟨j.val, by change j.val < a.1.val - a.2.val + j.val + 1; omega⟩⟩

private theorem translationColumn_last {k : ℕ} (a : FullBinaryIndex k) :
    translationColumn a (Fin.last a.2.val) = a := by
  apply fullBinaryIndex_ext
  · change a.1.val - a.2.val + a.2.val = a.1.val
    have := a.2.isLt
    omega
  · rfl

/-- The binomial translation matrix, written as a sum of its nonzero row positions. -/
def fullTranslationMatrix (k : ℕ) (t : ℝ) : Matrix (FullBinaryIndex k) (FullBinaryIndex k) ℝ :=
  fun a b => ∑ j : Fin (a.2.val + 1),
    if translationColumn a j = b then
      (Nat.choose a.2.val j.val : ℝ) * t ^ (a.2.val - j.val) else 0

/-- Each translated coordinate is the binomial sum along its fixed horizontal degree. -/
theorem fullTranslation_mulVec (k : ℕ) (t : ℝ) (v : FullBinarySpace k) (a : FullBinaryIndex k) :
    (fullTranslationMatrix k t *ᵥ v) a =
      ∑ j : Fin (a.2.val + 1), (Nat.choose a.2.val j.val : ℝ) *
        t ^ (a.2.val - j.val) * v (translationColumn a j) := by
  change (∑ b, fullTranslationMatrix k t a b * v b) = _
  simp only [fullTranslationMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single (translationColumn a j)]
  · simp only [ite_true]
  · intro b _ hb
    simp only [if_neg hb.symm]
  · simp

/-- Vertical translation can only lower total degree. -/
theorem fullTranslation_lower (k : ℕ) (t : ℝ) :
    ∀ a b : FullBinaryIndex k, a.1 < b.1 → fullTranslationMatrix k t a b = 0 := by
  intro a b hab
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  intro h
  have hd := congrArg (fun c : FullBinaryIndex k => c.1.val) h
  change a.1.val - a.2.val + j.val = b.1.val at hd
  have ha := a.2.isLt
  have hj := j.isLt
  have hab' : a.1.val < b.1.val := hab
  omega

/-- Translation has an identity diagonal block in every homogeneous degree. -/
theorem fullTranslation_diagonalBlock (k : ℕ) (t : ℝ) (d : Fin (k + 1)) :
    diagonalBlock (fullTranslationMatrix k t) d = 1 := by
  ext x y
  change (∑ j : Fin (x.val + 1),
    if translationColumn (Sigma.mk d x) j = Sigma.mk d y then
      (Nat.choose x.val j.val : ℝ) * t ^ (x.val - j.val) else 0) =
        (1 : Matrix (Fin (d.val + 1)) (Fin (d.val + 1)) ℝ) x y
  rw [Finset.sum_eq_single (Fin.last x.val)]
  · rw [translationColumn_last]
    change (if (Sigma.mk d x : FullBinaryIndex k) = Sigma.mk d y then
      (Nat.choose x.val x.val : ℝ) * t ^ (x.val - x.val) else 0) = _
    simp [Matrix.one_apply]
  · intro j _ hj
    apply if_neg
    intro h
    have hd := congrArg (fun c : FullBinaryIndex k => c.1.val) h
    change d.val - x.val + j.val = d.val at hd
    apply hj
    apply Fin.ext
    change j.val = x.val
    have hx := x.isLt
    have hj' := j.isLt
    omega
  · simp

/-- The translation matrix acts on the genuine polynomial moment vector. -/
theorem fullTranslation_moment (k : ℕ) (t x z : ℝ) :
    fullTranslationMatrix k t *ᵥ fullBinaryMoment k x z = fullBinaryMoment k x (z + t) := by
  funext a
  rw [fullTranslation_mulVec]
  have hm (j : Fin (a.2.val + 1)) : fullBinaryMoment k x z (translationColumn a j) =
      x ^ (a.1.val - a.2.val) * z ^ j.val := by
    simp only [fullBinaryMoment, translationColumn, Nat.add_sub_cancel_right]
  simp only [hm]
  change (∑ j : Fin (a.2.val + 1), (Nat.choose a.2.val j.val : ℝ) *
    t ^ (a.2.val - j.val) * (x ^ (a.1.val - a.2.val) * z ^ j.val)) =
      x ^ (a.1.val - a.2.val) * (z + t) ^ a.2.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (Nat.choose a.2.val j : ℝ) *
    t ^ (a.2.val - j) * (x ^ (a.1.val - a.2.val) * z ^ j)) (a.2.val + 1),
    add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Zero vertical translation is the identity on every monomial. -/
theorem fullTranslation_zero (k : ℕ) : fullTranslationMatrix k 0 = 1 := by
  ext a b
  change (∑ j : Fin (a.2.val + 1),
    if translationColumn a j = b then
      (Nat.choose a.2.val j.val : ℝ) * (0 : ℝ) ^ (a.2.val - j.val) else 0) = _
  rw [Finset.sum_eq_single (Fin.last a.2.val)]
  · rw [translationColumn_last]
    simp only [Fin.val_last, Nat.choose_self, Nat.cast_one, Nat.sub_self,
      pow_zero, mul_one, Matrix.one_apply]
  · intro j _ hj
    have hpow : a.2.val - j.val ≠ 0 := by
      intro hzero
      apply hj
      apply Fin.ext
      change j.val = a.2.val
      have := j.isLt
      omega
    simp only [zero_pow hpow, mul_zero, ite_self]
  · simp

/-- At the origin only the constant coordinate survives. -/
theorem fullBinaryMoment_zero (k : ℕ) (a : FullBinaryIndex k) :
    fullBinaryMoment k 0 0 a = if a.1.val = 0 then 1 else 0 := by
  by_cases hd : a.1.val = 0
  · have hv : a.2.val = 0 := by have := a.2.isLt; omega
    simp only [fullBinaryMoment, hd, hv, Nat.sub_zero, pow_zero, one_mul, ite_true]
  · by_cases hv : a.2.val = 0
    · simp only [fullBinaryMoment, hv, Nat.sub_zero, zero_pow hd, pow_zero, mul_one, if_neg hd]
    · simp only [fullBinaryMoment, zero_pow hv, mul_zero, if_neg hd]

/-- Pure shear is block diagonal in total degree. -/
def fullShearMatrix (k : ℕ) (θ : ℝ) : Matrix (FullBinaryIndex k) (FullBinaryIndex k) ℝ :=
  Matrix.blockDiagonal' (fun d : Fin (k + 1) => shearBlock (d.val + 1) θ)

theorem fullShear_moment (k : ℕ) (θ x z : ℝ) :
    fullShearMatrix k θ *ᵥ fullBinaryMoment k x z = fullBinaryMoment k x (z + θ * x) := by
  funext a
  rcases a with ⟨d, i⟩
  rw [fullShearMatrix, blockDiagonal_mulVec]
  change (shearBlock (d.val + 1) θ *ᵥ homogeneousMoment d.val x z) i = _
  rw [shearBlock_mul_homogeneousMoment]
  rfl

/-- Translation after shear realizes the full affine action on moments. -/
def fullAffineMatrix (k : ℕ) (θ t : ℝ) : Matrix (FullBinaryIndex k) (FullBinaryIndex k) ℝ :=
  fullTranslationMatrix k t * fullShearMatrix k θ

/-- The full affine matrix implements `(x,z) ↦ (x,z+θx+t)`. -/
theorem fullAffine_moment (k : ℕ) (θ t x z : ℝ) :
    fullAffineMatrix k θ t *ᵥ fullBinaryMoment k x z = fullBinaryMoment k x (z + θ * x + t) := by
  rw [fullAffineMatrix, ← Matrix.mulVec_mulVec, fullShear_moment, fullTranslation_moment]

theorem fullAffine_lower (k : ℕ) (θ t : ℝ) :
    ∀ a b : FullBinaryIndex k, a.1 < b.1 → fullAffineMatrix k θ t a b = 0 :=
  mul_blockDiagonal_lower _ (fullTranslation_lower k t) _

/-- The diagonal blocks are the pure shears, independently of the translation parameter. -/
theorem fullAffine_diagonalBlock (k : ℕ) (θ t : ℝ) (d : Fin (k + 1)) :
    diagonalBlock (fullAffineMatrix k θ t) d = shearBlock (d.val + 1) θ := by
  rw [fullAffineMatrix, fullShearMatrix, diagonalBlock_mul_blockDiagonal,
    fullTranslation_diagonalBlock, one_mul]

/-- Every full affine binary frame has determinant one. -/
theorem det_fullAffineMatrix (k : ℕ) (θ t : ℝ) : (fullAffineMatrix k θ t).det = 1 := by
  rw [det_of_lower _ (fullAffine_lower k θ t)]
  simp only [fullAffine_diagonalBlock, det_shearBlock, Finset.prod_const_one]

#print axioms fullTranslation_mulVec
#print axioms fullTranslation_lower
#print axioms fullTranslation_diagonalBlock
#print axioms fullTranslation_moment
#print axioms fullTranslation_zero
#print axioms fullAffine_moment
#print axioms fullAffine_diagonalBlock
#print axioms det_fullAffineMatrix

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
