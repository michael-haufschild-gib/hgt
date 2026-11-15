import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovTailShearColumns
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaRankLower

/-!
# Transverse moment shears and the binary-degree filtration

Each transverse shear replaces vertical powers by powers of one fixed
horizontal variable. Its matrix strictly lowers binary-chain degree away
from identity blocks. Products retain this property, so arbitrary transverse
directions cannot alter the diagonal binary-shear determinant certificates.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Homogeneous moment matrix of the elementary shear `z ↦ z+η yᵢ`. -/
def tailShearMatrix (r d : ℕ) (i : Fin r) (η : ℝ) :
    Matrix (HomogeneousAxisIndex r d) (HomogeneousAxisIndex r d) ℝ :=
  fun a b => ∑ j : Fin (a.2.val + 1),
    if tailShearColumn a i j = b then
      (Nat.choose a.2.val j.val : ℝ) * η ^ (a.2.val - j.val) else 0

theorem tailShear_mulVec (r d : ℕ) (i : Fin r) (η : ℝ)
    (v : HomogeneousAxisIndex r d → ℝ) (a : HomogeneousAxisIndex r d) :
    (tailShearMatrix r d i η *ᵥ v) a =
      ∑ j : Fin (a.2.val + 1), (Nat.choose a.2.val j.val : ℝ) *
        η ^ (a.2.val - j.val) * v (tailShearColumn a i j) := by
  change (∑ b, tailShearMatrix r d i η a b * v b) = _
  simp only [tailShearMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single (tailShearColumn a i j)]
  · simp only [ite_true]
  · intro b _ hb
    simp only [if_neg hb.symm]
  · simp

/-- Nonidentity transverse terms strictly lower remaining binary degree. -/
theorem tailShear_rankLower (r d : ℕ) (i : Fin r) (η : ℝ) :
    RankLower (fun a : HomogeneousChain r d => chainDegree a) (tailShearMatrix r d i η) := by
  intro a b hab hr
  apply Finset.sum_eq_zero
  intro j _
  apply if_neg
  intro h
  rcases tailShearColumn_eq_or_degree_lt a i j with he | hl
  · exact hab (congrArg (fun c : HomogeneousAxisIndex r d => c.1) (he.symm.trans h))
  · rw [h] at hl
    exact (not_lt_of_ge hr) hl

/-- Every diagonal binary-chain block of a transverse shear is identity. -/
theorem tailShear_diagonalBlock (r d : ℕ) (i : Fin r) (η : ℝ)
    (a : HomogeneousChain r d) : diagonalBlock (tailShearMatrix r d i η) a = 1 := by
  ext v w
  change (∑ j : Fin (v.val + 1),
    if tailShearColumn (Sigma.mk a v) i j = Sigma.mk a w then
      (Nat.choose v.val j.val : ℝ) * η ^ (v.val - j.val) else 0) = _
  rw [Finset.sum_eq_single (Fin.last v.val)]
  · rw [tailShearColumn_last]
    simp [Matrix.one_apply]
  · intro j _ hj
    apply if_neg
    intro h
    have hc := congrArg (fun b : HomogeneousAxisIndex r d => chainDegree b.1) h
    have hd := tailShearColumn_degree (Sigma.mk a v) i j
    change chainDegree (tailShearColumn (Sigma.mk a v) i j).1 = chainDegree a at hc
    change chainDegree (tailShearColumn (Sigma.mk a v) i j).1 + (v.val - j.val) =
      chainDegree a at hd
    apply hj
    apply Fin.ext
    change j.val = v.val
    have hbound := j.isLt
    omega
  · simp

/-- The sparse matrix implements the physical transverse shear on all homogeneous monomials. -/
theorem tailShear_moment (r d : ℕ) (i : Fin r) (η : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    tailShearMatrix r d i η *ᵥ homogeneousAxisMoment r d y x z =
      homogeneousAxisMoment r d y x (z + η * y i) := by
  funext a
  rw [tailShear_mulVec]
  simp only [homogeneousAxisMoment_tailShearColumn]
  change (∑ j : Fin (a.2.val + 1), (Nat.choose a.2.val j.val : ℝ) *
    η ^ (a.2.val - j.val) * ((∏ l, y l ^ chainExponent a.1 l) *
      (x ^ (chainDegree a.1 - a.2.val) * (y i ^ (a.2.val - j.val) * z ^ j.val)))) =
    (∏ l, y l ^ chainExponent a.1 l) *
      (x ^ (chainDegree a.1 - a.2.val) * (z + η * y i) ^ a.2.val)
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (Nat.choose a.2.val j : ℝ) *
    η ^ (a.2.val - j) * ((∏ l, y l ^ chainExponent a.1 l) *
      (x ^ (chainDegree a.1 - a.2.val) * (y i ^ (a.2.val - j) * z ^ j)))) (a.2.val + 1), add_pow]
  simp only [Finset.mul_sum, mul_pow]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tailShear_zero (r d : ℕ) (i : Fin r) : tailShearMatrix r d i 0 = 1 := by
  ext a b
  change (∑ j : Fin (a.2.val + 1),
    if tailShearColumn a i j = b then
      (Nat.choose a.2.val j.val : ℝ) * (0 : ℝ) ^ (a.2.val - j.val) else 0) = _
  rw [Finset.sum_eq_single (Fin.last a.2.val)]
  · rw [tailShearColumn_last]
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

/-- Ordered product of transverse elementary moment shears. -/
def tailProductList (r d : ℕ) (η : Fin r → ℝ) : List (Fin r) →
    Matrix (HomogeneousAxisIndex r d) (HomogeneousAxisIndex r d) ℝ
  | [] => 1
  | i :: L => tailShearMatrix r d i (η i) * tailProductList r d η L

theorem tailProductList_rankLower (r d : ℕ) (η : Fin r → ℝ) (L : List (Fin r)) :
    RankLower (fun a : HomogeneousChain r d => chainDegree a) (tailProductList r d η L) := by
  induction L with
  | nil => exact rankLower_one _
  | cons i L ih => exact (tailShear_rankLower r d i (η i)).mul ih

/-- Transverse products have identity diagonal blocks, regardless of their coefficients. -/
theorem tailProductList_diagonalBlock (r d : ℕ) (η : Fin r → ℝ) (L : List (Fin r))
    (a : HomogeneousChain r d) : diagonalBlock (tailProductList r d η L) a = 1 := by
  induction L with
  | nil => ext v w; simp [tailProductList, diagonalBlock, Matrix.one_apply]
  | cons i L ih =>
    rw [tailProductList, diagonalBlock_mul_of_rankLower
      (tailShear_rankLower r d i (η i)) (tailProductList_rankLower r d η L),
      tailShear_diagonalBlock, ih, one_mul]

/-- Composing transverse shears adds their physical linear forms. -/
theorem tailProductList_moment (r d : ℕ) (η : Fin r → ℝ) (L : List (Fin r))
    (y : Fin r → ℝ) (x z : ℝ) :
    tailProductList r d η L *ᵥ homogeneousAxisMoment r d y x z =
      homogeneousAxisMoment r d y x (z + (L.map (fun i => η i * y i)).sum) := by
  induction L with
  | nil => simp [tailProductList]
  | cons i L ih =>
    rw [tailProductList, ← Matrix.mulVec_mulVec, ih, tailShear_moment]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    ring

theorem tailProductList_zero (r d : ℕ) (L : List (Fin r)) : tailProductList r d 0 L = 1 := by
  induction L with
  | nil => rfl
  | cons i L ih => simp only [tailProductList, Pi.zero_apply, tailShear_zero, ih, one_mul]

/-- Moment matrix of the complete transverse linear form. -/
def tailProduct (r d : ℕ) (η : Fin r → ℝ) :
    Matrix (HomogeneousAxisIndex r d) (HomogeneousAxisIndex r d) ℝ :=
  tailProductList r d η (List.ofFn (fun i : Fin r => i))

theorem tailProduct_rankLower (r d : ℕ) (η : Fin r → ℝ) :
    RankLower (fun a : HomogeneousChain r d => chainDegree a) (tailProduct r d η) :=
  tailProductList_rankLower r d η _

theorem tailProduct_diagonalBlock (r d : ℕ) (η : Fin r → ℝ) (a : HomogeneousChain r d) :
    diagonalBlock (tailProduct r d η) a = 1 := tailProductList_diagonalBlock r d η _ a

/-- Arbitrary transverse coefficients act by their full horizontal linear form. -/
theorem tailProduct_moment (r d : ℕ) (η : Fin r → ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    tailProduct r d η *ᵥ homogeneousAxisMoment r d y x z =
      homogeneousAxisMoment r d y x (z + ∑ i, η i * y i) := by
  simpa only [tailProduct, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using
    tailProductList_moment r d η (List.ofFn (fun i : Fin r => i)) y x z

theorem tailProduct_zero (r d : ℕ) : tailProduct r d 0 = 1 := tailProductList_zero r d _

#print axioms tailShear_rankLower
#print axioms tailShear_diagonalBlock
#print axioms tailShear_moment
#print axioms tailShear_zero
#print axioms tailProductList_rankLower
#print axioms tailProductList_diagonalBlock
#print axioms tailProductList_moment
#print axioms tailProductList_zero
#print axioms tailProduct_moment
#print axioms tailProduct_diagonalBlock

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
