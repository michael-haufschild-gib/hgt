import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Negative height Grams

Negating a Hilbert Gram retains its exact radical and rank, while its
principal determinants alternate in sign. These are the linear-algebra
consequences of the height-kernel factorization in Corollaries 9.32–9.34
of Du, *Arithmetic theta products and doubling at arbitrary level*.
The statements apply to arbitrary finite families, including dependent ones.
-/

noncomputable section
open Matrix Finset
open scoped InnerProductSpace ComplexOrder

namespace HilbertMetric
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Negative Gram matrix in the conjugate-linear-first convention. -/
def negativeHeightGram (v : ι → E) : Matrix ι ι ℂ := -Matrix.gram ℂ v

/-- The negative quadratic form is exactly minus the output energy. -/
theorem negativeHeightGram_energy (v : ι → E) (c : ι → ℂ) :
    star c ⬝ᵥ (negativeHeightGram v *ᵥ c) =
      -((‖∑ i, c i • v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [negativeHeightGram, Matrix.neg_mulVec, dotProduct_neg,
    Matrix.star_dotProduct_gram_mulVec, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- Every null vector is an actual relation between the lifted vectors. -/
theorem negativeHeightGram_mulVec_eq_zero_iff (v : ι → E) (c : ι → ℂ) :
    negativeHeightGram v *ᵥ c = 0 ↔ ∑ i, c i • v i = 0 := by
  rw [negativeHeightGram, Matrix.neg_mulVec, neg_eq_zero]
  rw [← (Matrix.posSemidef_gram ℂ v).dotProduct_mulVec_zero_iff c,
    Matrix.star_dotProduct_gram_mulVec, inner_self_eq_zero]

/-- The full matrix radical consists of the exact synthesis relations. -/
theorem negativeHeightGram_ker (v : ι → E) :
    (negativeHeightGram v).mulVecLin.ker = (Fintype.linearCombination ℂ v).ker := by
  ext c
  exact negativeHeightGram_mulVec_eq_zero_iff v c

/-- Rank counts the dimension of the lifted span, even in a redundant family. -/
theorem negativeHeightGram_rank (v : ι → E) :
    (negativeHeightGram v).rank = Module.finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  have hG := (negativeHeightGram v).mulVecLin.finrank_range_add_finrank_ker
  have hV := (Fintype.linearCombination ℂ v).finrank_range_add_finrank_ker
  rw [negativeHeightGram_ker] at hG
  rw [Fintype.range_linearCombination] at hV
  exact Nat.add_right_cancel (hG.trans hV.symm)

variable [DecidableEq ι]

/-- Principal determinant signs include singular and empty families. -/
theorem negativeHeightGram_det_sign (v : ι → E) :
    (-1 : ℂ) ^ Fintype.card ι * (negativeHeightGram v).det = (Matrix.gram ℂ v).det := by
  rw [negativeHeightGram, Matrix.det_neg, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem negativeHeightGram_det_nonneg (v : ι → E) :
    0 ≤ (-1 : ℂ) ^ Fintype.card ι * (negativeHeightGram v).det := by
  rw [negativeHeightGram_det_sign]
  exact (Matrix.posSemidef_gram ℂ v).det_nonneg

/-- A nonzero minor certifies independent outputs, not merely independent inputs. -/
theorem negativeHeightGram_det_ne_zero_iff (v : ι → E) :
    (negativeHeightGram v).det ≠ 0 ↔ LinearIndependent ℂ v := by
  rw [negativeHeightGram, Matrix.det_neg, mul_ne_zero_iff]
  have h : (-1 : ℂ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [and_iff_right h, Matrix.det_gram_ne_zero_iff_linearIndependent]

omit [Fintype ι] [DecidableEq ι] in
/-- Every principal subfamily inherits the same exact sign and independence test. -/
theorem negativeHeightGram_principal_minor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → E) (j : κ → ι) :
    0 ≤ (-1 : ℂ) ^ Fintype.card κ * ((negativeHeightGram v).submatrix j j).det ∧
      (((negativeHeightGram v).submatrix j j).det ≠ 0 ↔
        LinearIndependent ℂ (v ∘ j)) :=
  ⟨negativeHeightGram_det_nonneg (v ∘ j), negativeHeightGram_det_ne_zero_iff (v ∘ j)⟩

#print axioms negativeHeightGram_energy
#print axioms negativeHeightGram_mulVec_eq_zero_iff
#print axioms negativeHeightGram_ker
#print axioms negativeHeightGram_rank
#print axioms negativeHeightGram_det_sign
#print axioms negativeHeightGram_det_nonneg
#print axioms negativeHeightGram_det_ne_zero_iff
#print axioms negativeHeightGram_principal_minor

end HilbertMetric
