import GaloisForLFunctions.HilbertMetric.NegativeHeightGrams
import GaloisForLFunctions.HTGeometry.FiniteGramsOfAnOperator

/-!
# Exact height certificates for negative Gram operators

For the existing finite operator Gram, a factorization `Q = -T†T` gives
the exact radical, rank, and determinant sign in terms of actual outputs
of `T`. Thus an independent input family can have a singular height Gram
precisely because its outputs acquire a relation. These are the finite
operator versions of Du, Corollaries 9.32–9.34.
-/

noncomputable section
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Matrix Finset
open GaloisForLFunctions.HTGeometry.PaperNegativePart

namespace HilbertMetric
variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The operator Gram is the negative Hilbert Gram of its actual images. -/
theorem finiteGram_negAdjoint (T : E →L[ℂ] F) (v : ι → E) :
    finiteGram (-(T.adjoint ∘L T)) v = negativeHeightGram (fun i => T (v i)) := by
  ext i j
  change inner ℂ (-(T.adjoint (T (v i)))) (v j) = -inner ℂ (T (v i)) (T (v j))
  rw [inner_neg_left, adjoint_inner_left]

/-- Every radical vector is exactly an input combination killed by `T`. -/
theorem finiteGram_negAdjoint_radical (T : E →L[ℂ] F) (v : ι → E) (c : ι → ℂ) :
    finiteGram (-(T.adjoint ∘L T)) v *ᵥ c = 0 ↔ T (finiteCombination v c) = 0 := by
  rw [finiteGram_negAdjoint, negativeHeightGram_mulVec_eq_zero_iff]
  simp only [finiteCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]

/-- The finite height rank is the dimension of the output span. -/
theorem finiteGram_negAdjoint_rank (T : E →L[ℂ] F) (v : ι → E) :
    (finiteGram (-(T.adjoint ∘L T)) v).rank =
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun i => T (v i))) := by
  rw [finiteGram_negAdjoint, negativeHeightGram_rank]

/-- Signed height determinants are nonnegative, including singular families. -/
theorem finiteGram_negAdjoint_det_nonneg (T : E →L[ℂ] F) (v : ι → E) :
    0 ≤ (-1 : ℂ) ^ Fintype.card ι * (finiteGram (-(T.adjoint ∘L T)) v).det := by
  rw [finiteGram_negAdjoint]
  exact negativeHeightGram_det_nonneg _

/-- A nonzero height determinant certifies independence after applying `T`. -/
theorem finiteGram_negAdjoint_det_ne_zero_iff (T : E →L[ℂ] F) (v : ι → E) :
    (finiteGram (-(T.adjoint ∘L T)) v).det ≠ 0 ↔
      LinearIndependent ℂ (fun i => T (v i)) := by
  rw [finiteGram_negAdjoint, negativeHeightGram_det_ne_zero_iff]

#print axioms finiteGram_negAdjoint
#print axioms finiteGram_negAdjoint_radical
#print axioms finiteGram_negAdjoint_rank
#print axioms finiteGram_negAdjoint_det_nonneg
#print axioms finiteGram_negAdjoint_det_ne_zero_iff

end HilbertMetric
