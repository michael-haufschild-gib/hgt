import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertFlow

/-!
# The Hilbert flow extends the original physical normalization-defect flow

The dense embedding intertwines both operators on every original quotient
class and polynomial representative. Density proves uniqueness of the bounded
extension. The original quotient flow is also bounded and symmetric in the
proved graded physical norm and inner product.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


theorem cubicDefectHilbertEmbedding_basis (k : ℕ) :
    cubicDefectHilbertEmbedding (cubicCuspDefectBasis k)=
      cubicDefectHilbertSingle k (cubicGradedDefectMk k (cubicHomogeneousMissing k)) := by
  change cubicDefectHilbertPolynomial (cubicCuspDefectEquiv
    (((Polynomial.basisMonomials ℝ).map cubicCuspDefectEquiv.symm) k))=_
  rw [Module.Basis.map_apply,LinearEquiv.apply_symm_apply,cubicDefectHilbertPolynomial_basis]

theorem cubicHilbertFlow_extension (q : Icc (0:ℝ) 1)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    cubicHilbertFlow q (cubicDefectHilbertEmbedding x)=
      cubicDefectHilbertEmbedding (cubicCuspDefectFlow q.val x) := by
  have h : (cubicHilbertFlow q).toLinearMap.comp cubicDefectHilbertEmbedding=
      cubicDefectHilbertEmbedding.comp (cubicCuspDefectFlow q.val) := by
    apply cubicCuspDefectBasis.ext
    intro k
    rw [LinearMap.comp_apply,LinearMap.comp_apply,cubicCuspDefectFlow_spectrum,map_smul,
      cubicDefectHilbertEmbedding_basis]
    exact cubicHilbertFlow_single q k _
  exact congrArg (fun f => f x) h

theorem cubicHilbertFlow_polynomial (q : Icc (0:ℝ) 1) (P : Polynomial (Polynomial ℝ)) :
    cubicHilbertFlow q (cubicDefectHilbertEmbedding (Submodule.Quotient.mk P))=
      cubicDefectHilbertEmbedding (Submodule.Quotient.mk (cubicPolynomialFlow q.val P)) := by
  rw [cubicHilbertFlow_extension,cubicCuspDefectFlow_mk]

theorem cubicHilbertFlow_unique (q : Icc (0:ℝ) 1)
    (F : cubicDefectHilbert →L[ℝ] cubicDefectHilbert) :
    (∀ x, F (cubicDefectHilbertEmbedding x)=
      cubicDefectHilbertEmbedding (cubicCuspDefectFlow q.val x)) ↔ F=cubicHilbertFlow q := by
  constructor
  · intro h
    have he := cubicDefectHilbertEmbedding_denseRange.equalizer F.continuous
      (cubicHilbertFlow q).continuous (by
        funext x
        change F (cubicDefectHilbertEmbedding x)=cubicHilbertFlow q (cubicDefectHilbertEmbedding x)
        rw [h x,cubicHilbertFlow_extension])
    exact DFunLike.coe_injective he
  · intro h
    subst F
    exact cubicHilbertFlow_extension q

theorem cubicCuspDefectFlow_graded_bound (q : Icc (0:ℝ) 1)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    letI := cubicCuspGradedNormedGroup
    ‖cubicCuspDefectFlow q.val x‖≤q.val*‖x‖ := by
  letI := cubicCuspGradedNormedGroup
  change ‖cubicDefectHilbertEmbedding (cubicCuspDefectFlow q.val x)‖≤
    q.val*‖cubicDefectHilbertEmbedding x‖
  rw [← cubicHilbertFlow_extension]
  exact cubicHilbertFlowLinear_bound q (cubicDefectHilbertEmbedding x)

def cubicCuspDefectContinuousFlow (q : Icc (0:ℝ) 1) :
    letI := cubicCuspGradedNormedGroup
    letI := cubicCuspGradedNormedSpace
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) →L[ℝ]
      (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedNormedSpace
  exact (cubicCuspDefectFlow q.val).mkContinuous q.val (cubicCuspDefectFlow_graded_bound q)

theorem cubicCuspDefectFlow_graded_inner (q : Icc (0:ℝ) 1)
    (x y : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    letI := cubicCuspGradedNormedGroup
    letI := cubicCuspGradedInnerProductSpace
    inner ℝ (cubicCuspDefectFlow q.val x) y=inner ℝ x (cubicCuspDefectFlow q.val y) := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedInnerProductSpace
  change inner ℝ (cubicDefectHilbertEmbedding (cubicCuspDefectFlow q.val x))
    (cubicDefectHilbertEmbedding y)=inner ℝ (cubicDefectHilbertEmbedding x)
    (cubicDefectHilbertEmbedding (cubicCuspDefectFlow q.val y))
  rw [← cubicHilbertFlow_extension,← cubicHilbertFlow_extension]
  exact cubicHilbertFlow_inner q _ _

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
