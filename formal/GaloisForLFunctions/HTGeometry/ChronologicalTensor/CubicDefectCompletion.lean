import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicDefectEmbedding
import Mathlib.Topology.UniformSpace.AbstractCompletion

/-!
# The actual normalization quotient and its graded Hilbert completion

Pullback along the proved injective dense embedding gives the existing
algebraic quotient its graded physical norm and inner product. The embedding
is an isometry and supplies an AbstractCompletion whose carrier is the Hilbert
sum of the actual graded defects. The original monomial classes have exactly
the optimal physical recovery gaps as their norms.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial

attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


@[implicit_reducible]
def cubicCuspGradedNormedGroup :
    NormedAddCommGroup (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :=
  NormedAddCommGroup.induced _ _ cubicDefectHilbertEmbedding cubicDefectHilbertEmbedding_injective

@[implicit_reducible]
def cubicCuspGradedNormedSpace :
    letI := cubicCuspGradedNormedGroup
    NormedSpace ℝ (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := cubicCuspGradedNormedGroup
  exact NormedSpace.induced ℝ _ _ cubicDefectHilbertEmbedding

@[implicit_reducible]
def cubicCuspGradedInnerProductSpace :
    letI := cubicCuspGradedNormedGroup
    InnerProductSpace ℝ (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := cubicCuspGradedNormedGroup
  exact InnerProductSpace.induced cubicDefectHilbertEmbedding

theorem cubicDefectHilbertEmbedding_isometry :
    letI := cubicCuspGradedNormedGroup
    Isometry cubicDefectHilbertEmbedding := by
  letI := cubicCuspGradedNormedGroup
  exact AddMonoidHomClass.isometry_of_norm cubicDefectHilbertEmbedding (fun _ => rfl)

def cubicCuspGradedCompletion :
    letI := cubicCuspGradedNormedGroup
    AbstractCompletion (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := cubicCuspGradedNormedGroup
  exact {
    space := cubicDefectHilbert
    coe := cubicDefectHilbertEmbedding
    uniformStruct := inferInstance
    complete := cubicDefectHilbert_complete
    separation := inferInstance
    isUniformInducing := cubicDefectHilbertEmbedding_isometry.isUniformInducing
    dense := cubicDefectHilbertEmbedding_denseRange }

theorem cubicCuspGradedNorm_sq
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    letI := cubicCuspGradedNormedGroup
    ‖x‖^(2 : ℕ)=∑' k, (cubicGradedRecoveryGap k)^(2 : ℕ) * ((cubicCuspDefectEquiv x).coeff k)^(2 : ℕ) :=
  cubicDefectHilbertEmbedding_norm_sq x

theorem cubicCuspGradedInner
    (x y : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    letI := cubicCuspGradedNormedGroup
    letI := cubicCuspGradedInnerProductSpace
    inner ℝ x y=∑' k, (cubicGradedRecoveryGap k)^(2 : ℕ) *
      (cubicCuspDefectEquiv x).coeff k * (cubicCuspDefectEquiv y).coeff k := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedInnerProductSpace
  change inner ℝ (cubicDefectHilbertEmbedding x) (cubicDefectHilbertEmbedding y)=_
  rw [cubicDefectHilbert_inner]
  congr 1
  funext k
  rw [← cubicDefectHilbertCoefficient_apply,← cubicDefectHilbertCoefficient_apply,
    cubicDefectHilbertEmbedding_coefficient,cubicDefectHilbertEmbedding_coefficient]

theorem cubicCuspGradedBasis_norm (k : ℕ) :
    letI := cubicCuspGradedNormedGroup
    ‖cubicCuspDefectBasis k‖=cubicGradedRecoveryGap k := by
  letI := cubicCuspGradedNormedGroup
  change ‖cubicDefectHilbertPolynomial (cubicCuspDefectEquiv
    (((Polynomial.basisMonomials ℝ).map cubicCuspDefectEquiv.symm) k))‖=_
  rw [Module.Basis.map_apply,LinearEquiv.apply_symm_apply,cubicDefectHilbertPolynomial_basis,
    cubicDefectHilbertSingle_observation,cubicGradedCoefficient_missing,abs_one,one_mul]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
