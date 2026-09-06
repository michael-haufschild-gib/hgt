import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertExtension

/-!
# The physically normalized Hilbert basis of the observation defect

Unit vectors are formed in the actual graded quotient lines using their
physical recovery norms. Orthogonality and grade-sum convergence prove that
these vectors form a Hilbert basis. Its representation coordinates are the
original missing coefficients scaled by their positive optimal recovery gaps.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete


def cubicHilbertUnitGrade (k : ℕ) : cubicGradedDefect k :=
  (cubicGradedScaledEquiv k).symm 1

theorem cubicHilbertUnitGrade_norm (k : ℕ) : ‖cubicHilbertUnitGrade k‖=1 := by
  change |(cubicGradedScaledEquiv k) ((cubicGradedScaledEquiv k).symm 1)|=1
  rw [Equiv.apply_symm_apply,abs_one]

def cubicHilbertUnit (k : ℕ) : cubicDefectHilbert :=
  cubicDefectHilbertSingle k (cubicHilbertUnitGrade k)

theorem cubicHilbertUnit_norm (k : ℕ) : ‖cubicHilbertUnit k‖=1 := by
  rw [cubicHilbertUnit,cubicDefectHilbertSingle_norm,← cubicGradedLine_norm,
    cubicHilbertUnitGrade_norm]

theorem cubicHilbertUnit_orthonormal : Orthonormal ℝ cubicHilbertUnit := by
  refine ⟨cubicHilbertUnit_norm,?_⟩
  intro i j hij
  exact cubicDefectHilbertSingle_inner i j (cubicHilbertUnitGrade i) (cubicHilbertUnitGrade j) hij

theorem cubicHilbertUnitGrade_spans (k : ℕ) (x : cubicGradedDefect k) :
    (cubicGradedScaledEquiv k x) • cubicHilbertUnitGrade k=x := by
  apply (cubicGradedLineLinearEquiv k).injective
  rw [map_smul]
  change (cubicGradedScaledEquiv k x)*((cubicGradedScaledEquiv k)
    ((cubicGradedScaledEquiv k).symm 1))=cubicGradedScaledEquiv k x
  rw [Equiv.apply_symm_apply,mul_one]

theorem cubicHilbertUnit_single_mem_span (k : ℕ) (x : cubicGradedDefect k) :
    cubicDefectHilbertSingle k x ∈ Submodule.span ℝ (Set.range cubicHilbertUnit) := by
  have h : cubicDefectHilbertSingle k x=(cubicGradedScaledEquiv k x) • cubicHilbertUnit k := by
    change lp.single 2 k x=(cubicGradedScaledEquiv k x) • lp.single 2 k (cubicHilbertUnitGrade k)
    rw [← lp.single_smul,cubicHilbertUnitGrade_spans]
  rw [h]
  exact (Submodule.span ℝ (Set.range cubicHilbertUnit)).smul_mem _
    (Submodule.subset_span ⟨k,rfl⟩)

theorem cubicHilbertUnit_denseSpan :
    ⊤≤(Submodule.span ℝ (Set.range cubicHilbertUnit)).topologicalClosure := by
  intro x _
  let S := Submodule.span ℝ (Set.range cubicHilbertUnit)
  have hs : ∀ t : Finset ℕ, ∑ k ∈ t, cubicDefectHilbertSingle k (x k) ∈
      closure (S : Set cubicDefectHilbert) := by
    intro t
    exact S.le_topologicalClosure (S.sum_mem (fun k _ => cubicHilbertUnit_single_mem_span k (x k)))
  exact isClosed_closure.mem_of_tendsto (cubicDefectHilbert_hasSum x)
    (Filter.Eventually.of_forall hs)

def cubicHilbertBasis : HilbertBasis ℕ ℝ cubicDefectHilbert :=
  HilbertBasis.mk cubicHilbertUnit_orthonormal cubicHilbertUnit_denseSpan

theorem cubicHilbertBasis_apply (k : ℕ) : cubicHilbertBasis k=cubicHilbertUnit k := by
  exact congrFun (HilbertBasis.coe_mk cubicHilbertUnit_orthonormal cubicHilbertUnit_denseSpan) k

theorem cubicHilbertFlow_basis (q : Icc (0:ℝ) 1) (k : ℕ) :
    cubicHilbertFlow q (cubicHilbertBasis k)=q.val^(k+1) • cubicHilbertBasis k := by
  rw [cubicHilbertBasis_apply]
  exact cubicHilbertFlow_single q k (cubicHilbertUnitGrade k)

theorem cubicHilbertBasis_repr (x : cubicDefectHilbert) (k : ℕ) :
    cubicHilbertBasis.repr x k=cubicGradedScaledEquiv k (x k) := by
  rw [HilbertBasis.repr_apply_apply,cubicHilbertBasis_apply]
  change inner ℝ (lp.single 2 k (cubicHilbertUnitGrade k)) x=_
  rw [lp.inner_single_left]
  change ((cubicGradedScaledEquiv k) ((cubicGradedScaledEquiv k).symm 1))*
    (cubicGradedScaledEquiv k (x k))=_
  rw [Equiv.apply_symm_apply,one_mul]

theorem cubicHilbertBasis_embedding_repr
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) (k : ℕ) :
    cubicHilbertBasis.repr (cubicDefectHilbertEmbedding x) k=
      cubicGradedRecoveryGap k*(cubicCuspDefectEquiv x).coeff k := by
  rw [cubicHilbertBasis_repr]
  change cubicGradedRecoveryGap k*cubicGradedDefectCoordinate k (cubicDefectHilbertEmbedding x k)=_
  rw [← cubicDefectHilbertCoefficient_apply,cubicDefectHilbertEmbedding_coefficient]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
