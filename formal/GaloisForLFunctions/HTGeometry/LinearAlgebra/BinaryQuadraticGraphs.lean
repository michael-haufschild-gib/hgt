import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryQuadraticRefinement
import GaloisForLFunctions.HTGeometry.LinearAlgebra.HyperbolicMatrixGraphs

/-!
# Binary matrix graphs and their quadratic obstruction

Polar self-orthogonality of a graph means symmetry of its matrix. Quadratic
isotropy additionally requires zero diagonal. The diagonal outer product is the
unique outer-product quadratic repair, at intersection defect zero or one.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
open LinearMap (BilinForm)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- On a symmetric binary matrix graph, the quadratic obstruction is its diagonal functional. -/
theorem binarySymmetricGraph_quadratic (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm)
    (v : (ι → ZMod 2) × (ι → ZMod 2)) (hv : v ∈ M.mulVecLin.graph) :
    hyperbolicMatrixQuadratic v = (fun i => M i i) ⬝ᵥ v.1 := by
  rw [hyperbolicMatrixQuadratic_apply]
  change v.2 = M *ᵥ v.1 at hv
  rw [hv, binary_symmetric_quadratic M hM]

/-- Every symmetric binary matrix graph is self-orthogonal for the polar form. -/
theorem binarySymmetricGraph_selfOrthogonal (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin M.mulVecLin.graph =
      M.mulVecLin.graph := by
  have hinc : M.mulVecLin.graph ≤
      BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin M.mulVecLin.graph := by
    intro v hv w hw
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      binarySymmetricGraph_quadratic M hM _ (M.mulVecLin.graph.add_mem hw hv),
      binarySymmetricGraph_quadratic M hM _ hw, binarySymmetricGraph_quadratic M hM _ hv]
    simp only [Prod.fst_add, dotProduct_add, add_sub_cancel_left, sub_self]
  apply (Submodule.eq_of_le_of_finrank_le hinc ?_).symm
  rw [BilinForm.finrank_orthogonal hyperbolicMatrixQuadratic_nondegenerate]
  simp only [linearMap_graph_finrank, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  omega

/-- A symmetric binary graph is a quadratic Lagrangian exactly when its diagonal vanishes. -/
theorem binarySymmetricGraph_isQuadraticLagrangian_iff (M : Matrix ι ι (ZMod 2))
    (hM : M.IsSymm) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic M.mulVecLin.graph ↔
      (fun i => M i i) = 0 := by
  constructor
  · intro h
    have ha : IsAlternatingMatrix M := by
      intro v
      have hz := h.1 (v, M *ᵥ v) rfl
      simpa only [hyperbolicMatrixQuadratic_apply] using hz
    exact ha.diagonal_zero
  · intro hd
    refine ⟨?_, binarySymmetricGraph_selfOrthogonal M hM⟩
    intro v hv
    rw [binarySymmetricGraph_quadratic M hM v hv, hd, zero_dotProduct]

/-- Rank-one correction gives a quadratic Lagrangian. -/
theorem binaryRepairGraph_isQuadraticLagrangian (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic (binaryAlternatingRepair M).mulVecLin.graph :=
  (isAlternatingMatrix_binaryAlternatingRepair M hM).graph_isQuadraticLagrangian

/-- The canonical quadratic repair is exactly one intersection step away unless the diagonal vanishes. -/
theorem binaryRepairGraph_defect (M : Matrix ι ι (ZMod 2)) :
    intersectionCodimension M.mulVecLin.graph (binaryAlternatingRepair M).mulVecLin.graph =
      if (fun i => M i i) = 0 then 0 else 1 := by
  rw [matrixGraph_intersectionCodimension]
  have heq : M - binaryAlternatingRepair M = vecMulVec (fun i => M i i) (fun i => M i i) := by
    ext i j
    change M i j - (M i j + M i i * M j j) = M i i * M j j
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, CharTwo.neg_eq]
  rw [heq, rank_binary_outer]

/-- Among outer-product corrections, the diagonal vector is the unique quadratic repair. -/
theorem binaryRepairGraph_unique (M : Matrix ι ι (ZMod 2)) (hM : M.IsSymm) (v : ι → ZMod 2) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic (M + vecMulVec v v).mulVecLin.graph ↔
      v = fun i => M i i := by
  constructor
  · intro h
    have ha : IsAlternatingMatrix (M + vecMulVec v v) := by
      intro x
      simpa only [hyperbolicMatrixQuadratic_apply] using
        h.1 (x, (M + vecMulVec v v) *ᵥ x) rfl
    have hd := ha.diagonal_zero
    funext i
    have hi := congrFun hd i
    change M i i + v i * v i = 0 at hi
    rw [← sq, ZMod.pow_card] at hi
    have heq := eq_neg_of_add_eq_zero_left hi
    simpa only [CharTwo.neg_eq] using heq.symm
  · intro h
    subst v
    exact binaryRepairGraph_isQuadraticLagrangian M hM

#print axioms binarySymmetricGraph_isQuadraticLagrangian_iff
#print axioms binaryRepairGraph_defect
#print axioms binaryRepairGraph_unique
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix
open LinearMap (BilinForm)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Polar self-orthogonality of a binary graph is exactly matrix symmetry. -/
theorem binaryGraph_selfOrthogonal_iff (M : Matrix ι ι (ZMod 2)) :
    BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin M.mulVecLin.graph =
      M.mulVecLin.graph ↔ M.IsSymm := by
  constructor
  · intro hM
    change Mᵀ = M
    ext i j
    change M j i = M i j
    have hv : (Pi.single i 1, M *ᵥ Pi.single i 1) ∈
        BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin M.mulVecLin.graph := by
      rw [hM]
      rfl
    have h := hv (Pi.single j 1, M *ᵥ Pi.single j 1) rfl
    rw [hyperbolicMatrixQuadratic_polar] at h
    have hzero : M j i + M i j = 0 := by
      simpa [dotProduct, mulVec, Pi.single_apply] using h
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hzero
  · exact binarySymmetricGraph_selfOrthogonal M

/-- Quadratic Lagrangian binary graphs are exactly symmetric zero-diagonal matrices. -/
theorem binaryGraph_isQuadraticLagrangian_iff (M : Matrix ι ι (ZMod 2)) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic M.mulVecLin.graph ↔
      M.IsSymm ∧ (fun i => M i i) = 0 := by
  constructor
  · intro h
    have hM := (binaryGraph_selfOrthogonal_iff M).mp h.2
    exact ⟨hM, (binarySymmetricGraph_isQuadraticLagrangian_iff M hM).mp h⟩
  · rintro ⟨hM, hd⟩
    exact (binarySymmetricGraph_isQuadraticLagrangian_iff M hM).mpr hd

/-- A rank-one quadratic repair exists precisely for symmetric matrices, and its vector is forced. -/
theorem binaryGraph_outerRepair_iff (M : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic (M + vecMulVec v v).mulVecLin.graph ↔
      M.IsSymm ∧ v = fun i => M i i := by
  constructor
  · intro h
    have hs := ((binaryGraph_isQuadraticLagrangian_iff (M + vecMulVec v v)).mp h).1
    change (M + vecMulVec v v)ᵀ = M + vecMulVec v v at hs
    have ho : (vecMulVec v v)ᵀ = vecMulVec v v := by
      ext i j
      exact mul_comm _ _
    rw [transpose_add, ho] at hs
    have hM : M.IsSymm := add_right_cancel hs
    exact ⟨hM, (binaryRepairGraph_unique M hM v).mp h⟩
  · rintro ⟨hM, hv⟩
    exact (binaryRepairGraph_unique M hM v).mpr hv

#print axioms binaryGraph_isQuadraticLagrangian_iff
#print axioms binaryGraph_outerRepair_iff
end GaloisForLFunctions.HTGeometry.LinearAlgebra
