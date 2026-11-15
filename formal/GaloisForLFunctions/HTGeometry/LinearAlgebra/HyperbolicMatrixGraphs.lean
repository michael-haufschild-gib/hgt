import GaloisForLFunctions.HTGeometry.LinearAlgebra.QuadraticLagrangianParity
import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingMatrixRank
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPolarizationTower

/-!
# Alternating matrix graphs in split quadratic spaces

The form `q(x,y)=x·y` is nondegenerate in every characteristic. Alternating matrices
give quadratic Lagrangians by taking their graphs. The intersection defect of two
graphs equals the rank of their difference, so alternating graphs have even defect.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The split quadratic form `q(x,y)=x·y`, in arbitrary characteristic. -/
def hyperbolicMatrixQuadratic : QuadraticForm K ((ι → K) × (ι → K)) :=
  LinearMap.BilinMap.toQuadraticMap ((1 : Matrix ι ι K).toBilin'.compl₁₂
    (LinearMap.fst K (ι → K) (ι → K))
    (LinearMap.snd K (ι → K) (ι → K)))

theorem hyperbolicMatrixQuadratic_apply (v : (ι → K) × (ι → K)) :
    hyperbolicMatrixQuadratic v = v.1 ⬝ᵥ v.2 := by
  change (1 : Matrix ι ι K).toBilin' v.1 v.2 = _
  rw [Matrix.toBilin'_apply', one_mulVec]

theorem hyperbolicMatrixQuadratic_polar (v w : (ι → K) × (ι → K)) :
    hyperbolicMatrixQuadratic.polarBilin v w = v.1 ⬝ᵥ w.2 + w.1 ⬝ᵥ v.2 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [hyperbolicMatrixQuadratic_apply, Prod.fst_add, Prod.snd_add,
    dotProduct_add, add_dotProduct]
  abel

/-- Both coordinate pairings are detected by standard basis vectors. -/
theorem hyperbolicMatrixQuadratic_nondegenerate :
    (hyperbolicMatrixQuadratic (K := K) (ι := ι)).polarBilin.Nondegenerate := by
  apply (quadratic_polar_isRefl
    (hyperbolicMatrixQuadratic (K := K) (ι := ι))).nondegenerate_iff_separatingLeft.mpr
  intro v hv
  apply Prod.ext
  · ext i
    have h := hv (0, Pi.single i 1)
    change (hyperbolicMatrixQuadratic (K := K) (ι := ι)).polarBilin v (0, Pi.single i 1) = 0 at h
    rw [hyperbolicMatrixQuadratic_polar] at h
    simpa [dotProduct, Pi.single_apply] using h
  · ext i
    have h := hv (Pi.single i 1, 0)
    change (hyperbolicMatrixQuadratic (K := K) (ι := ι)).polarBilin v (Pi.single i 1, 0) = 0 at h
    rw [hyperbolicMatrixQuadratic_polar] at h
    simpa [dotProduct, Pi.single_apply] using h

/-- The graph of any alternating matrix is a quadratic Lagrangian. -/
theorem IsAlternatingMatrix.graph_isQuadraticLagrangian {M : Matrix ι ι K}
    (hM : IsAlternatingMatrix M) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic M.mulVecLin.graph := by
  have hzero : ∀ v ∈ M.mulVecLin.graph, hyperbolicMatrixQuadratic v = 0 := by
    intro v hv
    rw [hyperbolicMatrixQuadratic_apply]
    change v.2 = M *ᵥ v.1 at hv
    rw [hv]
    exact hM v.1
  refine ⟨hzero, ?_⟩
  have hinc : M.mulVecLin.graph ≤
      LinearMap.BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin M.mulVecLin.graph := by
    intro v hv w hw
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hzero _ (M.mulVecLin.graph.add_mem hw hv), hzero _ hw, hzero _ hv]
    simp only [sub_zero]
  apply (Submodule.eq_of_le_of_finrank_le hinc ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal hyperbolicMatrixQuadratic_nondegenerate]
  simp only [linearMap_graph_finrank, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  omega

/-- Arbitrary matrices supply concrete quadratic Lagrangians by skew-symmetrization. -/
theorem skewGraph_isQuadraticLagrangian (M : Matrix ι ι K) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic (M - Mᵀ).mulVecLin.graph :=
  (isAlternatingMatrix_sub_transpose M).graph_isQuadraticLagrangian

/-- The intersection-defect cocycle holds for arbitrary skew-symmetrized matrix graphs. -/
theorem skewGraph_defect_cocycle (A B C : Matrix ι ι K) :
    intersectionCodimension (A - Aᵀ).mulVecLin.graph (C - Cᵀ).mulVecLin.graph % 2 =
      (intersectionCodimension (A - Aᵀ).mulVecLin.graph (B - Bᵀ).mulVecLin.graph +
        intersectionCodimension (B - Bᵀ).mulVecLin.graph (C - Cᵀ).mulVecLin.graph) % 2 :=
  quadraticLagrangian_defect_cocycle hyperbolicMatrixQuadratic
    hyperbolicMatrixQuadratic_nondegenerate (skewGraph_isQuadraticLagrangian A)
    (skewGraph_isQuadraticLagrangian B) (skewGraph_isQuadraticLagrangian C)

#print axioms hyperbolicMatrixQuadratic_nondegenerate
#print axioms skewGraph_isQuadraticLagrangian
#print axioms skewGraph_defect_cocycle
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Intersections of graphs are kernels of differences, with an explicit isomorphism. -/
def graphIntersectionKernelEquiv (f g : V →ₗ[K] V) :
    (f - g).ker ≃ₗ[K] ↥(f.graph ⊓ g.graph) where
  toFun x := ⟨(x, f x), ⟨rfl, sub_eq_zero.mp x.property⟩⟩
  invFun z := ⟨z.val.1, sub_eq_zero.mpr (z.property.1.symm.trans z.property.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv z := Subtype.ext (Prod.ext rfl z.property.1.symm)
  map_add' x y := Subtype.ext (Prod.ext rfl (map_add f (x : V) (y : V)))
  map_smul' a x := Subtype.ext (Prod.ext rfl (map_smul f a (x : V)))

/-- The intersection defect of two graphs is exactly the rank of the difference. -/
theorem graph_intersectionCodimension [FiniteDimensional K V] (f g : V →ₗ[K] V) :
    intersectionCodimension f.graph g.graph = finrank K (f - g).range := by
  rw [intersectionCodimension_eq, linearMap_graph_finrank,
    ← (graphIntersectionKernelEquiv f g).finrank_eq]
  have h := LinearMap.finrank_range_add_finrank_ker (f - g)
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Matrix-graph intersection codimension is the matrix rank of the difference. -/
theorem matrixGraph_intersectionCodimension (A B : Matrix ι ι K) :
    intersectionCodimension A.mulVecLin.graph B.mulVecLin.graph = (A - B).rank := by
  rw [graph_intersectionCodimension]
  have heq : (A - B).mulVecLin = A.mulVecLin - B.mulVecLin := by
    apply LinearMap.ext
    intro v
    exact Matrix.sub_mulVec A B v
  change _ = finrank K (A - B).mulVecLin.range
  rw [heq]

/-- Two alternating matrix graphs always have even intersection defect. -/
theorem alternatingGraph_even_defect {A B : Matrix ι ι K}
    (hA : IsAlternatingMatrix A) (hB : IsAlternatingMatrix B) :
    Even (intersectionCodimension A.mulVecLin.graph B.mulVecLin.graph) := by
  rw [matrixGraph_intersectionCodimension]
  apply IsAlternatingMatrix.even_rank
  intro v
  rw [Matrix.sub_mulVec, dotProduct_sub, hA v, hB v, sub_zero]

#print axioms graph_intersectionCodimension
#print axioms matrixGraph_intersectionCodimension
#print axioms alternatingGraph_even_defect
end GaloisForLFunctions.HTGeometry.LinearAlgebra
