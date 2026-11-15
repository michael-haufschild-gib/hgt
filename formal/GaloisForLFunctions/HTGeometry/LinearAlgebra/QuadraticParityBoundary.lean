import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinaryQuadraticGraphs

/-!
# The quadratic boundary of Lagrangian intersection parity

The three lines of the binary symplectic plane are polar self-orthogonal and
have pairwise intersection defect one. They violate the quadratic parity
cocycle because the diagonal line is not totally singular for the quadratic
form. Graph classification identifies the precise missing condition.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
open LinearMap (BilinForm)

/-- The vertical coordinate subspace, complementary to every linear graph. -/
def verticalGraphPole (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Submodule K (V × V) := (LinearMap.fst K V V).ker

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem graph_inf_verticalGraphPole (f : V →ₗ[K] V) :
    f.graph ⊓ verticalGraphPole K V = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  have hfst : v.1 = 0 := hv.2
  have hsnd : v.2 = f v.1 := hv.1
  rw [hfst, map_zero] at hsnd
  exact Prod.ext hfst hsnd

/-- Every graph is transverse to the vertical pole. -/
theorem graph_vertical_intersectionCodimension [FiniteDimensional K V] (f : V →ₗ[K] V) :
    intersectionCodimension f.graph (verticalGraphPole K V) = finrank K V := by
  rw [intersectionCodimension_eq, graph_inf_verticalGraphPole,
    finrank_bot, Nat.sub_zero, linearMap_graph_finrank]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vertical pole is a quadratic Lagrangian for the split quadratic form. -/
theorem verticalGraphPole_isQuadraticLagrangian :
    IsQuadraticLagrangian (hyperbolicMatrixQuadratic (K := K) (ι := ι))
      (verticalGraphPole K (ι → K)) := by
  constructor
  · intro v hv
    change v.1 = 0 at hv
    rw [hyperbolicMatrixQuadratic_apply, hv, zero_dotProduct]
  · apply le_antisymm
    · intro v hv
      change v.1 = 0
      ext i
      have h := hv (0, Pi.single i 1) rfl
      rw [hyperbolicMatrixQuadratic_polar] at h
      simpa [dotProduct, Pi.single_apply] using h
    · intro v hv w hw
      change v.1 = 0 at hv
      change w.1 = 0 at hw
      rw [hyperbolicMatrixQuadratic_polar, hv, hw, zero_dotProduct, zero_dotProduct, add_zero]

/-- In characteristic two the split polar form is symplectic. -/
theorem binary_hyperbolic_polar_isAlt :
    (hyperbolicMatrixQuadratic (K := ZMod 2) (ι := ι)).polarBilin.IsAlt := by
  intro v
  rw [hyperbolicMatrixQuadratic_polar, CharTwo.add_self_eq_zero]

abbrev BinaryBoundarySpace := (Fin 1 → ZMod 2) × (Fin 1 → ZMod 2)

/-- The horizontal line in the binary symplectic plane. -/
def binaryBoundaryHorizontal : Submodule (ZMod 2) BinaryBoundarySpace :=
  (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph

/-- The diagonal line in the binary symplectic plane. -/
def binaryBoundaryDiagonal : Submodule (ZMod 2) BinaryBoundarySpace :=
  (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph

/-- The vertical line in the binary symplectic plane. -/
def binaryBoundaryVertical : Submodule (ZMod 2) BinaryBoundarySpace :=
  verticalGraphPole (ZMod 2) (Fin 1 → ZMod 2)

/-- Three self-orthogonal subspaces of one nondegenerate alternating space. -/
theorem binaryBoundary_polarLagrangians :
    (hyperbolicMatrixQuadratic (K := ZMod 2) (ι := Fin 1)).polarBilin.Nondegenerate ∧
    (hyperbolicMatrixQuadratic (K := ZMod 2) (ι := Fin 1)).polarBilin.IsAlt ∧
    BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin binaryBoundaryHorizontal =
      binaryBoundaryHorizontal ∧
    BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin binaryBoundaryDiagonal =
      binaryBoundaryDiagonal ∧
    BilinForm.orthogonal hyperbolicMatrixQuadratic.polarBilin binaryBoundaryVertical =
      binaryBoundaryVertical := by
  refine ⟨hyperbolicMatrixQuadratic_nondegenerate, binary_hyperbolic_polar_isAlt, ?_, ?_, ?_⟩
  · exact (isAlternatingMatrix_zero (F := ZMod 2) (ι := Fin 1)).graph_isQuadraticLagrangian.2
  · exact binarySymmetricGraph_selfOrthogonal 1 Matrix.isSymm_one
  · exact (verticalGraphPole_isQuadraticLagrangian (K := ZMod 2) (ι := Fin 1)).2

/-- Every pair among these three lines has intersection defect one. -/
theorem binaryBoundary_pairwise_defects :
    intersectionCodimension binaryBoundaryHorizontal binaryBoundaryDiagonal = 1 ∧
    intersectionCodimension binaryBoundaryDiagonal binaryBoundaryVertical = 1 ∧
    intersectionCodimension binaryBoundaryHorizontal binaryBoundaryVertical = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change intersectionCodimension (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph
      (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph = 1
    rw [matrixGraph_intersectionCodimension, zero_sub]
    have hn : -(1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) = 1 := by
      ext i j
      exact CharTwo.neg_eq _
    rw [hn, rank_one, Fintype.card_fin]
  · change intersectionCodimension (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph
      (verticalGraphPole (ZMod 2) (Fin 1 → ZMod 2)) = 1
    rw [graph_vertical_intersectionCodimension, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · change intersectionCodimension (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)).mulVecLin.graph
      (verticalGraphPole (ZMod 2) (Fin 1 → ZMod 2)) = 1
    rw [graph_vertical_intersectionCodimension, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Symplectic Lagrangians alone do not satisfy the quadratic parity cocycle. -/
theorem binaryBoundary_parity_cocycle_fails :
    intersectionCodimension binaryBoundaryHorizontal binaryBoundaryVertical % 2 ≠
      (intersectionCodimension binaryBoundaryHorizontal binaryBoundaryDiagonal +
        intersectionCodimension binaryBoundaryDiagonal binaryBoundaryVertical) % 2 := by
  obtain ⟨hxy, hyz, hxz⟩ := binaryBoundary_pairwise_defects
  rw [hxy, hyz, hxz]
  omega

/-- The missing quadratic condition is exactly the diagonal line's nonzero diagonal. -/
theorem binaryBoundary_diagonal_not_quadratic :
    ¬ IsQuadraticLagrangian hyperbolicMatrixQuadratic binaryBoundaryDiagonal := by
  rw [binaryBoundaryDiagonal,
    binarySymmetricGraph_isQuadraticLagrangian_iff _ Matrix.isSymm_one]
  intro h
  have h0 := congrFun h 0
  change (1 : ZMod 2) = 0 at h0
  exact one_ne_zero h0

/-- No change of nondegenerate quadratic form can make all three lines quadratic Lagrangians. -/
theorem binaryBoundary_no_common_quadratic_form :
    ¬ ∃ Q : QuadraticForm (ZMod 2) BinaryBoundarySpace,
      Q.polarBilin.Nondegenerate ∧
      IsQuadraticLagrangian Q binaryBoundaryHorizontal ∧
      IsQuadraticLagrangian Q binaryBoundaryDiagonal ∧
      IsQuadraticLagrangian Q binaryBoundaryVertical := by
  rintro ⟨Q, hQ, hX, hY, hZ⟩
  exact binaryBoundary_parity_cocycle_fails
    (quadraticLagrangian_defect_cocycle Q hQ hX hY hZ)

#print axioms binaryBoundary_polarLagrangians
#print axioms binaryBoundary_pairwise_defects
#print axioms binaryBoundary_parity_cocycle_fails
#print axioms binaryBoundary_diagonal_not_quadratic
#print axioms binaryBoundary_no_common_quadratic_form
end GaloisForLFunctions.HTGeometry.LinearAlgebra
