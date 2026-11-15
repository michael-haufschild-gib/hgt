import GaloisForLFunctions.HTGeometry.LinearAlgebra.HyperbolicMatrixGraphs
import GaloisForLFunctions.HTGeometry.LinearAlgebra.BinarySelmerCompletion

/-!
# A binary cube of quadratic Lagrangians

The graphs of the binary Selmer completion matrices are distinct quadratic
Lagrangians. Their intersection codimension is twice the Hamming distance between
diagonal choices, independently of the initial matrix and rank-one correction.
Consequently their intersection dimension is twice the number of unchanged entries.
-/

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
open Matrix Module
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A cross-diagonal block has rank twice the support size of its diagonal. -/
theorem rank_crossDiagonal (d : ι → K) :
    (fromBlocks (0 : Matrix ι ι K) (diagonal d) (diagonal d) 0).rank =
      2 * Nat.card {i // d i ≠ 0} := by
  classical
  rw [Nat.card_eq_fintype_card]
  have heq : fromBlocks (0 : Matrix ι ι K) (diagonal d) (diagonal d) 0 =
      (diagonal (Sum.elim d d)).submatrix (Equiv.sumComm ι ι) (Equiv.refl (ι ⊕ ι)) := by
    ext (i | i) (j | j) <;> simp [submatrix, diagonal, fromBlocks]
  rw [heq, rank_submatrix, rank_diagonal]
  let e : {s : ι ⊕ ι // Sum.elim d d s ≠ 0} ≃
      ({i // d i ≠ 0} ⊕ {i // d i ≠ 0}) :=
    { toFun := fun s => match s with
        | ⟨Sum.inl i, hi⟩ => Sum.inl ⟨i, hi⟩
        | ⟨Sum.inr i, hi⟩ => Sum.inr ⟨i, hi⟩
      invFun := fun s => match s with
        | Sum.inl i => ⟨Sum.inl i.val, i.property⟩
        | Sum.inr i => ⟨Sum.inr i.val, i.property⟩
      left_inv := by rintro ⟨i | i, hi⟩ <;> rfl
      right_inv := by rintro (i | i) <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum, two_mul]

omit [Fintype ι] in
private theorem binary_add_diagonal_transpose (A : Matrix ι ι (ZMod 2)) (ε : ι → ZMod 2) :
    (A + diagonal ε) + (A + diagonal ε)ᵀ = A + Aᵀ := by
  rw [transpose_add, diagonal_transpose]
  have hd : diagonal ε + diagonal ε = (0 : Matrix ι ι (ZMod 2)) := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  calc
    (A + diagonal ε) + (Aᵀ + diagonal ε) =
        (A + Aᵀ) + (diagonal ε + diagonal ε) := by abel
    _ = _ := by rw [hd, add_zero]

omit [Fintype ι] in
/-- Changing the diagonal choice leaves only a cross-diagonal difference. -/
theorem binarySelmerMatrix_sub (A : Matrix ι ι (ZMod 2)) (z ε η : ι → ZMod 2) :
    binarySelmerMatrix A z ε - binarySelmerMatrix A z η =
      fromBlocks 0 (diagonal (ε - η)) (diagonal (ε - η)) 0 := by
  dsimp only [binarySelmerMatrix]
  rw [binary_add_diagonal_transpose, binary_add_diagonal_transpose,
    transpose_add, transpose_add, diagonal_transpose, diagonal_transpose,
    sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  have hd (B : Matrix ι ι (ZMod 2)) :
      (B + diagonal ε) + -(B + diagonal η) = diagonal (ε - η) := by
    calc
      (B + diagonal ε) + -(B + diagonal η) = diagonal ε - diagonal η := by abel
      _ = diagonal (ε - η) := diagonal_sub ε η
  rw [add_neg_cancel, hd, hd, add_neg_cancel]

/-- The distance between any two diagonal choices is twice their Hamming distance. -/
theorem binarySelmerGraph_intersectionCodimension
    (A : Matrix ι ι (ZMod 2)) (z ε η : ι → ZMod 2) :
    intersectionCodimension (binarySelmerMatrix A z ε).mulVecLin.graph
      (binarySelmerMatrix A z η).mulVecLin.graph =
        2 * Fintype.card {i // ε i ≠ η i} := by
  rw [matrixGraph_intersectionCodimension, binarySelmerMatrix_sub, rank_crossDiagonal]
  simp only [Nat.card_eq_fintype_card, Pi.sub_apply, sub_ne_zero]

/-- Every member of the binary Selmer family is a quadratic Lagrangian graph. -/
theorem binarySelmerGraph_isQuadraticLagrangian
    (A : Matrix ι ι (ZMod 2)) (z ε : ι → ZMod 2) :
    IsQuadraticLagrangian hyperbolicMatrixQuadratic
      (binarySelmerMatrix A z ε).mulVecLin.graph :=
  (isAlternatingMatrix_binarySelmerMatrix A z ε).graph_isQuadraticLagrangian

/-- Intersections lose exactly two dimensions for each changed diagonal entry. -/
theorem finrank_binarySelmerGraph_intersection
    (A : Matrix ι ι (ZMod 2)) (z ε η : ι → ZMod 2) :
    finrank (ZMod 2) ↥((binarySelmerMatrix A z ε).mulVecLin.graph ⊓
      (binarySelmerMatrix A z η).mulVecLin.graph) =
        2 * (Fintype.card ι - Fintype.card {i // ε i ≠ η i}) := by
  have hd := binarySelmerGraph_intersectionCodimension A z ε η
  rw [intersectionCodimension_eq, linearMap_graph_finrank] at hd
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at hd
  have hle : finrank (ZMod 2) ↥((binarySelmerMatrix A z ε).mulVecLin.graph ⊓
      (binarySelmerMatrix A z η).mulVecLin.graph) ≤
      finrank (ZMod 2) (binarySelmerMatrix A z ε).mulVecLin.graph :=
    Submodule.finrank_mono inf_le_left
  rw [linearMap_graph_finrank] at hle
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at hle
  omega

/-- Distinct diagonal choices give distinct quadratic Lagrangian graphs. -/
theorem binarySelmerGraph_injective (A : Matrix ι ι (ZMod 2)) (z : ι → ZMod 2) :
    Function.Injective (fun ε => (binarySelmerMatrix A z ε).mulVecLin.graph) := by
  intro ε η heq
  change (binarySelmerMatrix A z ε).mulVecLin.graph =
    (binarySelmerMatrix A z η).mulVecLin.graph at heq
  have hd := binarySelmerGraph_intersectionCodimension A z ε η
  rw [heq, intersectionCodimension_eq, inf_idem, Nat.sub_self] at hd
  funext i
  by_contra hi
  have hpos : 0 < Fintype.card {i // ε i ≠ η i} :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  omega

#print axioms rank_crossDiagonal
#print axioms binarySelmerMatrix_sub
#print axioms binarySelmerGraph_intersectionCodimension
#print axioms binarySelmerGraph_isQuadraticLagrangian
#print axioms finrank_binarySelmerGraph_intersection
#print axioms binarySelmerGraph_injective
end GaloisForLFunctions.HTGeometry.LinearAlgebra
