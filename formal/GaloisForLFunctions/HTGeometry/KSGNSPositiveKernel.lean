import GaloisForLFunctions.HTGeometry.CenteredKSGNSAlgebra
import GaloisForLFunctions.HTGeometry.StarOrderedConjugation

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A B ι : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [Fintype ι]

/-- The canonical Gram matrix attached to a finite family in a C⋆-algebra. -/
def cpGramMatrix (a : ι → A) : CStarMatrix ι ι A :=
  fun i j => star (a i) * a j

/-- A C⋆-algebraic Gram matrix is positive, including for an empty index type. -/
theorem cpGramMatrix_nonneg (a : ι → A) : 0 ≤ cpGramMatrix a := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      have hz : cpGramMatrix a = 0 := by
        ext i
        exact isEmptyElim i
      rw [hz]
  | inr h =>
      letI := h
      let k : ι := Classical.choice h
      let X : CStarMatrix ι ι A := fun i j => if i = k then a j else 0
      have hX : star X * X = cpGramMatrix a := by
        ext i j
        rw [CStarMatrix.mul_apply]
        simp only [CStarMatrix.star_apply, X]
        rw [Finset.sum_eq_single k]
        · simp [cpGramMatrix]
        · intro q _ hq
          simp [hq]
        · simp
      rw [← hX]
      exact star_mul_self_nonneg X

/-- The finite quadratic form defining the Paschke--KSGNS inner product. -/
def cpGramQuadratic (phi : A →CP B) (a : ι → A) (b : ι → B) : B :=
  ∑ i, ∑ j, star (b i) * phi (star (a i) * a j) * b j

/-- Complete positivity makes every finite Paschke--KSGNS quadratic form positive. -/
theorem cpGramQuadratic_nonneg (phi : A →CP B) (a : ι → A) (b : ι → B) :
    0 ≤ cpGramQuadratic phi a b := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      simp [cpGramQuadratic]
  | inr h =>
      letI := h
      let k : ι := Classical.choice h
      let N : CStarMatrix ι ι B := (cpGramMatrix a).map phi
      have hN : 0 ≤ N := CompletelyPositiveMap.map_cstarMatrix_nonneg phi
        (cpGramMatrix a) (cpGramMatrix_nonneg a)
      let V : CStarMatrix ι ι B := fun i j => if j = k then b i else 0
      have hq : cpGramQuadratic phi a b = (star V * N * V) k k := by
        rw [CStarMatrix.mul_apply]
        simp only [V, if_pos]
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, N,
          CStarMatrix.map_apply, cpGramMatrix]
        simp only [if_true, Finset.sum_mul]
        exact Finset.sum_comm
      have hconj : 0 ≤ star V * N * V :=
        star_conjugate_nonneg_of_nonneg hN V
      rw [hq]
      exact cstarMatrix_diagonal_nonneg_of_nonneg _ hconj k

end GaloisForLFunctions.HTGeometry
