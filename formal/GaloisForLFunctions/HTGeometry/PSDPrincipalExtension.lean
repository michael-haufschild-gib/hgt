import GaloisForLFunctions.HTGeometry.RationalNonabelianContextAnomaly

/-!
# Positive principal extension by zero

Every finite positive semidefinite matrix extends to a larger index type by a zero block, with its
principal block and trace unchanged. Every matrix effect `0 ≤ E ≤ 1` likewise extends by zero,
with the complement acquiring an identity block. These are the exact linear-algebraic content of
face-surjectivity for states and effects; no ambient context-complex ontology is required.
-/

open Matrix
open scoped ComplexOrder Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive semidefinite matrix packaged with its certificate. -/
structure PSDMatrix (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : Matrix I I ℂ
  posSemidef : matrix.PosSemidef

/-- Extend a positive matrix by a zero block on a disjoint index type. -/
def PSDMatrix.zeroExtend {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : PSDMatrix I) : PSDMatrix (I ⊕ J) where
  matrix := contextBlockSum A.matrix 0
  posSemidef := contextBlockSum_posSemidef_iff.mpr ⟨A.posSemidef, Matrix.PosSemidef.zero⟩

/-- Zero extension is exactly surjective onto the original principal face. -/
theorem PSDMatrix.zeroExtend_principal {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : PSDMatrix I) :
    (A.zeroExtend (J := J)).matrix.submatrix Sum.inl Sum.inl = A.matrix := by
  rfl

/-- Zero extension preserves normalization traces exactly. -/
theorem PSDMatrix.zeroExtend_trace {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : PSDMatrix I) :
    (A.zeroExtend (J := J)).matrix.trace = A.matrix.trace := by
  simp [PSDMatrix.zeroExtend, contextBlockSum, Matrix.trace, Fintype.sum_sum_type]

/-- Finite matrix effect, intrinsically packaging `0 ≤ E ≤ 1`. -/
structure MatrixEffect (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : Matrix I I ℂ
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

/-- Extend an effect by zero; its complement is `(1-E) ⊕ 1`. -/
def MatrixEffect.zeroExtend {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (E : MatrixEffect I) : MatrixEffect (I ⊕ J) where
  matrix := contextBlockSum E.matrix 0
  positive := contextBlockSum_posSemidef_iff.mpr ⟨E.positive, Matrix.PosSemidef.zero⟩
  complement_positive := by
    have heq : (1 : Matrix (I ⊕ J) (I ⊕ J) ℂ) - contextBlockSum E.matrix 0 =
        contextBlockSum (1 - E.matrix) 1 := by
      ext x y
      cases x <;> cases y <;> simp [contextBlockSum, Matrix.fromBlocks, Matrix.one_apply]
    rw [heq, contextBlockSum_posSemidef_iff]
    exact ⟨E.complement_positive, Matrix.PosSemidef.one⟩

/-- Effect zero extension is exactly surjective onto the original principal face. -/
theorem MatrixEffect.zeroExtend_principal {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (E : MatrixEffect I) :
    (E.zeroExtend (J := J)).matrix.submatrix Sum.inl Sum.inl = E.matrix := by
  rfl

end

end GaloisForLFunctions.HTGeometry
