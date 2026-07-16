import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The Dirac square of a full constraint simplex

The monomial blocks of a coordinate-facet descent complex are augmented cochain complexes of
full simplices.  Their Hermitian Hodge operator is exterior creation plus annihilation by the
all-facet vector.  This file formalizes the finite Clifford-algebra core: its square is exactly the
number of facets.  In particular every nonempty simplex block has a positive scalar Dirac square.

The weighted Hilbert direct sum and the identification with the completed facet complex are kept
outside this finite algebraic module.
-/

open scoped BigOperators

namespace GaloisForLFunctions

/-- The Euclidean quadratic form on the real facet-coordinate space. -/
noncomputable def simplexConstraintQuadraticForm (ι : Type*) [Fintype ι] [DecidableEq ι] :
    QuadraticForm ℝ (ι → ℝ) :=
  (1 : Matrix ι ι ℝ).toQuadraticForm'

/-- The sum of all orthonormal facet-coordinate vectors. -/
def simplexConstraintVector (ι : Type*) : ι → ℝ := fun _ => 1

/-- The squared length of the all-facet vector is the number of facets. -/
theorem simplexConstraintQuadraticForm_vector
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    simplexConstraintQuadraticForm ι (simplexConstraintVector ι) =
      (Fintype.card ι : ℝ) := by
  simp [simplexConstraintQuadraticForm, simplexConstraintVector,
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, Matrix.one_apply]

/-- Clifford multiplication by the all-facet vector, the finite simplex Dirac element. -/
noncomputable def simplexConstraintDiracElement
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    CliffordAlgebra (simplexConstraintQuadraticForm ι) :=
  CliffordAlgebra.ι (simplexConstraintQuadraticForm ι) (simplexConstraintVector ι)

/-- **Full-simplex Dirac square.**  The square is the scalar cardinality of the facet set. -/
theorem simplexConstraintDiracElement_sq
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    simplexConstraintDiracElement ι * simplexConstraintDiracElement ι =
      algebraMap ℝ (CliffordAlgebra (simplexConstraintQuadraticForm ι))
        (Fintype.card ι : ℝ) := by
  rw [simplexConstraintDiracElement, CliffordAlgebra.ι_sq_scalar]
  congr 1
  exact simplexConstraintQuadraticForm_vector ι

/-- Left Clifford multiplication by the simplex Dirac element squares to the facet-cardinality
scalar on every state.  This is the algebraic block form of the simplex Hodge gap. -/
theorem simplexConstraintDirac_square_apply
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (x : CliffordAlgebra (simplexConstraintQuadraticForm ι)) :
    simplexConstraintDiracElement ι * (simplexConstraintDiracElement ι * x) =
      (Fintype.card ι : ℝ) • x := by
  rw [← mul_assoc, simplexConstraintDiracElement_sq, Algebra.smul_def]

end GaloisForLFunctions
