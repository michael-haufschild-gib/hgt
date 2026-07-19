import GaloisForLFunctions.HTGeometry.LeafContinuityInfty
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface

/-!
# The classical N-extremal Nevanlinna family, constructed

Every field of `ClassicalNevanlinnaExtremalFamily` has been built from the moment sequence alone: the
matrix from the orthogonal polynomials, its denominator row's continuity from entirety of the limiting
entries, the leaves from quasi-orthogonal quadrature, their carriers from the denominator fibers,
their moments from the quadrature exactness, and their weak continuity in the parameter from
tightness together with uniqueness.

The hypotheses are that the moment form is positive definite, normalised, and has bounded kernel at
one point — that is, that the Hamburger moment problem for `s` is indeterminate.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The classical N-extremal Nevanlinna family of an indeterminate moment problem.** -/
noncomputable def nevExtremalFamily (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s where
  matrix := nevMatrixDataInf h h0b
  continuous_B := continuous_nevMatrixDataInf_B h h0b
  continuous_D := continuous_nevMatrixDataInf_D h h0b
  leaf := nevLeaf h h0b h0
  continuous_leaf := continuous_nevLeaf h h0b h0
  finite_carried := nevLeaf_finite_carried h h0b h0
  infinity_carried := nevLeaf_infinity_carried h h0b h0
  leaf_moments := nevLeaf_hasHamburgerMoments h h0b h0

@[simp] theorem nevExtremalFamily_matrix (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : (nevExtremalFamily h h0b h0).matrix = nevMatrixDataInf h h0b := rfl

@[simp] theorem nevExtremalFamily_leaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) : (nevExtremalFamily h h0b h0).leaf = nevLeaf h h0b h0 := rfl

/-- **Existence of the classical family.**  A positive definite normalised moment sequence whose
kernel is bounded at a point carries a classical N-extremal Nevanlinna family. -/
theorem exists_classicalNevanlinnaExtremalFamily (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Nonempty (GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s) :=
  ⟨nevExtremalFamily h h0b h0⟩

/-- **The weights of every leaf are the Christoffel limits.**  The geometric content the family does
not itself record. -/
theorem nevExtremalFamily_atoms (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {ξ : ℝ}
    (hξ : ξ ∈ (nevExtremalFamily h h0b h0).matrix.finiteDenominatorFiber tau) :
    ((nevExtremalFamily h h0b h0).leaf (tau : OnePoint ℝ) : Measure ℝ) {ξ}
      = ENNReal.ofReal (christoffelLimit s ξ) :=
  nevLeaf_atoms h h0b h0 tau hξ

end HTGeometry
