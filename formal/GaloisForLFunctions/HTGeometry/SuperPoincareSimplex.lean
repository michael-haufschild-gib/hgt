import GaloisForLFunctions.HTGeometry.SimplexConstraintDirac
import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra

/-!
# Super-Poincare certificate for simplex constraint Dirac elements

The full-simplex Clifford Dirac element is an `N = 1` supercharge.  Its translation generator is
the scalar facet cardinality.  Thus the corpus simplex Hodge gap is exactly a positive-momentum
one-dimensional Super-Poincare representation for every finite simplex.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The `n`-facet simplex Dirac element as an `N = 1` supertranslation certificate. -/
def simplexConstraintD1N1 (n : ℕ) :
    SuperPoincare.D1N1
      (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n))) where
  supercharge := simplexConstraintDiracElement (Fin n)
  momentum :=
    algebraMap ℝ (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n))) (n : ℝ)
  supercharge_sq := by
    simpa using simplexConstraintDiracElement_sq (Fin n)

/-- The induced translation is exactly facet cardinality, not a new hypothesis. -/
theorem simplexConstraintD1N1_momentum (n : ℕ) :
    (simplexConstraintD1N1 n).momentum =
      algebraMap ℝ (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n))) (n : ℝ) :=
  rfl

end GaloisForLFunctions
