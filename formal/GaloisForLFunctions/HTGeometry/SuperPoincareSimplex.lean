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

/-- Clifford generator attached to one simplex facet. -/
def simplexFacetSupercharge (n : ℕ) (i : Fin n) :
    CliffordAlgebra (simplexConstraintQuadraticForm (Fin n)) :=
  CliffordAlgebra.ι (simplexConstraintQuadraticForm (Fin n)) (Pi.single i 1)

/-- Each facet supercharge squares to unit translation. -/
theorem simplexFacetSupercharge_sq (n : ℕ) (i : Fin n) :
    simplexFacetSupercharge n i * simplexFacetSupercharge n i = 1 := by
  rw [simplexFacetSupercharge, CliffordAlgebra.ι_sq_scalar]
  have hq : simplexConstraintQuadraticForm (Fin n) (Pi.single i 1) = 1 := by
    simp [simplexConstraintQuadraticForm, Matrix.toQuadraticForm',
      LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
      Matrix.one_apply, Pi.single_apply]
  rw [hq]
  exact (algebraMap ℝ
    (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n)))).map_one

/-- Distinct facet supercharges have zero mixed anticommutator. -/
theorem simplexFacetSupercharge_anticommute (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    simplexFacetSupercharge n i * simplexFacetSupercharge n j +
      simplexFacetSupercharge n j * simplexFacetSupercharge n i = 0 := by
  rw [simplexFacetSupercharge, simplexFacetSupercharge,
    CliffordAlgebra.ι_mul_ι_add_swap]
  have hpolar : QuadraticMap.polar (simplexConstraintQuadraticForm (Fin n))
      (Pi.single i 1) (Pi.single j 1) = 0 := by
    simp [simplexConstraintQuadraticForm, QuadraticMap.polar,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, Matrix.one_apply, Pi.single_apply, hij, Ne.symm hij]
  rw [hpolar]
  exact (algebraMap ℝ
    (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n)))).map_zero

/-- Every finite simplex carries `n` extended supercharges with common unit momentum. -/
def simplexFacetD1Extended (n : ℕ) :
    SuperPoincare.D1Extended (Fin n)
      (CliffordAlgebra (simplexConstraintQuadraticForm (Fin n))) where
  supercharge := simplexFacetSupercharge n
  momentum := 1
  supercharge_sq := simplexFacetSupercharge_sq n
  mixed_anticommutator := simplexFacetSupercharge_anticommute n

end GaloisForLFunctions
