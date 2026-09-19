import GaloisForLFunctions.HTGeometry.LamzouriAlgebraicallyClosedPolynomialRoots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Lamzouri collision bounds for finite matrix spectra

Applying the polynomial root inequalities to a characteristic polynomial
turns algebraic eigenvalue multiplicities into a finite spectral collision
energy.  No normality or Hermitian hypothesis is needed.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HilbertMetric

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distinct algebraic eigenvalues of a finite complex matrix. -/
def matrixEigenvalueSupport (H : Matrix ι ι ℂ) : Finset ℂ :=
  algebraicallyClosedPolynomialRootSupport H.charpoly

/-- Algebraic eigenvalue multiplicity in the characteristic polynomial. -/
def matrixEigenvalueMultiplicity (H : Matrix ι ι ℂ) (z : ℂ) : ℕ :=
  algebraicallyClosedPolynomialRootMultiplicity H.charpoly z

/-- Squared algebraic-multiplicity collision energy of a matrix spectrum. -/
def matrixEigenvalueCollisionMass (H : Matrix ι ι ℂ) : ℝ :=
  algebraicallyClosedPolynomialRootCollisionMass H.charpoly

/-- Algebraically simple eigenvalues of a finite complex matrix. -/
def matrixSimpleEigenvalueSupport (H : Matrix ι ι ℂ) : Finset ℂ :=
  algebraicallyClosedPolynomialSimpleRootSupport H.charpoly

/-- Total algebraic eigenvalue multiplicity is matrix dimension. -/
theorem matrixEigenvalueMultiplicityMass_eq_dim (H : Matrix ι ι ℂ) :
    finiteMultiplicityMass (matrixEigenvalueSupport H)
        (matrixEigenvalueMultiplicity H) = Fintype.card ι := by
  change finiteMultiplicityMass
      (algebraicallyClosedPolynomialRootSupport H.charpoly)
      (algebraicallyClosedPolynomialRootMultiplicity H.charpoly) = _
  simpa only [Matrix.charpoly_natDegree_eq_dim] using
    algebraicallyClosedPolynomialRootMultiplicityMass_eq H.charpoly

/-- Algebraically simple eigenvalues dominate twice dimension minus spectral
collision energy. -/
theorem matrixSimpleEigenvalueSupport_lower (H : Matrix ι ι ℂ) :
    2 * (Fintype.card ι : ℝ) - matrixEigenvalueCollisionMass H ≤
      (matrixSimpleEigenvalueSupport H).card := by
  simpa only [matrixEigenvalueCollisionMass, matrixSimpleEigenvalueSupport,
    Matrix.charpoly_natDegree_eq_dim] using
    algebraicallyClosedPolynomialSimpleRootSupport_lower H.charpoly

/-- Distinct algebraic eigenvalues dominate Lamzouri's rank--trace
expression. -/
theorem matrixDistinctEigenvalueSupport_lower (H : Matrix ι ι ℂ) :
    (3 / 2 : ℝ) * (Fintype.card ι : ℝ) -
        (1 / 2 : ℝ) * matrixEigenvalueCollisionMass H ≤
      (matrixEigenvalueSupport H).card := by
  simpa only [matrixEigenvalueCollisionMass, matrixEigenvalueSupport,
    Matrix.charpoly_natDegree_eq_dim] using
    algebraicallyClosedPolynomialDistinctRootSupport_lower H.charpoly

/-- Matrix dimension is a lower bound for algebraic spectral collision
energy. -/
theorem matrixDimension_le_eigenvalueCollisionMass (H : Matrix ι ι ℂ) :
    (Fintype.card ι : ℝ) ≤ matrixEigenvalueCollisionMass H := by
  simpa only [matrixEigenvalueCollisionMass,
    Matrix.charpoly_natDegree_eq_dim] using
    algebraicallyClosedPolynomialRootDegree_le_collisionMass H.charpoly

end

end GaloisForLFunctions.HTGeometry
