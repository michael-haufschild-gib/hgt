import GaloisForLFunctions.HTGeometry.GomesPolynomialOrbitCoordinates
import GaloisForLFunctions.HTGeometry.SourceCoboundaryModule
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# A free polynomial module underlying each nonconstant connection

Let the new polynomial variable act as the connection operator. The orbit coordinate
map is then polynomial-linear and identifies this operator module with a finite free
module. Its rank is exactly the degree of the original coefficient, and its basis is
given by the low-degree monomial seeds.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Polynomials viewed as a module on which the polynomial variable acts by the connection. -/
abbrev GomesPolynomialConnectionModule (A : GomesNonconstantPolynomialCoefficient) :=
  Module.AEval' (gomesPolynomialFirstOrderLinearMap A.val)

/-- The full orbit coordinate equivalence is linear over the polynomial operator ring. -/
def gomesPolynomialConnectionModuleCoordinates (A : GomesNonconstantPolynomialCoefficient) :
    GomesPolynomialConnectionModule A ≃ₗ[ℝ[X]] (Fin A.val.natDegree → ℝ[X]) :=
  LinearEquiv.ofAEval (gomesPolynomialFirstOrderLinearMap A.val)
    (gomesPolynomialConnectionOrbitCoordinates A) fun P =>
      gomesPolynomialConnectionOrbitCoordinates_operator A P

/-- The polynomial-linear equivalence extends the actual real-linear orbit coordinates. -/
theorem gomesPolynomialConnectionModuleCoordinates_of
    (A : GomesNonconstantPolynomialCoefficient) (P : ℝ[X]) :
    gomesPolynomialConnectionModuleCoordinates A
      ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A.val)) P) =
        gomesPolynomialConnectionOrbitCoordinates A P := rfl

/-- Each standard free generator corresponds to the matching low-degree monomial seed. -/
theorem gomesPolynomialConnectionModuleCoordinates_symm_single
    (A : GomesNonconstantPolynomialCoefficient) (j : Fin A.val.natDegree) :
    (gomesPolynomialConnectionModuleCoordinates A).symm (Pi.single j 1) =
      (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A.val)) (X ^ j.val) := by
  apply (gomesPolynomialConnectionModuleCoordinates A).injective
  rw [LinearEquiv.apply_symm_apply, gomesPolynomialConnectionModuleCoordinates_of,
    gomesPolynomialConnectionOrbitCoordinates_seed]

/-- The low-degree seeds form a basis over the polynomial ring of connection operators. -/
def gomesPolynomialConnectionModuleBasis (A : GomesNonconstantPolynomialCoefficient) :
    Module.Basis (Fin A.val.natDegree) ℝ[X] (GomesPolynomialConnectionModule A) :=
  (Pi.basisFun ℝ[X] (Fin A.val.natDegree)).map
    (gomesPolynomialConnectionModuleCoordinates A).symm

/-- The operator-module basis consists exactly of the monomials below coefficient degree. -/
theorem gomesPolynomialConnectionModuleBasis_apply
    (A : GomesNonconstantPolynomialCoefficient) (j : Fin A.val.natDegree) :
    gomesPolynomialConnectionModuleBasis A j =
      (Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A.val)) (X ^ j.val) := by
  rw [gomesPolynomialConnectionModuleBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    gomesPolynomialConnectionModuleCoordinates_symm_single]

/-- Nonconstant polynomial connections define free modules over their polynomial operator rings. -/
instance gomesPolynomialConnectionModule_free (A : GomesNonconstantPolynomialCoefficient) :
    Module.Free ℝ[X] (GomesPolynomialConnectionModule A) :=
  Module.Free.of_basis (gomesPolynomialConnectionModuleBasis A)

/-- There are finitely many polynomial-module generators, even though real dimension is infinite. -/
instance gomesPolynomialConnectionModule_finite (A : GomesNonconstantPolynomialCoefficient) :
    Module.Finite ℝ[X] (GomesPolynomialConnectionModule A) :=
  Module.Finite.of_basis (gomesPolynomialConnectionModuleBasis A)

/-- Polynomial-module rank recovers the coefficient degree exactly. -/
theorem gomesPolynomialConnectionModule_finrank (A : GomesNonconstantPolynomialCoefficient) :
    Module.finrank ℝ[X] (GomesPolynomialConnectionModule A) = A.val.natDegree := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (gomesPolynomialConnectionModuleBasis A)

/-- Every polynomial in the connection acts as the same scalar polynomial on all orbit coordinates. -/
theorem gomesPolynomialConnectionOrbitCoordinates_aeval
    (A : GomesNonconstantPolynomialCoefficient) (F P : ℝ[X]) :
    gomesPolynomialConnectionOrbitCoordinates A
      ((Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A.val)) F P) =
        F • gomesPolynomialConnectionOrbitCoordinates A P := by
  have h := (gomesPolynomialConnectionModuleCoordinates A).map_smul F
    ((Module.AEval'.of (gomesPolynomialFirstOrderLinearMap A.val)) P)
  rw [smul_aEval_of] at h
  simpa only [gomesPolynomialConnectionModuleCoordinates_of] using h

end GaloisForLFunctions.HTGeometry
