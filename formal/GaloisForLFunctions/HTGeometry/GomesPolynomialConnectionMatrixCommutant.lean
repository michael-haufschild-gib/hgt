import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionCommutant
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The full symmetry algebra is a polynomial matrix algebra

For coefficient degree `m > 0`, there are exactly `m` independent connection orbit
chains. All commuting real-linear maps are polynomial matrices mixing these chains.
The column formula identifies the matrix directly from images of the monomial seeds.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The full commutant of a degree-m connection is the m-by-m polynomial matrix algebra. -/
def gomesPolynomialConnectionCommutantMatrixEquiv
    (A : GomesNonconstantPolynomialCoefficient) :
    GomesPolynomialConnectionCommutant A.val ≃ₐ[ℝ]
      Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X] :=
  (gomesPolynomialConnectionCommutantModuleEquiv A.val).trans
    (((gomesPolynomialConnectionModuleCoordinates A).conjAlgEquiv ℝ).trans
      ((LinearMap.toMatrixAlgEquiv' :
        Module.End ℝ[X] (Fin A.val.natDegree → ℝ[X]) ≃ₐ[ℝ[X]]
          Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X]).restrictScalars ℝ))

set_option maxRecDepth 2048 in
/-- A symmetry matrix is determined by the orbit coordinates of its monomial-seed images. -/
theorem gomesPolynomialConnectionCommutantMatrixEquiv_apply
    (A : GomesNonconstantPolynomialCoefficient)
    (E : GomesPolynomialConnectionCommutant A.val) (i j : Fin A.val.natDegree) :
    gomesPolynomialConnectionCommutantMatrixEquiv A E i j =
      gomesPolynomialConnectionOrbitCoordinates A (E.val (X ^ j.val)) i := by
  change (gomesPolynomialConnectionModuleCoordinates A
    (gomesPolynomialCommutantToModuleEnd A.val E
      ((gomesPolynomialConnectionModuleCoordinates A).symm (Pi.single j 1)))) i = _
  rw [gomesPolynomialConnectionModuleCoordinates_symm_single,
    gomesPolynomialCommutantToModuleEnd_apply, gomesPolynomialConnectionModuleCoordinates_of]

/-- Every polynomial matrix is realized by a unique commuting real-linear map. -/
theorem gomesPolynomialConnectionCommutantMatrix_exists_unique
    (A : GomesNonconstantPolynomialCoefficient)
    (M : Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X]) :
    ∃! E : GomesPolynomialConnectionCommutant A.val,
      gomesPolynomialConnectionCommutantMatrixEquiv A E = M :=
  (gomesPolynomialConnectionCommutantMatrixEquiv A).bijective.existsUnique M

/-- Polynomial expressions in the connection are precisely the corresponding scalar matrices. -/
theorem gomesPolynomialConnectionPolynomialSymmetry_matrix
    (A : GomesNonconstantPolynomialCoefficient) (F : ℝ[X]) :
    gomesPolynomialConnectionCommutantMatrixEquiv A
      (gomesPolynomialConnectionPolynomialSymmetry A.val F) =
        Matrix.diagonal (fun _ => F) := by
  apply Matrix.ext
  intro i j
  rw [gomesPolynomialConnectionCommutantMatrixEquiv_apply]
  change gomesPolynomialConnectionOrbitCoordinates A
    ((Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A.val)) F (X ^ j.val)) i = _
  rw [gomesPolynomialConnectionOrbitCoordinates_aeval,
    gomesPolynomialConnectionOrbitCoordinates_seed]
  simp [Pi.smul_apply, Pi.single_apply, Matrix.diagonal_apply]

/-- A nonconstant connection has no relation identifying two distinct operator polynomials. -/
theorem gomesPolynomialConnectionPolynomialSymmetry_injective
    (A : GomesNonconstantPolynomialCoefficient) :
    Function.Injective (gomesPolynomialConnectionPolynomialSymmetry A.val) := by
  intro F G h
  have hm := congrArg (gomesPolynomialConnectionCommutantMatrixEquiv A) h
  rw [gomesPolynomialConnectionPolynomialSymmetry_matrix,
    gomesPolynomialConnectionPolynomialSymmetry_matrix] at hm
  let j : Fin A.val.natDegree := ⟨0, gomesNonconstantPolynomialCoefficient_degree_pos A⟩
  have hj := congrArg (fun M : Matrix (Fin A.val.natDegree) (Fin A.val.natDegree) ℝ[X] =>
    M j j) hm
  simpa only [Matrix.diagonal_apply_eq] using hj

/-- Evaluation at the connection is an injective polynomial algebra representation. -/
theorem gomesPolynomialConnection_aeval_injective
    (A : GomesNonconstantPolynomialCoefficient) :
    Function.Injective (Polynomial.aeval (R := ℝ) (gomesPolynomialFirstOrderLinearMap A.val)) := by
  intro F G h
  apply gomesPolynomialConnectionPolynomialSymmetry_injective A
  exact Subtype.ext h

/-- No nonzero polynomial annihilates a nonconstant connection operator. -/
theorem gomesPolynomialConnection_aeval_eq_zero_iff
    (A : GomesNonconstantPolynomialCoefficient) (F : ℝ[X]) :
    (Polynomial.aeval (gomesPolynomialFirstOrderLinearMap A.val)) F = 0 ↔ F = 0 := by
  constructor
  · intro h
    apply gomesPolynomialConnection_aeval_injective A
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

end GaloisForLFunctions.HTGeometry
