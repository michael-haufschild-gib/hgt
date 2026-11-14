import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Polynomial uniqueness for hexablock and tetrablock coordinates

The two polynomial parametrizations have nonzero Jacobian determinants.
The corpus's characteristic-zero Jacobian criterion therefore makes their
coordinate families algebraically independent: substitution loses no
polynomial information. The determinant factorizations also identify the
critical loci of both parametrizations.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.HexablockPolynomial
open MvPolynomial Matrix

/-- Polynomial form of the hexablock parametrization. -/
def hex : Fin 4 → MvPolynomial (Fin 4) ℂ :=
  ![C (1/2) * X 2 * (X 0 - 1), C (1/2) * X 1 * (X 0 + 1),
    C (1/2) * X 2 * X 3 * (X 0 + 1), X 0 * X 1 * X 2 * X 3]

/-- Polynomial form of the tetrablock parametrization. -/
def tetra : Fin 3 → MvPolynomial (Fin 3) ℂ :=
  ![C (1/2) * X 2 * (X 0 + X 1), C (1/2) * (X 0 + X 1), X 0 * X 1 * X 2]

/-- The tetrablock Jacobian degenerates exactly on its three displayed factors. -/
lemma tetra_det : (polynomialJacobianMinor tetra id).det =
    C (1/4) * X 2 * (X 0 + X 1) * (X 0 - X 1) := by
  have hh : (C (1/4 : ℂ) : MvPolynomial (Fin 3) ℂ) = C (1/2 : ℂ) ^ 2 := by
    rw [← map_pow]
    congr 1
    norm_num
  rw [hh, Matrix.det_fin_three]
  simp [polynomialJacobianMinor, tetra, pderiv_X]
  ring

/-- The hexablock Jacobian factors into its coordinate and sum/difference degeneracies. -/
lemma hex_det : (polynomialJacobianMinor hex id).det =
    -C (1/8) * X 1 * X 2 ^ 2 * X 3 * (X 0 - 1) ^ 2 * (X 0 + 1) := by
  have hh : (C (1/8 : ℂ) : MvPolynomial (Fin 4) ℂ) = C (1/2 : ℂ) ^ 3 := by
    rw [← map_pow]
    congr 1
    norm_num
  rw [hh, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, polynomialJacobianMinor, hex, pderiv_X]
  ring

/-- The tetrablock coordinates satisfy no nonzero polynomial relation. -/
theorem tetra_algebraicIndependent : AlgebraicIndependent ℂ tetra := by
  apply algebraicIndependent_of_jacobian_det_ne_zero tetra id
  intro h
  have he := congrArg (eval (fun i : Fin 3 => if i = 1 then 0 else 1)) h
  rw [tetra_det] at he
  norm_num [Fin.ext_iff] at he

/-- The hexablock coordinates satisfy no nonzero polynomial relation. -/
theorem hex_algebraicIndependent : AlgebraicIndependent ℂ hex := by
  apply algebraicIndependent_of_jacobian_det_ne_zero hex id
  intro h
  have he := congrArg (eval (fun _ : Fin 4 => (2 : ℂ))) h
  rw [hex_det] at he
  norm_num at he

/-- Substitution by tetrablock coordinates preserves and reflects polynomial equality. -/
theorem tetra_substitution_injective : Function.Injective (aeval (R := ℂ) tetra) :=
  algebraicIndependent_iff_injective_aeval.mp tetra_algebraicIndependent

/-- Substitution by hexablock coordinates preserves and reflects polynomial equality. -/
theorem hex_substitution_injective : Function.Injective (aeval (R := ℂ) hex) :=
  algebraicIndependent_iff_injective_aeval.mp hex_algebraicIndependent

end GaloisForLFunctions.HTGeometry.HexablockPolynomial
#print axioms GaloisForLFunctions.HTGeometry.HexablockPolynomial.hex_substitution_injective
#print axioms GaloisForLFunctions.HTGeometry.HexablockPolynomial.tetra_substitution_injective
