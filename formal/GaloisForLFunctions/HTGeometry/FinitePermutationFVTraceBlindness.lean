import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite permutation Frobenius--Verschiebung trace blindness

At a finite integral formation stage, Frobenius acts by a permutation matrix.  If
Verschiebung is degree times inverse Frobenius, the squared parity supertrace is only a
fixed-point count multiplied by the degree defect.  It contains no analytic rapidity.
-/

namespace GaloisForLFunctions

open Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Squared Frobenius--Verschiebung supertrace at a finite permutation stage. -/
def finitePermutationFVSquaredSupertrace
    (q : ℤ) (σ : Equiv.Perm ι) : ℤ :=
  Matrix.trace ((σ ^ 2).permMatrix ℤ) -
    Matrix.trace (q ^ 2 • (((σ⁻¹) ^ 2).permMatrix ℤ))

/-- A finite permutation and its inverse have the same squared trace. -/
theorem finitePermutation_inverseSquare_trace_eq
    (σ : Equiv.Perm ι) :
    Matrix.trace (((σ⁻¹) ^ 2).permMatrix ℤ) =
      Matrix.trace ((σ ^ 2).permMatrix ℤ) := by
  rw [inv_pow, ← Matrix.transpose_permMatrix]
  exact Matrix.trace_transpose _

/--
The finite squared Frobenius--Verschiebung supertrace is exactly degree defect times the
number of points fixed by the squared Frobenius permutation.
-/
theorem finitePermutationFVSquaredSupertrace_eq
    (q : ℤ) (σ : Equiv.Perm ι) :
    finitePermutationFVSquaredSupertrace q σ =
      (1 - q ^ 2) * ((Function.fixedPoints ⇑(σ ^ 2)).ncard : ℤ) := by
  rw [finitePermutationFVSquaredSupertrace, Matrix.trace_smul,
    finitePermutation_inverseSquare_trace_eq]
  rw [Matrix.trace_permutation]
  ring

end GaloisForLFunctions
