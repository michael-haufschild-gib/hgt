import GaloisForLFunctions.RHTower.Deninger.DeningerResidueSequence
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Quotient form of the logarithmic residue sequence

The residue sequence of one coordinate stage identifies the quotient of global logarithmic forms
by forms extended from the divisor with the residue forms on that divisor.  Thus every local
residue is globally realized, and two realizations differ exactly by an extension from the divisor.
-/

namespace RHTower

open Complex

noncomputable section

/-- **Residue local-global equivalence.** Global logarithmic forms modulo the residue-free
extensions from the divisor are linearly equivalent to the divisor's logarithmic residue forms. -/
noncomputable def deningerResidueQuotientEquiv (r n : ℕ) :
    (((Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) ⧸
      (LinearMap.range (deningerExtendForm r (n + 1)))) ≃ₗ[ℂ]
      ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp (deningerResidue_exact_sequence (r := r) (n := n))).symm).trans
      (LinearMap.quotKerEquivOfSurjective (deningerResidueForm r n)
        (deningerResidueForm_surjective (r := r) (n := n)))

/-- The residue local-global equivalence is induced by the residue map itself. -/
theorem deningerResidueQuotientEquiv_mk (r n : ℕ)
    (α : (Fin (r + 1) → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerResidueQuotientEquiv r n (Submodule.Quotient.mk α) =
      deningerResidueForm r n α := by
  simp [deningerResidueQuotientEquiv]

end
