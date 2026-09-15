import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspTransport

/-!
# The principal-congruence Maass source in the rational Hecke arena

The existing Maass source is invariant under the real image in `SL(2, ℝ)` of an
integral subgroup. Rational Hecke correspondences instead live in `GL(2, ℝ)`.
This file gives the exact same source data with invariance indexed by the
integral subgroup's `GL(2, ℝ)` image; its function, eigen-equation, cusp decay,
and nonvanishing are unchanged.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff

noncomputable section

/-- Nonzero smooth cuspidal Maass eigenfunctions invariant under a `GL(2, ℝ)` subgroup. -/
def GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) (eigenvalue : ℝ) :=
  {f : upperHalfPlaneInvariantFunctions Γ //
    f ≠ 0 ∧ IsMaassEigenfunction eigenvalue f.1 ∧ IsCuspidalAtIntegralCusps f.1}

/-- Reindex integral-subgroup invariance from the real special-linear image to the
identical `GL(2, ℝ)` Möbius action. -/
def integralMaassToGLInvariant (Γ : Subgroup SL2Z)
    (f : upperHalfPlaneInvariantFunctions (realImage Γ)) :
    upperHalfPlaneInvariantFunctions (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  ⟨f.1, by
    intro γ z
    obtain ⟨A, hA, hγ⟩ := γ.2
    have hf := f.2 ⟨integralSL2ToReal A, ⟨A, hA, rfl⟩⟩ z
    rw [← hγ]
    exact hf⟩

/-- The actual principal-congruence Maass source, unchanged, in the rational
`GL(2, ℝ)` correspondence arena. -/
def integralMaassCuspEigenformToGL (Γ : Subgroup SL2Z) (eigenvalue : ℝ)
    (f : MaassCuspEigenform (realImage Γ) eigenvalue) :
    GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) eigenvalue :=
  ⟨integralMaassToGLInvariant Γ f.1, f.2⟩

end

end GaloisForLFunctions.RHTower
