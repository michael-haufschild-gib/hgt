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

/-- The complex submodule of functions invariant under the Möbius action of a
`GL(2, ℝ)` subgroup. -/
def glUpperHalfPlaneInvariantFunctions (Γ : Subgroup (GL (Fin 2) ℝ)) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {f | ∀ γ : Γ, ∀ z : ℍ, f (γ.1 • z) = f z}
  zero_mem' := by
    intro γ z
    rfl
  add_mem' := by
    intro f g hf hg γ z
    simp only [Pi.add_apply, hf γ z, hg γ z]
  smul_mem' := by
    intro c f hf γ z
    simp only [Pi.smul_apply, hf γ z]

/-- Nonzero smooth cuspidal Maass eigenfunctions invariant under a `GL(2, ℝ)` subgroup. -/
def GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) (eigenvalue : ℝ) :=
  {f : glUpperHalfPlaneInvariantFunctions Γ //
    f.1 ≠ 0 ∧ IsMaassEigenfunction eigenvalue f.1 ∧ IsCuspidalAtIntegralCusps f.1}

/-- Reindex integral-subgroup invariance from the real special-linear image to the
identical `GL(2, ℝ)` Möbius action. -/
def integralMaassToGLInvariant (Γ : Subgroup SL2Z)
    (f : upperHalfPlaneInvariantFunctions (realImage Γ)) :
    glUpperHalfPlaneInvariantFunctions (Γ : Subgroup (GL (Fin 2) ℝ)) :=
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
  ⟨integralMaassToGLInvariant Γ f.1, by
    constructor
    · intro hzero
      apply f.2.1
      ext z
      exact congrFun hzero z
    exact f.2.2⟩

/-- Reindex a Maass cusp eigenform invariant under an integral subgroup viewed in `GL(2, ℝ)`
back to the identical real `SL(2, ℝ)` action. -/
def glIntegralMaassCuspEigenformToMaass (Γ : Subgroup SL2Z) (eigenvalue : ℝ)
    (f : GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) eigenvalue) :
    MaassCuspEigenform (realImage Γ) eigenvalue :=
  ⟨⟨f.1.1, by
    intro γ z
    obtain ⟨A, hA, hγ⟩ := γ.2
    rw [← hγ]
    exact f.1.2 ⟨integralSL2ToReal A, ⟨A, hA, rfl⟩⟩ z
  ⟩, by
    refine ⟨?_, f.2.2.1, f.2.2.2⟩
    intro hzero
    apply f.2.1
    exact congrArg Subtype.val hzero⟩

/-- Reindexing the same integral congruence action between its `SL(2, ℝ)` and
`GL(2, ℝ)` carriers is an exact equivalence of Maass cusp eigenspaces. -/
def integralMaassCuspEigenformGLCorrespondence (Γ : Subgroup SL2Z) (eigenvalue : ℝ) :
    MaassCuspEigenform (realImage Γ) eigenvalue ≃
      GLMaassCuspEigenform (Γ : Subgroup (GL (Fin 2) ℝ)) eigenvalue where
  toFun := integralMaassCuspEigenformToGL Γ eigenvalue
  invFun := glIntegralMaassCuspEigenformToMaass Γ eigenvalue
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

end

end GaloisForLFunctions.RHTower
