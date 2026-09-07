import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral transport across the Maass homogeneous-space correspondence

Any complex-linear operator on invariant upper-half-plane functions transports by conjugation to
the spherical automorphic model.  This file proves exact preservation of eigen-equations,
eigenvectors, and eigenvalues.  An eventual coordinate Laplacian/Casimir theorem can instantiate
this general result.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Conjugate an operator on invariant upper-half-plane functions into the spherical automorphic
model. -/
def transportedSphericalOperator (Γ : Subgroup SL2R)
    (T : Module.End ℂ (upperHalfPlaneInvariantFunctions Γ)) :
    Module.End ℂ (sphericalAutomorphicVectors Γ) :=
  (maassToSphericalAutomorphicCorrespondence Γ).conj T

@[simp]
theorem transportedSphericalOperator_apply (Γ : Subgroup SL2R)
    (T : Module.End ℂ (upperHalfPlaneInvariantFunctions Γ))
    (f : upperHalfPlaneInvariantFunctions Γ) :
    transportedSphericalOperator Γ T (maassToSphericalAutomorphicCorrespondence Γ f) =
      maassToSphericalAutomorphicCorrespondence Γ (T f) := by
  simp [transportedSphericalOperator, LinearEquiv.conj_apply]

/-- Operator eigen-equations are identical after the homogeneous-space correspondence. -/
theorem transportedSphericalOperator_eigenEquation_iff (Γ : Subgroup SL2R)
    (T : Module.End ℂ (upperHalfPlaneInvariantFunctions Γ)) (μ : ℂ)
    (f : upperHalfPlaneInvariantFunctions Γ) :
    transportedSphericalOperator Γ T (maassToSphericalAutomorphicCorrespondence Γ f) =
        μ • maassToSphericalAutomorphicCorrespondence Γ f ↔
      T f = μ • f := by
  rw [transportedSphericalOperator_apply]
  change
    maassToSphericalAutomorphicCorrespondence Γ (T f) =
        maassToSphericalAutomorphicCorrespondence Γ (μ • f) ↔
      T f = μ • f
  exact (maassToSphericalAutomorphicCorrespondence Γ).injective.eq_iff

/-- Nonzero eigenvectors are preserved exactly by spectral transport. -/
theorem transportedSphericalOperator_hasEigenvector_iff (Γ : Subgroup SL2R)
    (T : Module.End ℂ (upperHalfPlaneInvariantFunctions Γ)) (μ : ℂ)
    (f : upperHalfPlaneInvariantFunctions Γ) :
    (transportedSphericalOperator Γ T).HasEigenvector μ
        (maassToSphericalAutomorphicCorrespondence Γ f) ↔
      T.HasEigenvector μ f := by
  simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  rw [transportedSphericalOperator_eigenEquation_iff]
  exact and_congr_right fun _ ↦ (maassToSphericalAutomorphicCorrespondence Γ).map_ne_zero_iff

/-- An operator has `μ` as an eigenvalue when it has a nonzero `μ`-eigenvector. -/
def OperatorHasEigenvalue {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (T : Module.End ℂ V) (μ : ℂ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ T v = μ • v

/-- Spectral transport preserves the predicate that `μ` is an eigenvalue. -/
theorem transportedSphericalOperator_hasEigenvalue_iff (Γ : Subgroup SL2R)
    (T : Module.End ℂ (upperHalfPlaneInvariantFunctions Γ)) (μ : ℂ) :
    OperatorHasEigenvalue (transportedSphericalOperator Γ T) μ ↔
      OperatorHasEigenvalue T μ := by
  constructor
  · rintro ⟨F, hFzero, hFeig⟩
    let f := (maassToSphericalAutomorphicCorrespondence Γ).symm F
    have hmap : maassToSphericalAutomorphicCorrespondence Γ f = F := by
      simp [f]
    refine ⟨f, ?_, ?_⟩
    · intro hfzero
      apply hFzero
      rw [← hmap, hfzero]
      simp
    · have htransport : transportedSphericalOperator Γ T
          (maassToSphericalAutomorphicCorrespondence Γ f) =
            μ • maassToSphericalAutomorphicCorrespondence Γ f := by
        simpa only [hmap] using hFeig
      exact (transportedSphericalOperator_eigenEquation_iff Γ T μ f).mp htransport
  · rintro ⟨f, hfzero, hfeig⟩
    refine ⟨maassToSphericalAutomorphicCorrespondence Γ f, ?_, ?_⟩
    · exact (maassToSphericalAutomorphicCorrespondence Γ).map_ne_zero_iff.mpr hfzero
    · exact (transportedSphericalOperator_eigenEquation_iff Γ T μ f).mpr hfeig

end

end GaloisForLFunctions.RHTower
