import GaloisForLFunctions.RHTower.CongruenceMaassCorrespondence
import GaloisForLFunctions.RHTower.MaassSpectralTransport
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Analytic Maass cusp forms and spherical automorphic vectors

This file enriches the algebraic homogeneous-space correspondence with concrete real `C²`
regularity, the positive hyperbolic Laplacian `-y²(∂ₓ²+∂ᵧ²)`, nonvanishing, and decay at every
integral cusp.  It gives an exact equivalence between these Maass cusp eigenfunctions and their
spherical right-regular realizations, including the standard principal, `Γ₀`, and `Γ₁`
congruence subgroups.

The cusp condition used here is pointwise decay after every integral scaling matrix.  This is the
standard consequence of Fourier cuspidality for Maass eigenfunctions; proving its equivalence to
zero constant terms and quotient `L²` membership requires the missing Fourier/quotient-measure
layer.  No Laplacian-to-derived-Casimir identification is asserted.
-/

namespace GaloisForLFunctions.RHTower

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-- Smoothness on the real two-manifold underlying the upper half-plane. -/
def IsRealSmoothUpperHalfPlane (f : ℍ → ℂ) : Prop :=
  ContDiffOn ℝ 2 (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}

/-- Positive hyperbolic Laplacian `-y²(∂ₓ²+∂ᵧ²)` in the complex coordinate chart. -/
def positiveHyperbolicLaplacian (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  -(z.im : ℂ) ^ 2 *
    (fderiv ℝ (fun w : ℂ ↦
        fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) w 1) (z : ℂ) 1 +
      fderiv ℝ (fun w : ℂ ↦
        fderiv ℝ (f ∘ UpperHalfPlane.ofComplex) w Complex.I) (z : ℂ) Complex.I)

/-- A real-smooth eigenfunction of the positive hyperbolic Laplacian. -/
def IsMaassEigenfunction (eigenvalue : ℝ) (f : ℍ → ℂ) : Prop :=
  IsRealSmoothUpperHalfPlane f ∧
    ∀ z : ℍ, positiveHyperbolicLaplacian f z = (eigenvalue : ℂ) * f z

/-- Decay at every integral cusp, expressed by all integral scaling matrices. -/
def IsCuspidalAtIntegralCusps (f : ℍ → ℂ) : Prop :=
  ∀ σ : SL2Z, UpperHalfPlane.IsZeroAtImInfty
    (fun z : ℍ ↦ f (integralSL2ToReal σ • z))

/-- Nonzero smooth cuspidal Laplace eigenfunctions for a real subgroup. -/
def MaassCuspEigenform (Γ : Subgroup SL2R) (eigenvalue : ℝ) :=
  {f : upperHalfPlaneInvariantFunctions Γ //
    f ≠ 0 ∧ IsMaassEigenfunction eigenvalue f.1 ∧ IsCuspidalAtIntegralCusps f.1}

/-- Spherical automorphic vectors whose descended upper-half-plane function is a Maass cusp
 eigenfunction. -/
def SphericalCuspidalAutomorphicEigenvector (Γ : Subgroup SL2R) (eigenvalue : ℝ) :=
  {F : sphericalAutomorphicVectors Γ //
    let f := (maassToSphericalAutomorphicCorrespondence Γ).symm F
    f ≠ 0 ∧ IsMaassEigenfunction eigenvalue f.1 ∧ IsCuspidalAtIntegralCusps f.1}

/-- Full Maass-to-spherical-automorphic correspondence with smoothness, positive-Laplacian
 eigen-equation, nonvanishing, and cusp decay retained exactly. -/
def maassCuspToSphericalAutomorphicCorrespondence (Γ : Subgroup SL2R) (eigenvalue : ℝ) :
    MaassCuspEigenform Γ eigenvalue ≃ SphericalCuspidalAutomorphicEigenvector Γ eigenvalue where
  toFun f := ⟨maassToSphericalAutomorphicCorrespondence Γ f.1, by
    simpa using f.2⟩
  invFun F := ⟨(maassToSphericalAutomorphicCorrespondence Γ).symm F.1, F.2⟩
  left_inv f := by
    apply Subtype.ext
    simp
  right_inv F := by
    apply Subtype.ext
    simp

@[simp]
theorem maassCuspToSphericalAutomorphicCorrespondence_apply
    (Γ : Subgroup SL2R) (eigenvalue : ℝ) (f : MaassCuspEigenform Γ eigenvalue) (g : SL2R) :
    (maassCuspToSphericalAutomorphicCorrespondence Γ eigenvalue f).1.1.1 g =
      f.1.1 (g • UpperHalfPlane.I) := rfl

@[simp]
theorem maassCuspToSphericalAutomorphicCorrespondence_symm_apply
    (Γ : Subgroup SL2R) (eigenvalue : ℝ)
    (F : SphericalCuspidalAutomorphicEigenvector Γ eigenvalue) (z : ℍ) :
    ((maassCuspToSphericalAutomorphicCorrespondence Γ eigenvalue).symm F).1.1 z =
      F.1.1.1 (UpperHalfPlane.toSL2R z) := rfl

/-- Analytic Maass/automorphic correspondence for the principal congruence subgroup `Γ(N)`. -/
def principalCongruenceMaassCuspCorrespondence (N : ℕ) (eigenvalue : ℝ) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) eigenvalue ≃
      SphericalCuspidalAutomorphicEigenvector
        (realImage (CongruenceSubgroup.Gamma N)) eigenvalue :=
  maassCuspToSphericalAutomorphicCorrespondence _ _

/-- Analytic Maass/automorphic correspondence for `Γ₀(N)`. -/
def gammaZeroMaassCuspCorrespondence (N : ℕ) (eigenvalue : ℝ) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 N)) eigenvalue ≃
      SphericalCuspidalAutomorphicEigenvector
        (realImage (CongruenceSubgroup.Gamma0 N)) eigenvalue :=
  maassCuspToSphericalAutomorphicCorrespondence _ _

/-- Analytic Maass/automorphic correspondence for `Γ₁(N)`. -/
def gammaOneMaassCuspCorrespondence (N : ℕ) (eigenvalue : ℝ) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma1 N)) eigenvalue ≃
      SphericalCuspidalAutomorphicEigenvector
        (realImage (CongruenceSubgroup.Gamma1 N)) eigenvalue :=
  maassCuspToSphericalAutomorphicCorrespondence _ _

end
end GaloisForLFunctions.RHTower
