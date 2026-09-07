import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Congruence-subgroup instances of the Maass homogeneous-space correspondence

This file embeds subgroups of `SL(2, ℤ)` into `SL(2, ℝ)` and specializes the exact
upper-half-plane/right-regular correspondence to the standard principal, `Γ₀`, and `Γ₁`
congruence subgroups supplied by Mathlib.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The integral special linear group. -/
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- Entrywise inclusion `SL(2, ℤ) → SL(2, ℝ)`. -/
def integralSL2ToReal : SL2Z →* SL2R :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- Real image of an integral matrix subgroup. -/
def realImage (Γ : Subgroup SL2Z) : Subgroup SL2R :=
  Γ.map integralSL2ToReal

/-- Exact homogeneous-space correspondence for any integral matrix subgroup. -/
def integralMaassToSphericalAutomorphicCorrespondence (Γ : Subgroup SL2Z) :
    upperHalfPlaneInvariantFunctions (realImage Γ) ≃ₗ[ℂ]
      sphericalAutomorphicVectors (realImage Γ) :=
  maassToSphericalAutomorphicCorrespondence (realImage Γ)

/-- Exact correspondence for Mathlib's principal congruence subgroup `Γ(N)`. -/
def principalCongruenceMaassCorrespondence (N : ℕ) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N)) ≃ₗ[ℂ]
      sphericalAutomorphicVectors (realImage (CongruenceSubgroup.Gamma N)) :=
  integralMaassToSphericalAutomorphicCorrespondence (CongruenceSubgroup.Gamma N)

/-- Exact correspondence for Mathlib's congruence subgroup `Γ₀(N)`. -/
def gammaZeroMaassCorrespondence (N : ℕ) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 N)) ≃ₗ[ℂ]
      sphericalAutomorphicVectors (realImage (CongruenceSubgroup.Gamma0 N)) :=
  integralMaassToSphericalAutomorphicCorrespondence (CongruenceSubgroup.Gamma0 N)

/-- Exact correspondence for Mathlib's congruence subgroup `Γ₁(N)`. -/
def gammaOneMaassCorrespondence (N : ℕ) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma1 N)) ≃ₗ[ℂ]
      sphericalAutomorphicVectors (realImage (CongruenceSubgroup.Gamma1 N)) :=
  integralMaassToSphericalAutomorphicCorrespondence (CongruenceSubgroup.Gamma1 N)

@[simp]
theorem principalCongruenceMaassCorrespondence_apply (N : ℕ)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma N)))
    (g : SL2R) :
    (principalCongruenceMaassCorrespondence N f).1.1 g =
      f.1 (g • UpperHalfPlane.I) :=
  rfl

@[simp]
theorem gammaZeroMaassCorrespondence_apply (N : ℕ)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma0 N)))
    (g : SL2R) :
    (gammaZeroMaassCorrespondence N f).1.1 g =
      f.1 (g • UpperHalfPlane.I) :=
  rfl

@[simp]
theorem gammaOneMaassCorrespondence_apply (N : ℕ)
    (f : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma1 N)))
    (g : SL2R) :
    (gammaOneMaassCorrespondence N f).1.1 g =
      f.1 (g • UpperHalfPlane.I) :=
  rfl

end

end GaloisForLFunctions.RHTower
