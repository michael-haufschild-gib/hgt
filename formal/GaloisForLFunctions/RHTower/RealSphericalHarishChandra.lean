import GaloisForLFunctions.RHTower.RankOneComplementarySeriesBound
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Spherical principal-series Harish-Chandra module for `SL(2, ℝ)`

This file constructs the algebraic `K`-finite model on finitely supported sequences indexed by
even weights.  It defines the standard `sl₂` raising, lowering, and weight operators, proves their
commutator relations, and computes the Casimir scalar.  It also isolates the first raising-norm
coefficient whose positivity gives the complementary-series bound.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Algebraic spherical `K`-finite model, with index `m` representing weight `2m`. -/
abbrev SphericalKFiniteModel := ℤ →₀ ℂ

/-- A one-dimensional weighted basis insertion. -/
def weightedSingle (m : ℤ) (a : ℂ) : ℂ →ₗ[ℂ] SphericalKFiniteModel where
  toFun z := Finsupp.single m (a * z)
  map_add' x y := by
    ext j
    by_cases h : m = j <;> simp [h, mul_add]
  map_smul' c z := by
    ext j
    by_cases h : m = j
    · simp [h]
      ring
    · simp [h]

/-- Linear extension of a weighted shift on the `K`-type basis. -/
def weightedShift (δ : ℤ) (a : ℤ → ℂ) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  Finsupp.lsum ℂ (fun m ↦ weightedSingle (m + δ) (a m))

@[simp]
theorem weightedShift_single (δ : ℤ) (a : ℤ → ℂ) (m : ℤ) (z : ℂ) :
    weightedShift δ a (Finsupp.single m z) =
      Finsupp.single (m + δ) (a m * z) := by
  simp [weightedShift, weightedSingle]

/-- Weight operator `h w_{2m} = 2m w_{2m}`. -/
def sphericalPrincipalH : SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  weightedShift 0 (fun m ↦ 2 * (m : ℂ))

/-- Raising operator `e w_{2m} = (s - 1 - 2m)/2 w_{2m+2}`. -/
def sphericalPrincipalE (s : ℂ) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  weightedShift 1 (fun m ↦ (s - 1 - 2 * (m : ℂ)) / 2)

/-- Lowering operator `f w_{2m} = (s - 1 + 2m)/2 w_{2m-2}`. -/
def sphericalPrincipalF (s : ℂ) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  weightedShift (-1) (fun m ↦ (s - 1 + 2 * (m : ℂ)) / 2)

@[simp]
theorem sphericalPrincipalH_single (m : ℤ) (z : ℂ) :
    sphericalPrincipalH (Finsupp.single m z) =
      Finsupp.single m ((2 * (m : ℂ)) * z) := by
  simp [sphericalPrincipalH]

@[simp]
theorem sphericalPrincipalE_single (s : ℂ) (m : ℤ) (z : ℂ) :
    sphericalPrincipalE s (Finsupp.single m z) =
      Finsupp.single (m + 1) (((s - 1 - 2 * (m : ℂ)) / 2) * z) := by
  simp [sphericalPrincipalE]

@[simp]
theorem sphericalPrincipalF_single (s : ℂ) (m : ℤ) (z : ℂ) :
    sphericalPrincipalF s (Finsupp.single m z) =
      Finsupp.single (m - 1) (((s - 1 + 2 * (m : ℂ)) / 2) * z) := by
  simp [sphericalPrincipalF, sub_eq_add_neg]

/-- The weight and raising operators satisfy `[h,e]=2e`. -/
theorem sphericalPrincipalH_comm_E (s : ℂ) :
    sphericalPrincipalH.comp (sphericalPrincipalE s) -
        (sphericalPrincipalE s).comp sphericalPrincipalH =
      2 • sphericalPrincipalE s := by
  apply Finsupp.lhom_ext
  intro m z
  ext j
  by_cases h : m + 1 = j
  · subst j
    simp
    ring
  · simp [h]

/-- The weight and lowering operators satisfy `[h,f]=-2f`. -/
theorem sphericalPrincipalH_comm_F (s : ℂ) :
    sphericalPrincipalH.comp (sphericalPrincipalF s) -
        (sphericalPrincipalF s).comp sphericalPrincipalH =
      (-2) • sphericalPrincipalF s := by
  apply Finsupp.lhom_ext
  intro m z
  ext j
  by_cases h : m - 1 = j
  · subst j
    simp
    ring
  · simp [h]

/-- The raising and lowering operators satisfy `[e,f]=h`. -/
theorem sphericalPrincipalE_comm_F (s : ℂ) :
    (sphericalPrincipalE s).comp (sphericalPrincipalF s) -
        (sphericalPrincipalF s).comp (sphericalPrincipalE s) =
      sphericalPrincipalH := by
  apply Finsupp.lhom_ext
  intro m z
  ext j
  by_cases h : m = j
  · subst j
    simp
    ring
  · simp [h]

/-- Casimir operator `fe + (h+1)²/4` on the spherical principal-series model. -/
def sphericalPrincipalCasimir (s : ℂ) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  (sphericalPrincipalF s).comp (sphericalPrincipalE s) +
    (1 / 4 : ℂ) •
      ((sphericalPrincipalH + LinearMap.id).comp
        (sphericalPrincipalH + LinearMap.id))

/-- The Casimir acts by the scalar `s²/4`. -/
theorem sphericalPrincipalCasimir_eq_smul_id (s : ℂ) :
    sphericalPrincipalCasimir s = (s ^ 2 / 4) • LinearMap.id := by
  apply Finsupp.lhom_ext
  intro m z
  ext j
  by_cases h : m = j <;> simp [sphericalPrincipalCasimir, h]
  ring

/-- Positive-Laplacian normalization obtained from the shifted Casimir. -/
def sphericalPrincipalLaplacian (s : ℂ) :
    SphericalKFiniteModel →ₗ[ℂ] SphericalKFiniteModel :=
  (1 / 4 : ℂ) • LinearMap.id - sphericalPrincipalCasimir s

/-- The shifted Casimir acts by the scalar `(1-s²)/4`. -/
theorem sphericalPrincipalLaplacian_eq_smul_id (s : ℂ) :
    sphericalPrincipalLaplacian s = ((1 - s ^ 2) / 4) • LinearMap.id := by
  rw [sphericalPrincipalLaplacian, sphericalPrincipalCasimir_eq_smul_id]
  ext v m
  by_cases h : v = m
  · subst m
    simp
    ring
  · simp [h]

/-- Raising-norm coefficient at even weight `2m` for real parameter `s`. -/
def sphericalRaisingNormCoefficient (s : ℝ) (m : ℤ) : ℝ :=
  (((2 * m + 1 : ℤ) : ℝ) ^ 2 - s ^ 2) / 4

/-- At spherical weight zero and `s=2ν`, the raising-norm coefficient is the Selberg eigenvalue. -/
theorem sphericalRaisingNormCoefficient_zero_two_mul (ν : ℝ) :
    sphericalRaisingNormCoefficient (2 * ν) 0 =
      eigenvalueOfComplementaryExponent ν := by
  simp [sphericalRaisingNormCoefficient, eigenvalueOfComplementaryExponent]
  ring

/-- At `s=2ν`, the shifted Casimir scalar is the Selberg-normalized eigenvalue. -/
theorem sphericalPrincipalLaplacian_two_mul_eq_eigenvalue (ν : ℝ) :
    sphericalPrincipalLaplacian ((2 * ν : ℝ) : ℂ) =
      (eigenvalueOfComplementaryExponent ν : ℂ) • LinearMap.id := by
  rw [sphericalPrincipalLaplacian_eq_smul_id]
  ext v m
  by_cases h : v = m
  · subst m
    simp [eigenvalueOfComplementaryExponent]
    ring
  · simp [h]

/-- Positivity of the first raising norm gives the exact complementary-series exponent bound. -/
theorem sphericalRaisingNormCoefficient_zero_pos_iff (ν : ℝ) :
    0 < sphericalRaisingNormCoefficient (2 * ν) 0 ↔ |ν| < 1 / 2 := by
  rw [sphericalRaisingNormCoefficient_zero_two_mul]
  exact sphericalRaisingNormFactor_pos_iff ν

end

end GaloisForLFunctions.RHTower
