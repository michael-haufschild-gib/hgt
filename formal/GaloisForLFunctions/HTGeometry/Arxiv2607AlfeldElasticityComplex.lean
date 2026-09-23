import Mathlib
import GaloisForLFunctions.HTGeometry.Arxiv2607PiecewiseSymmetric
import GaloisForLFunctions.HTGeometry.MayerVietorisQuotient
import GaloisForLFunctions.HTGeometry.ConstitutivePolyscopicMatching

/-!
# Exactness and dimension laws for tetrahedral Alfeld elasticity complexes

This file formalizes reusable consequences of arXiv:2607.01933,
*Low-regularity finite element elasticity complexes with hybridizable stresses on tetrahedral
Alfeld splits*.

It records the exact-triple interface used by the paper, proves cycle/potential consequences,
instantiates them with the corpus Mayer--Vietoris exact sequence, verifies all displayed local and
bubble dimension identities symbolically, and exposes the symmetric/skew matrix split from
`Arxiv2607PiecewiseSymmetric` as the algebraic `def = sym grad` core.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section ExactTriples

universe u

variable (𝕜 A B C : Type u) [Semiring 𝕜]
  [AddCommMonoid A] [Module 𝕜 A]
  [AddCommMonoid B] [Module 𝕜 B]
  [AddCommMonoid C] [Module 𝕜 C]

/-- A certified exact pair of consecutive linear maps. -/
structure ExactLinearTriple where
  first : A →ₗ[𝕜] B
  second : B →ₗ[𝕜] C
  exact : LinearMap.range first = LinearMap.ker second

variable {𝕜 A B C}

/-- Every boundary in an exact linear triple is a cycle. -/
theorem ExactLinearTriple.boundary_is_cycle (E : ExactLinearTriple 𝕜 A B C) (a : A) :
    E.second (E.first a) = 0 := by
  rw [← LinearMap.mem_ker, ← E.exact]
  exact ⟨a, rfl⟩

/-- Every cycle in an exact linear triple admits a potential. -/
theorem ExactLinearTriple.cycle_has_potential (E : ExactLinearTriple 𝕜 A B C)
    {b : B} (hb : E.second b = 0) : ∃ a, E.first a = b := by
  rw [← LinearMap.mem_ker, ← E.exact] at hb
  exact hb

/-- Commuting interpolation maps cycles in a source complex to cycles in a target complex. -/
theorem commutingInterpolation_sends_cycle
    {A' B' C' : Type u}
    [AddCommMonoid A'] [Module 𝕜 A']
    [AddCommMonoid B'] [Module 𝕜 B']
    [AddCommMonoid C'] [Module 𝕜 C']
    (d₀ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] C)
    (D₀ : A' →ₗ[𝕜] B') (D₁ : B' →ₗ[𝕜] C')
    (I₀ : A →ₗ[𝕜] A') (I₁ : B →ₗ[𝕜] B') (I₂ : C →ₗ[𝕜] C')
    (commutes₀ : I₁.comp d₀ = D₀.comp I₀)
    (commutes₁ : I₂.comp d₁ = D₁.comp I₁)
    {a : A} (ha : d₁ (d₀ a) = 0) : D₁ (D₀ (I₀ a)) = 0 := by
  have h₀ := LinearMap.congr_fun commutes₀ a
  have h₁ := LinearMap.congr_fun commutes₁ (d₀ a)
  simp only [LinearMap.comp_apply] at h₀ h₁
  rw [← h₀, ← h₁, ha, map_zero]

end ExactTriples

section MayerVietorisApplication

universe u
variable {R : Type u} [CommRing R]

/-- The corpus Mayer--Vietoris maps form a certified exact linear triple. -/
def mayerVietorisExactLinearTriple (I J : Ideal R) :
    ExactLinearTriple R (R ⧸ (I ⊓ J)) ((R ⧸ I) × (R ⧸ J)) (R ⧸ (I ⊔ J)) where
  first := mvPair I J
  second := mvDiff I J
  exact := mv_exact I J

/-- A compatible pair of quotient classes has a common lift. -/
theorem mvDiff_zero_iff_exists_commonLift (I J : Ideal R) (z : (R ⧸ I) × (R ⧸ J)) :
    mvDiff I J z = 0 ↔ ∃ x, mvPair I J x = z := by
  constructor
  · exact (mayerVietorisExactLinearTriple I J).cycle_has_potential
  · rintro ⟨x, rfl⟩
    exact (mayerVietorisExactLinearTriple I J).boundary_is_cycle x

end MayerVietorisApplication

section MatchingComplexApplication

universe u
variable {k V W : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Kernel inclusion followed by any corpus matching map is an exact linear triple. -/
def matchingKernelExactLinearTriple (μ : V →ₗ[k] W) :
    ExactLinearTriple k (LinearMap.ker μ) V W where
  first := (LinearMap.ker μ).subtype
  second := μ
  exact := (matching_kernel_cokernel μ).1

/-- Any corpus matching map followed by its range quotient is an exact linear triple. -/
def matchingCokernelExactLinearTriple (μ : V →ₗ[k] W) :
    ExactLinearTriple k V W (W ⧸ LinearMap.range μ) where
  first := μ
  second := Submodule.mkQ (LinearMap.range μ)
  exact := (matching_kernel_cokernel μ).2.1

/-- Vanishing of a matching cokernel class is equivalent to existence of a global preimage. -/
theorem matchingClass_zero_iff_exists_preimage (μ : V →ₗ[k] W) (w : W) :
    Submodule.mkQ (LinearMap.range μ) w = 0 ↔ ∃ v, μ v = w := by
  constructor
  · exact (matchingCokernelExactLinearTriple μ).cycle_has_potential
  · rintro ⟨v, rfl⟩
    exact (matchingCokernelExactLinearTriple μ).boundary_is_cycle v

end MatchingComplexApplication

section MatrixElasticity

variable {𝕜 ι : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The paper's algebraic `B = sym B + skw B` identity in corpus notation. -/
theorem alfeld_matrix_eq_def_add_rotation (B : Matrix ι ι 𝕜) :
    B = matrixSymPart B + matrixSkewPart B := by
  symm
  exact matrix_sym_add_skew B

/-- The `def` component of a matrix-valued gradient is symmetric. -/
theorem alfeld_def_transpose (B : Matrix ι ι 𝕜) :
    (matrixSymPart B).transpose = matrixSymPart B :=
  matrixSymPart_transpose B

/-- The complementary rotation component of a matrix-valued gradient is skew-symmetric. -/
theorem alfeld_rotation_transpose (B : Matrix ι ι 𝕜) :
    (matrixSkewPart B).transpose = -matrixSkewPart B :=
  matrixSkewPart_transpose B

end MatrixElasticity

/-! ## Symbolic verification of the paper's dimension formulas -/

section Dimensions

/-- Formula (3.3) with both binomial denominators cleared. -/
theorem alfeld_hess_dimension_cleared (k : ℤ) :
    (k + 6) * (k + 5) * (k + 4) + 3 * (k + 2) * (k + 1) * k =
      4 * (k ^ (3 : ℕ) + 6 * k ^ (2 : ℕ) + 20 * k + 30) := by
  ring

/-- Formula (3.4), expanded. -/
theorem alfeld_curl_dimension_expansion (k : ℤ) :
    (k + 3) * (2 * k ^ (2 : ℕ) + 9 * k + 22) =
      2 * k ^ (3 : ℕ) + 15 * k ^ (2 : ℕ) + 49 * k + 66 := by
  ring

/-- Formula (3.5), derived by Euler characteristic of the smoother exact complex. -/
theorem alfeld_smoother_inc_dimension_identity (k : ℤ) :
    2 * (k ^ (3 : ℕ) + 6 * k ^ (2 : ℕ) + 20 * k + 30) +
        (4 * k + 3) * (k + 1) * (k + 2) =
      (4 * k ^ (3 : ℕ) + 21 * k ^ (2 : ℕ) + 53 * k + 60) +
        2 * k * (k + 1) * (k + 2) + 6 := by
  ring

/-- Formula (3.6), derived by Euler characteristic of the lower-regularity exact complex. -/
theorem alfeld_lowRegularity_inc_dimension_identity (k : ℤ) :
    (k + 3) * (2 * k ^ (2 : ℕ) + 9 * k + 22) +
        (4 * k + 3) * (k + 1) * (k + 2) =
      (4 * k ^ (3 : ℕ) + 24 * k ^ (2 : ℕ) + 62 * k + 66) +
        2 * k * (k + 1) * (k + 2) + 6 := by
  ring

/-- Formula (3.7), expanded. -/
theorem alfeld_symmetric_div_dimension_expansion (k : ℤ) :
    (4 * k + 3) * (k + 1) * (k + 2) =
      4 * k ^ (3 : ℕ) + 15 * k ^ (2 : ℕ) + 17 * k + 6 := by
  ring

/-- Formula (3.18), expanded. -/
theorem alfeld_div_bubble_dimension_expansion (k : ℤ) :
    (k + 1) * (k + 2) * (4 * k - 3) =
      4 * k ^ (3 : ℕ) + 9 * k ^ (2 : ℕ) - k - 6 := by
  ring

/-- Formula (3.21) follows from the smoother bubble Euler characteristic. -/
theorem alfeld_smoother_inc_bubble_dimension_identity (k : ℤ) :
    2 * k * (k + 1) * (k + 2) +
        3 * (k + 1) * (k + 2) * (4 * k - 3) + 18 =
      3 * (4 * k ^ (3 : ℕ) + 9 * k ^ (2 : ℕ) - k) +
        2 * k * (k + 1) * (k + 2) := by
  ring

/-- Formula (3.23), expanded. -/
theorem alfeld_curl_bubble_dimension_expansion (k : ℤ) :
    k * (k + 1) * (2 * k + 3) = 2 * k ^ (3 : ℕ) + 5 * k ^ (2 : ℕ) + 3 * k := by
  ring

/-- Formula (3.24) follows from the lower-regularity bubble Euler characteristic. -/
theorem alfeld_lowRegularity_inc_bubble_dimension_identity (k : ℤ) :
    k * (k + 1) * (2 * k + 3) +
        (k + 1) * (k + 2) * (4 * k - 3) + 6 =
      (4 * k ^ (3 : ℕ) + 8 * k ^ (2 : ℕ) - 2 * k) +
        2 * k * (k + 1) * (k + 2) := by
  ring

/-- Section 4's degree-of-freedom count equals the lower-regularity space dimension. -/
theorem alfeld_lowRegularity_dof_count (k : ℤ) :
    24 + 18 * (2 * k + 3) + 4 * (4 * k ^ (2 : ℕ) + 7 * k - 3) +
        (4 * k ^ (3 : ℕ) + 8 * k ^ (2 : ℕ) - 2 * k) =
      4 * k ^ (3 : ℕ) + 24 * k ^ (2 : ℕ) + 62 * k + 66 := by
  ring

end Dimensions

end GaloisForLFunctions.HTGeometry
