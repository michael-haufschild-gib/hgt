import GaloisForLFunctions.RHTower.RealSphericalHarishChandra
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Unitarity obstruction for the real spherical principal series

This file defines positive-definite Hermitian forms on the spherical `K`-finite model and the
infinitesimal invariance relation `e† = -f`.  It proves the raising-norm identity and then proves,
without assuming an exponent bound, that every real parameter admitting such a form lies in
`(-1, 1)`.  Under `s = 2ν`, this is the strict bound `|ν| < 1/2`.

Existence of the complementary-series form inside this interval and classification of arbitrary
generic unitary representations are separate results.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complex sesquilinear form, conjugate-linear in the first argument. -/
abbrev ComplexHermitianForm (V : Type*) [AddCommMonoid V] [Module ℂ V] :=
  V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ

/-- Hermitian form whose diagonal real part is strictly positive away from zero. -/
def IsPositiveDefiniteHermitian {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (B : ComplexHermitianForm V) : Prop :=
  B.IsSymm ∧ ∀ v : V, v ≠ 0 → 0 < (B v v).re

/-- Infinitesimal invariance relation `e† = -f` on the spherical principal-series model. -/
def IsSphericalPrincipalInvariant (s : ℝ)
    (B : ComplexHermitianForm SphericalKFiniteModel) : Prop :=
  ∀ v w,
    B (sphericalPrincipalE (s : ℂ) v) w =
      -B v (sphericalPrincipalF (s : ℂ) w)

/-- Real parameters for which the full spherical algebraic model admits a positive-definite
invariant Hermitian form. -/
def UnitarizableSphericalPrincipalParameter : Set ℝ :=
  {s | ∃ B : ComplexHermitianForm SphericalKFiniteModel,
    IsPositiveDefiniteHermitian B ∧ IsSphericalPrincipalInvariant s B}

/-- The invariant-form relation computes the first raising norm. -/
theorem sphericalPrincipal_raising_norm_identity (s : ℝ)
    (B : ComplexHermitianForm SphericalKFiniteModel)
    (hB : IsSphericalPrincipalInvariant s B) :
    B (sphericalPrincipalE (s : ℂ) (Finsupp.single 0 1))
        (sphericalPrincipalE (s : ℂ) (Finsupp.single 0 1)) =
      (((1 - s ^ (2 : ℕ)) / 4 : ℝ) : ℂ) *
        B (Finsupp.single 0 1) (Finsupp.single 0 1) := by
  rw [hB]
  have hFE :
      sphericalPrincipalF (s : ℂ)
          (sphericalPrincipalE (s : ℂ) (Finsupp.single 0 1)) =
        (((s ^ (2 : ℕ) - 1) / 4 : ℝ) : ℂ) • Finsupp.single 0 1 := by
    ext j
    by_cases hj : (0 : ℤ) = j
    · subst j
      simp
      ring
    · simp [hj]
  rw [hFE]
  simp only [map_smul]
  push_cast
  ring

/-- **Spherical complementary-series bound.** A positive-definite invariant Hermitian form on the
full spherical principal-series module forces the real parameter into `(-1, 1)`. -/
theorem unitarizableSphericalPrincipalParameter_subset :
    UnitarizableSphericalPrincipalParameter ⊆ Set.Ioo (-1) 1 := by
  intro s hs
  obtain ⟨B, hpos, hinv⟩ := hs
  let v0 : SphericalKFiniteModel := Finsupp.single 0 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have h0 := congr_arg (fun v : SphericalKFiniteModel ↦ v 0) h
    simp [v0] at h0
  have hq : 0 < (B v0 v0).re := hpos.2 v0 hv0
  have hsone : s ≠ 1 := by
    intro hs1
    have hrel := hinv (Finsupp.single (-1) 1) v0
    subst s
    simp [v0] at hrel
    have hre := congr_arg Complex.re hrel
    simp at hre
    linarith
  have hEv0 : sphericalPrincipalE (s : ℂ) v0 ≠ 0 := by
    intro hzero
    have h1 := congr_arg (fun v : SphericalKFiniteModel ↦ v 1) hzero
    simp [v0] at h1
    have hre := congr_arg Complex.re h1
    simp at hre
    apply hsone
    linarith
  have hnorm :
      0 < (B (sphericalPrincipalE (s : ℂ) v0)
        (sphericalPrincipalE (s : ℂ) v0)).re :=
    hpos.2 _ hEv0
  have hid := sphericalPrincipal_raising_norm_identity s B hinv
  change
    B (sphericalPrincipalE (s : ℂ) v0) (sphericalPrincipalE (s : ℂ) v0) =
      (((1 - s ^ (2 : ℕ)) / 4 : ℝ) : ℂ) * B v0 v0 at hid
  rw [hid] at hnorm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hnorm
  have hcoeff : 0 < (1 - s ^ (2 : ℕ)) / 4 := pos_of_mul_pos_left hnorm hq.le
  constructor <;> nlinarith

/-- In complementary-exponent normalization `s=2ν`, unitarizability forces
`ν ∈ (-1/2,1/2)`. -/
theorem unitarizableSphericalExponentParameter_subset :
    {ν : ℝ | 2 * ν ∈ UnitarizableSphericalPrincipalParameter} ⊆
      Set.Ioo (-1 / 2) (1 / 2) := by
  intro ν hν
  have hs := unitarizableSphericalPrincipalParameter_subset hν
  rcases hs with ⟨hsleft, hsright⟩
  constructor <;> linarith

end

end GaloisForLFunctions.RHTower
