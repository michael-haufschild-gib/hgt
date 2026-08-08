import GaloisForLFunctions.HTGeometry.FreeDifferentialFamilyScale
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Witt-index-one reality for a common eigenvalue

This file isolates the finite algebraic mechanism needed by the reflection-folded Route-R source.
For a complex sesquilinear form, linear in its first slot and conjugate-linear in its second, a
formally self-adjoint operator cannot have two independent eigenvectors at one non-real
eigenvalue when the form has no independent totally isotropic pair.

No topology, completeness, positivity, spectral theorem, or finite-dimensionality is used.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace ComplexSesquilinearForm

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Conjugate symmetry of a complex sesquilinear form. -/
def IsHermitian (B : ComplexSesquilinearForm V) : Prop :=
  ∀ x y, B x y = starRingEnd ℂ (B y x)

/-- Formal self-adjointness of a linear operator for a sesquilinear form. -/
def IsFormallySelfAdjoint (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ x y, B (A x) y = B x (A y)

/-- Algebraic `Witt index ≤ 1`: no linearly independent pair spans a totally isotropic plane.

The four displayed pairings are exactly the Gram matrix of the restricted form on the pair.
This formulation remains correct without finite-dimensionality, unlike a natural-number
`finrank` convention on an arbitrary infinite-dimensional carrier. -/
def WittIndexAtMostOne (B : ComplexSesquilinearForm V) : Prop :=
  ∀ x y, B x x = 0 → B x y = 0 → B y x = 0 → B y y = 0 →
    ¬ LinearIndependent ℂ ![x, y]

/-- A non-star-fixed common eigenvalue makes every pairing of its eigenvectors vanish. -/
theorem pairing_eq_zero_of_common_eigenvalue_not_star_fixed
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hA : B.IsFormallySelfAdjoint A) {mu : ℂ} (hmu : mu ≠ starRingEnd ℂ mu)
    {x y : V} (hx : A x = mu • x) (hy : A y = mu • y) :
    B x y = 0 := by
  have hpair := hA x y
  rw [hx, hy] at hpair
  simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    smul_eq_mul] at hpair
  have hzero : (mu - starRingEnd ℂ mu) * B x y = 0 := by
    linear_combination hpair
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hmu)

/-- **Two-mode Witt obstruction.** Two independent common eigenvectors of a formally self-adjoint
operator in a Witt-index-one sesquilinear carrier force their eigenvalue to be fixed by complex
conjugation. -/
theorem common_eigenvalue_star_fixed_of_wittIndexAtMostOne
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    {mu : ℂ} {x y : V} (hxy : LinearIndependent ℂ ![x, y])
    (hx : A x = mu • x) (hy : A y = mu • y) :
    starRingEnd ℂ mu = mu := by
  by_contra hstar
  have hmu : mu ≠ starRingEnd ℂ mu := Ne.symm hstar
  have hxx := pairing_eq_zero_of_common_eigenvalue_not_star_fixed B A hA hmu hx hx
  have hxyZero := pairing_eq_zero_of_common_eigenvalue_not_star_fixed B A hA hmu hx hy
  have hyx := pairing_eq_zero_of_common_eigenvalue_not_star_fixed B A hA hmu hy hx
  have hyy := pairing_eq_zero_of_common_eigenvalue_not_star_fixed B A hA hmu hy hy
  exact (hWitt x y hxx hxyZero hyx hyy) hxy

/-- Imaginary-part form of the two-mode Witt obstruction. -/
theorem common_eigenvalue_im_eq_zero_of_wittIndexAtMostOne
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    {mu : ℂ} {x y : V} (hxy : LinearIndependent ℂ ![x, y])
    (hx : A x = mu • x) (hy : A y = mu • y) :
    mu.im = 0 :=
  Complex.conj_eq_iff_im.mp
    (common_eigenvalue_star_fixed_of_wittIndexAtMostOne B A hWitt hA hxy hx hy)

/-- **Injective-intertwiner form.** If an injective comparison carries two independent source
eigenmodes into a Witt-index-one carrier and intertwines their operator with a formally
self-adjoint target operator, then their common eigenvalue is real. -/
theorem common_eigenvalue_im_eq_zero_of_injective_intertwiner
    (B : ComplexSesquilinearForm V) (A : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W)
    (T : W →ₗ[ℂ] V) (hT : Function.Injective T)
    (hWitt : B.WittIndexAtMostOne) (hA : B.IsFormallySelfAdjoint A)
    (hintertwine : A.comp T = T.comp S)
    {mu : ℂ} {x y : W} (hxy : LinearIndependent ℂ ![x, y])
    (hx : S x = mu • x) (hy : S y = mu • y) :
    mu.im = 0 := by
  have himages : LinearIndependent ℂ ![T x, T y] := by
    rw [LinearIndependent.pair_iff] at hxy ⊢
    intro s t hzero
    apply hxy s t
    apply hT
    simpa using hzero
  have hxImage : A (T x) = mu • T x := by
    have h := LinearMap.congr_fun hintertwine x
    change A (T x) = T (S x) at h
    simpa [hx] using h
  have hyImage : A (T y) = mu • T y := by
    have h := LinearMap.congr_fun hintertwine y
    change A (T y) = T (S y) at h
    simpa [hy] using h
  exact common_eigenvalue_im_eq_zero_of_wittIndexAtMostOne
    B A hWitt hA himages hxImage hyImage

end ComplexSesquilinearForm

end

end GaloisForLFunctions.HTGeometry
