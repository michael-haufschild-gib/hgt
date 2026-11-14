import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Polynomial shear and translation frames

On variables `(x,z)`, the map `z ↦ z + θ·x + t` induces a polynomial
pullback. Shear and translation commute, their parameters add, and
subtracting the value at the origin gives the action on polynomials
modulo constants. These identities hold in every degree.

This is the coordinate-free dual of the frame identities in Bi–Sun,
*Lᵖ integrability of functions with Fourier support on high codimension
manifolds*, Proposition 2.1. The relative frame depends only on parameter
differences, as required when comparing the paper's covering boxes.
-/

open MvPolynomial
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section
variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

/-- Horizontal coordinates are `some i`; the distinguished vertical coordinate is `none`. -/
def shearForm (θ : ι → R) : MvPolynomial (Option ι) R :=
  ∑ i, C (θ i) * X (some i)

/-- Pullback by the affine shear `(x,z) ↦ (x,z+θ·x+t)`. -/
def pull (θ : ι → R) (t : R) :
    MvPolynomial (Option ι) R →ₐ[R] MvPolynomial (Option ι) R :=
  bind₁ (fun j => match j with
    | none => X none + shearForm θ + C t
    | some i => X (some i))

@[simp] theorem pull_horizontal (θ : ι → R) (t : R) (i : ι) :
    pull θ t (X (some i)) = X (some i) := by
  exact bind₁_X_right _ _

@[simp] theorem pull_vertical (θ : ι → R) (t : R) :
    pull θ t (X none) = X none + shearForm θ + C t := by
  exact bind₁_X_right _ _

@[simp] theorem pull_constant (θ : ι → R) (t c : R) : pull θ t (C c) = C c := by
  exact bind₁_C_right _ _

@[simp] theorem pull_shearForm (θ φ : ι → R) (t : R) :
    pull θ t (shearForm φ) = shearForm φ := by
  simp only [shearForm, map_sum, map_mul, pull_constant, pull_horizontal]

theorem shearForm_add (θ φ : ι → R) : shearForm (θ + φ) = shearForm θ + shearForm φ := by
  simp only [shearForm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem shearForm_zero : shearForm (0 : ι → R) = 0 := by
  simp [shearForm]

/-- The full affine frame composition law. -/
theorem pull_comp (θ φ : ι → R) (t s : R) :
    (pull θ t).comp (pull φ s) = pull (θ + φ) (t + s) := by
  ext j
  cases j with
  | none => simp only [AlgHom.comp_apply, pull_vertical, map_add, pull_shearForm,
      pull_constant, shearForm_add]; ring
  | some i => simp only [AlgHom.comp_apply, pull_horizontal]

@[simp] theorem pull_zero : pull (0 : ι → R) 0 = AlgHom.id R _ := by
  ext j
  cases j <;> simp

/-- Shear and vertical translation commute in every polynomial degree. -/
theorem shear_translation_commute (θ : ι → R) (t : R) :
    (pull θ 0).comp (pull 0 t) = (pull 0 t).comp (pull θ 0) := by
  simp only [pull_comp, add_zero, zero_add]

/-- Relative frames are controlled by differences of shear and translation parameters. -/
theorem relative_pull (θ φ : ι → R) (t s : R) :
    (pull (-θ) (-t)).comp (pull φ s) = pull (φ - θ) (s - t) := by
  rw [pull_comp]
  congr 1 <;> abel

/-- Polynomial representative modulo constants, normalized to vanish at the origin. -/
def centeredPull (θ : ι → R) (t : R) (p : MvPolynomial (Option ι) R) :
    MvPolynomial (Option ι) R :=
  pull θ t p - C (eval (0 : Option ι → R) (pull θ t p))

@[simp] theorem centeredPull_at_zero (θ : ι → R) (t : R)
    (p : MvPolynomial (Option ι) R) :
    eval (0 : Option ι → R) (centeredPull θ t p) = 0 := by
  simp [centeredPull]

/-- Recentering preserves the frame composition law; intermediate constants cancel. -/
theorem centeredPull_comp (θ φ : ι → R) (t s : R)
    (p : MvPolynomial (Option ι) R) :
    centeredPull θ t (centeredPull φ s p) = centeredPull (θ + φ) (t + s) p := by
  have h := DFunLike.congr_fun (pull_comp θ φ t s) p
  simp only [AlgHom.comp_apply] at h
  simp only [centeredPull, map_sub, pull_constant, h, eval_C]
  ring

/-- Inverting a centered frame recovers every nonconstant coefficient exactly. -/
theorem centeredPull_inverse (θ : ι → R) (t : R)
    (p : MvPolynomial (Option ι) R) :
    centeredPull (-θ) (-t) (centeredPull θ t p) = p - C (eval 0 p) := by
  rw [centeredPull_comp]
  simp only [neg_add_cancel, centeredPull, pull_zero, AlgHom.id_apply]

/-- No polynomial information is lost after retaining the original constant coefficient. -/
theorem reconstruction (θ : ι → R) (t : R) (p : MvPolynomial (Option ι) R) :
    centeredPull (-θ) (-t) (centeredPull θ t p) + C (eval 0 p) = p := by
  rw [centeredPull_inverse, sub_add_cancel]

#print axioms pull_comp
#print axioms shear_translation_commute
#print axioms relative_pull
#print axioms centeredPull_comp
#print axioms reconstruction

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
