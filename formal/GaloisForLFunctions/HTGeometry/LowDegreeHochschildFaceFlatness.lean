import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Low-degree Hochschild face flatness

This file formalizes the algebraic core of finite-prime BV face flatness.  For an algebra `A`,
`hochschildBoundaryTwoPure a b c` is the degree-two Hochschild boundary

`ab ⊗ c - a ⊗ bc + ca ⊗ b`.

Two commuting idempotents `e` and `f` model commuting prime-range projections, while `x` models
the diagonal weight commuting with both.  The main theorem gives an explicit degree-two boundary
for the difference between the two orders of crossing the corresponding prime faces.

This is deliberately only an algebraic finite-face theorem.  It supplies no bornological,
topological, all-prime, or Xi-localization control; those are the open infinite-completion core.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Degree-one Hochschild boundary `a ⊗ b ↦ ab - ba`. -/
def hochschildBoundaryOne : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A -
    (LinearMap.mul' R A).comp (TensorProduct.comm R A A).toLinearMap

/-- Degree-two Hochschild boundary evaluated on a pure tensor `a ⊗ b ⊗ c`. -/
def hochschildBoundaryTwoPure (a b c : A) : A ⊗[R] A :=
  (a * b) ⊗ₜ[R] c - a ⊗ₜ[R] (b * c) + (c * a) ⊗ₜ[R] b

/-- The displayed degree-two formula is a cycle for the degree-one Hochschild boundary. -/
theorem hochschildBoundaryOne_boundaryTwoPure (a b c : A) :
    hochschildBoundaryOne (R := R) (A := A) (hochschildBoundaryTwoPure a b c) = 0 := by
  simp [hochschildBoundaryOne, hochschildBoundaryTwoPure, mul_assoc]

/-- An idempotent supplies an explicit primitive: if `e² = e` and `a` commutes with `e`, then
the boundary of `2 ae ⊗ e ⊗ e - a ⊗ e ⊗ e` is `a ⊗ e`. -/
theorem hochschild_idempotent_primitive_boundary
    (a e : A) (he : e * e = e) (hae : a * e = e * a) :
    2 • hochschildBoundaryTwoPure (a * e) e e -
        hochschildBoundaryTwoPure a e e =
      a ⊗ₜ[R] e := by
  have hea : e * (a * e) = a * e := by
    rw [← mul_assoc, ← hae, mul_assoc, he]
  simp only [hochschildBoundaryTwoPure, mul_assoc, he, hea]
  rw [← hae]
  abel

/-- **Two-face Hochschild flatness.**  Let `e` and `f` be commuting idempotents and let `x`
commute with both.  The residual between the two orders of crossing the `e`- and `f`-faces,
`f ⊗ ex - e ⊗ fx`, is the explicit sum of degree-two Hochschild boundaries on the left.

In the prime-dilation application, `e = P_m`, `f = P_n`, and `x = Q`.  Thus the finite two-prime
ordering defect vanishes in Hochschild homology. -/
theorem commutingIdempotent_faceDifference_is_boundary
    (e f x : A)
    (he : e * e = e) (hf : f * f = f)
    (hef : e * f = f * e) (hex : e * x = x * e) (hfx : f * x = x * f) :
    (2 • hochschildBoundaryTwoPure ((x * f) * e) e e -
          hochschildBoundaryTwoPure (x * f) e e) -
        (2 • hochschildBoundaryTwoPure ((x * e) * f) f f -
          hochschildBoundaryTwoPure (x * e) f f) -
        hochschildBoundaryTwoPure f e x + hochschildBoundaryTwoPure e f x =
      f ⊗ₜ[R] (e * x) - e ⊗ₜ[R] (f * x) := by
  have hxfe : (x * f) * e = e * (x * f) := by
    calc
      (x * f) * e = x * (f * e) := mul_assoc _ _ _
      _ = x * (e * f) := by rw [← hef]
      _ = (x * e) * f := (mul_assoc _ _ _).symm
      _ = (e * x) * f := by rw [← hex]
      _ = e * (x * f) := mul_assoc _ _ _
  have hxef : (x * e) * f = f * (x * e) := by
    calc
      (x * e) * f = x * (e * f) := mul_assoc _ _ _
      _ = x * (f * e) := by rw [hef]
      _ = (x * f) * e := (mul_assoc _ _ _).symm
      _ = (f * x) * e := by rw [← hfx]
      _ = f * (x * e) := mul_assoc _ _ _
  rw [hochschild_idempotent_primitive_boundary (a := x * f) (e := e) he hxfe]
  rw [hochschild_idempotent_primitive_boundary (a := x * e) (e := f) hf hxef]
  simp only [hochschildBoundaryTwoPure]
  rw [hef, hfx, hex]
  abel

end GaloisForLFunctions.HTGeometry
