import Mathlib

/-!
# Integral roots in a polynomial fraction field

A root in `Frac(F[u])` of a monic polynomial over `F[u]` is already a polynomial in `u`.
This is the root-integrality input in the field form of algebraic simple connectedness of the
affine line: after scalar extension to an algebraic closure, the roots of an everywhere-unramified
cover lie in the polynomial ring rather than merely in its rational function field.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **A monic integral root in `Frac(F[u])` lies in `F[u]`.** -/
theorem exists_polynomial_eq_of_monic_eval₂_eq_zero {F : Type*} [Field F]
    (p : Polynomial (Polynomial F)) (hp : p.Monic)
    (x : FractionRing (Polynomial F))
    (hx : Polynomial.eval₂
      (algebraMap (Polynomial F) (FractionRing (Polynomial F))) x p = 0) :
    ∃ q : Polynomial F,
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) q = x := by
  have hi : IsIntegral (Polynomial F) x := ⟨p, hp, hx⟩
  exact
    (isIntegrallyClosed_iff (FractionRing (Polynomial F))).mp
      (by infer_instance) hi

/-- **Root form of `exists_polynomial_eq_of_monic_eval₂_eq_zero`.**  Every root in the rational
function field of the scalar extension of a monic polynomial over `F[u]` is represented by an
element of `F[u]`. -/
theorem exists_polynomial_eq_of_monic_map_isRoot {F : Type*} [Field F]
    (p : Polynomial (Polynomial F)) (hp : p.Monic)
    (x : FractionRing (Polynomial F))
    (hx : (p.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))).IsRoot x) :
    ∃ q : Polynomial F,
      algebraMap (Polynomial F) (FractionRing (Polynomial F)) q = x := by
  apply exists_polynomial_eq_of_monic_eval₂_eq_zero p hp x
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using hx

end GaloisForLFunctions.HTGeometry
