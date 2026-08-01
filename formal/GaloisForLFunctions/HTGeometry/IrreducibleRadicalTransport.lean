import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Irreducibility of a radical polynomial transports along an isomorphism

An isomorphism of the coefficient rings induces one of the polynomial rings, carrying a radical
polynomial to the radical polynomial of the image of its constant.  Isomorphisms preserve
irreducibility, so the property transports.

This reads a statement proved in a convenient model as a statement about the field it models.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mapEquiv_X_pow_sub_C (e : R ≃+* S) (n : ℕ) (a : R) :
    Polynomial.mapEquiv e (Polynomial.X ^ n - Polynomial.C a : Polynomial R) =
      Polynomial.X ^ n - Polynomial.C (e a) := by
  rw [Polynomial.mapEquiv_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]
  rfl

/-- **Irreducibility of a radical polynomial transports along an isomorphism.** -/
theorem irreducible_X_pow_sub_C_map (e : R ≃+* S) {n : ℕ} {a : R}
    (h : Irreducible (Polynomial.X ^ n - Polynomial.C a : Polynomial R)) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (e a) : Polynomial S) := by
  rw [← mapEquiv_X_pow_sub_C e n a]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)
    (x := (Polynomial.X ^ n - Polynomial.C a : Polynomial R))).2 h

end GaloisForLFunctions.HTGeometry
