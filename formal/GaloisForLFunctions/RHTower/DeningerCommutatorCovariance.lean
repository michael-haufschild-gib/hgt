import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

/-!
# Real-Fourier covariance of a collar commutator

The Möbius--Fourier commutator has the shape `S h = F(E h) - E(J h)`, where `J` is the collar
exchange and `F` the Fourier transform.  Its covariance under collar exchange is purely algebraic:
it needs only that `J` is an involution and that `F` squares to the identity on the range of `E` —
the latter being Fourier inversion together with evenness of the preimages.

`S(J h) = -F(S h)`

So collar exchange acts on the target by `-F`, and the kernel is real-Fourier invariant before any
norm square is taken.

* `deningerCollarCommutator` : the commutator `F ∘ E - E ∘ J`.
* `deningerCollarCommutator_covariance` : **`S(J h) = -F(S h)`.**
-/

namespace RHTower

variable {H V : Type*} [AddCommGroup V]

/-- The collar commutator `S h = F(E h) - E(J h)`. -/
def deningerCollarCommutator (E : H → V) (J : H → H) (F : V →+ V) (h : H) : V :=
  F (E h) - E (J h)

/-- **Real-Fourier covariance.**  Collar exchange acts on the target by `-F`.  The only inputs are
that the exchange is an involution and that `F` squares to the identity on the preimages. -/
theorem deningerCollarCommutator_covariance (E : H → V) (J : H → H) (F : V →+ V)
    (hJ : ∀ h, J (J h) = h) (hF : ∀ h, F (F (E h)) = E h) (h : H) :
    deningerCollarCommutator E J F (J h)
      = -(F (deningerCollarCommutator E J F h)) := by
  rw [deningerCollarCommutator, deningerCollarCommutator, hJ, map_sub, hF]
  abel

/-- The commutator vanishes exactly when the two collars are Fourier partners. -/
theorem deningerCollarCommutator_eq_zero_iff (E : H → V) (J : H → H) (F : V →+ V) (h : H) :
    deningerCollarCommutator E J F h = 0 ↔ F (E h) = E (J h) := by
  rw [deningerCollarCommutator, sub_eq_zero]

/-- Covariance makes the kernel invariant under collar exchange. -/
theorem deningerCollarCommutator_kernel_invariant (E : H → V) (J : H → H) (F : V →+ V)
    (hJ : ∀ h, J (J h) = h) (hF : ∀ h, F (F (E h)) = E h) {h : H}
    (hzero : deningerCollarCommutator E J F h = 0) :
    deningerCollarCommutator E J F (J h) = 0 := by
  rw [deningerCollarCommutator_covariance E J F hJ hF h, hzero, map_zero, neg_zero]

end RHTower
