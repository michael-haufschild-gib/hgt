import Mathlib.Algebra.Module.Basic

/-!
# Polarized transfer law behind Deninger's half-density shift

Projection-formula adjunction, Hodge naturality, and the degree formula imply that pullback scales
the cup--Hodge metric by its degree.  This is the abstract source theorem behind normalization by
the square root of a finite-syntomic degree.

The Milnor--Witt specialization must still prove that Gamma-polarized realization sends the
quadratic degree `n_epsilon` to scalar rank `n`; no positivity of the bare quadratic transfer is
assumed here.
-/

namespace RHTower

section PolarizedTransfer

variable {R V : Type*}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/--
Poincare adjunction plus Hodge naturality converts the push-pull degree formula into exact
weight scaling of the cup--Hodge pairing.
-/
theorem deningerPolarizedTransfer_pairing_scale
    (B : V → V → R) (pull push hodge : V → V) (q : R)
    (hadj : ∀ x z, B (pull x) z = B x (push z))
    (hhodge : ∀ y, hodge (pull y) = pull (hodge y))
    (hdegree : ∀ y, push (pull y) = q • y)
    (hlinearRight : ∀ x c y, B x (c • y) = c * B x y)
    (x y : V) :
    B (pull x) (hodge (pull y)) = q * B x (hodge y) := by
  calc
    B (pull x) (hodge (pull y)) =
        B (pull x) (pull (hodge y)) := by rw [hhodge]
    _ = B x (push (pull (hodge y))) := hadj _ _
    _ = B x (q • hodge y) := by rw [hdegree]
    _ = q * B x (hodge y) := hlinearRight _ _ _

end PolarizedTransfer

end RHTower

