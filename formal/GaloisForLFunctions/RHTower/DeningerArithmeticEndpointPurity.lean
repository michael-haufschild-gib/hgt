import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCohomology

/-!
# Endpoint purity forced by Poincare duality

Deninger's rational-Witt dynamical approximation already has one-dimensional `H⁰` with trivial
flow.  Once degree-two Poincare duality is constructed, its weight-one derivation law forces the
top generator to be the identity.  Thus the `H²` weight is a consequence of the source `H⁰`
theorem and perfect endpoint duality.

This file proves the forcing argument abstractly.  It assumes no zeta-zero information,
positivity, or Riemann hypothesis.
-/

namespace RHTower

section EndpointPurity

variable {R A0 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A2] [Module R A2]

/--
If the bottom generator is zero and a separating endpoint pairing has weight one, then the top
generator is the identity.
-/
theorem deningerTheta2_eq_id_of_theta0_eq_zero_of_endpointPairing
    (theta0 : Module.End R A0)
    (theta2 : Module.End R A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hTheta :
      ∀ x z,
        pair02 (theta0 x) z + pair02 x (theta2 z) =
          pair02 x z)
    (htheta0 : theta0 = 0)
    (hseparating :
      ∀ z : A2, (∀ x : A0, pair02 x z = 0) → z = 0) :
    theta2 = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.mp
  apply hseparating
  intro x
  have h := hTheta x z
  simp only [htheta0, LinearMap.zero_apply, map_zero, zero_add] at h
  simp only [map_sub, LinearMap.id_apply, h, sub_self]

end EndpointPurity

end RHTower
