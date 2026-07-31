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

/-- A pairing whose second-variable transpose is bijective separates the top module. -/
theorem endpointPairing_separating_of_bijective
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hperf : Function.Bijective pair02.flip) :
    ∀ z : A2, (∀ x : A0, pair02 x z = 0) → z = 0 := by
  intro z hz
  have h0 : pair02.flip z = 0 := by
    ext x
    simpa using hz x
  have hz0 : pair02.flip z = pair02.flip 0 := by simpa using h0
  exact hperf.injective hz0

/-- Perfect endpoint duality identifies the top module with the dual of the bottom module. -/
noncomputable def endpointTopDualEquiv
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hperf : Function.Bijective pair02.flip) :
    A2 ≃ₗ[R] Module.Dual R A0 :=
  LinearEquiv.ofBijective pair02.flip hperf

/-- Perfect duality against a rank-one free bottom module makes the top module rank-one free. -/
noncomputable def endpointTopEquiv
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hperf : Function.Bijective pair02.flip)
    (e : A0 ≃ₗ[R] R) :
    A2 ≃ₗ[R] R :=
  (endpointTopDualEquiv pair02 hperf).trans
    ((e.dualMap).symm.trans (LinearMap.ringLmapEquivSelf R R R))

/-- **Endpoint purity.**  A vanishing bottom generator together with a perfect weight-one endpoint
pairing against a rank-one free bottom module forces the top module to be rank-one free and its
generator to be the identity; this is the statement `H² ≃ R(-1)`. -/
theorem deningerEndpointPurity
    (theta0 : Module.End R A0)
    (theta2 : Module.End R A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hTheta :
      ∀ x z,
        pair02 (theta0 x) z + pair02 x (theta2 z) =
          pair02 x z)
    (htheta0 : theta0 = 0)
    (hperf : Function.Bijective pair02.flip)
    (e : A0 ≃ₗ[R] R) :
    theta2 = LinearMap.id ∧ Nonempty (A2 ≃ₗ[R] R) :=
  ⟨deningerTheta2_eq_id_of_theta0_eq_zero_of_endpointPairing theta0 theta2 pair02 hTheta htheta0
      (endpointPairing_separating_of_bijective pair02 hperf),
    ⟨endpointTopEquiv pair02 hperf e⟩⟩

end EndpointPurity

end RHTower
