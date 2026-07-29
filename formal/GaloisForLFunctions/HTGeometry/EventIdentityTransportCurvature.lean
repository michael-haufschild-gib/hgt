import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Curvature of event-created partial identity transport

In a unital C⋆-algebra, a partial isometry `u` creates an initial projection `u⋆u` and a final
projection `uu⋆`. For successive partial isometries `u` then `v`, their ordinary product `vu`
remains a partial isometry exactly when the final projection of `u` commutes with the initial
projection of `v`.

The commutator of those two interface projections is therefore an exact composability defect. The
operator theorem is classical. This module formalizes it as a bridge for the event-generated
identity research programme; it proves no identification with physical spacetime or force.
-/

open scoped CStarAlgebra

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A]

/-- Regular-star form of a partial isometry. In the event interpretation, `u` transports only the
identity support on which it is isometric. -/
def IsPartialIdentityTransport (u : A) : Prop :=
  u * star u * u = u

/-- Interface commutator between the final identity created by `u` and the initial identity
required by its successor `v`. -/
def eventIdentityCurvature (u v : A) : A :=
  (u * star u) * (star v * v) - (star v * v) * (u * star u)

namespace IsPartialIdentityTransport

variable {u v : A}

/-- The adjoint of a partial identity transport is again a partial identity transport. -/
theorem star_transport (hu : IsPartialIdentityTransport u) :
    IsPartialIdentityTransport (star u) := by
  unfold IsPartialIdentityTransport at hu ⊢
  have h := congrArg star hu
  simpa only [star_mul, star_star, mul_assoc] using h

/-- A partial identity transport canonically creates its final support projection. -/
theorem finalProjection (hu : IsPartialIdentityTransport u) :
    IsStarProjection (u * star u) where
  isIdempotentElem := by
    rw [IsIdempotentElem]
    calc
      (u * star u) * (u * star u) = (u * star u * u) * star u := by
        simp only [mul_assoc]
      _ = u * star u := by rw [hu]
  isSelfAdjoint := by simp

/-- A partial identity transport canonically creates its initial support projection. -/
theorem initialProjection (hu : IsPartialIdentityTransport u) :
    IsStarProjection (star u * u) := by
  simpa only [star_star] using hu.star_transport.finalProjection

/-- Commuting interface identities suffice for successive partial transports to compose. -/
theorem mul_of_interface_commute
    (hu : IsPartialIdentityTransport u)
    (hv : IsPartialIdentityTransport v)
    (hcomm : Commute (u * star u) (star v * v)) :
    IsPartialIdentityTransport (v * u) := by
  rw [IsPartialIdentityTransport, star_mul]
  calc
    v * u * (star u * star v) * (v * u) =
        v * (u * star u) * (star v * v) * u := by
          simp only [mul_assoc]
    _ = v * ((u * star u) * (star v * v)) * u := by
          simp only [mul_assoc]
    _ = v * ((star v * v) * (u * star u)) * u := by rw [hcomm.eq]
    _ = (v * star v * v) * (u * star u) * u := by
          simp only [mul_assoc]
    _ = v * (u * star u * u) := by rw [hv]; simp only [mul_assoc]
    _ = v * u := by rw [hu]

private theorem compression_projection_of_mul
    (hv : IsPartialIdentityTransport v)
    (hvu : IsPartialIdentityTransport (v * u)) :
    IsStarProjection ((star v * v) * (u * star u) * (star v * v)) := by
  let w : A := v * u
  let r : A := w * star w
  have hfinal := hvu.finalProjection
  have hr : IsStarProjection r := hfinal
  have hleft : (v * star v) * r = r := by
    change (v * star v) * ((v * u) * star (v * u)) =
      (v * u) * star (v * u)
    calc
      (v * star v) * ((v * u) * star (v * u)) =
          ((v * star v * v) * u) * star (v * u) := by
            simp only [mul_assoc]
      _ = (v * u) * star (v * u) := by rw [hv]
  have hright : r * (v * star v) = r := by
    have h := congrArg star hleft
    simpa [hr.isSelfAdjoint.star_eq] using h
  have hrepr :
      (star v * v) * (u * star u) * (star v * v) =
        star v * r * v := by
    change (star v * v) * (u * star u) * (star v * v) =
      star v * ((v * u) * star (v * u)) * v
    simp only [star_mul, mul_assoc]
  rw [hrepr]
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    calc
      (star v * r * v) * (star v * r * v) =
          star v * (r * (v * star v)) * r * v := by
            simp only [mul_assoc]
      _ = star v * r * r * v := by rw [hright]
      _ = star v * (r * r) * v := by simp only [mul_assoc]
      _ = star v * r * v := by rw [hr.isIdempotentElem]
  · change star (star v * r * v) = star v * r * v
    simp only [star_mul, star_star, hr.isSelfAdjoint.star_eq, mul_assoc]

private theorem commute_of_compression_projection
    (hp : IsStarProjection (u * star u))
    (hq : IsStarProjection (star v * v))
    (hcompression :
      IsStarProjection ((star v * v) * (u * star u) * (star v * v))) :
    Commute (u * star u) (star v * v) := by
  let p : A := u * star u
  let q : A := star v * v
  have hp' : IsStarProjection p := hp
  have hq' : IsStarProjection q := hq
  have hr : IsStarProjection (q * p * q) := hcompression
  have hqcompl : IsStarProjection (1 - q) := hq'.one_sub
  have hprod :
      (q * p * q) * (q * p * q) = q * p * q * p * q := by
    calc
      (q * p * q) * (q * p * q) = q * p * (q * q) * p * q := by
        simp only [mul_assoc]
      _ = q * p * q * p * q := by rw [hq'.isIdempotentElem]
  have hxstarx :
      star ((1 - q) * p * q) * ((1 - q) * p * q) = 0 := by
    calc
      star ((1 - q) * p * q) * ((1 - q) * p * q) =
          q * p * (1 - q) * (1 - q) * p * q := by
            simp [hp'.isSelfAdjoint.star_eq, hq'.isSelfAdjoint.star_eq]
            noncomm_ring
      _ = q * p * ((1 - q) * (1 - q)) * p * q := by
            simp only [mul_assoc]
      _ = q * p * (1 - q) * p * q := by
            rw [hqcompl.isIdempotentElem]
      _ = q * p * p * q - q * p * q * p * q := by
            noncomm_ring
      _ = q * (p * p) * q - q * p * q * p * q := by
            simp only [mul_assoc]
      _ = q * p * q - q * p * q * p * q := by
            rw [hp'.isIdempotentElem]
      _ = q * p * q - (q * p * q) * (q * p * q) := by
            rw [hprod]
      _ = 0 := by rw [hr.isIdempotentElem, sub_self]
  have hx : (1 - q) * p * q = 0 :=
    (CStarRing.star_mul_self_eq_zero_iff _).mp hxstarx
  have hpq : p * q = q * p * q := by
    have hdecomp : q + (1 - q) = 1 := by abel
    calc
      p * q = 1 * (p * q) := by rw [one_mul]
      _ = (q + (1 - q)) * (p * q) := by rw [hdecomp]
      _ = q * p * q + (1 - q) * p * q := by
        simp only [add_mul, mul_assoc]
      _ = q * p * q := by rw [hx, add_zero]
  have hqp : q * p = q * p * q := by
    have h := congrArg star hpq
    simpa only [star_mul, hp'.isSelfAdjoint.star_eq, hq'.isSelfAdjoint.star_eq,
      mul_assoc] using h
  exact hpq.trans hqp.symm

/-- **Partial-identity composition law.** Successive event-created identity transports compose
exactly when their interface support projections commute. -/
theorem mul_iff_interface_commute
    (hu : IsPartialIdentityTransport u)
    (hv : IsPartialIdentityTransport v) :
    IsPartialIdentityTransport (v * u) ↔
      Commute (u * star u) (star v * v) := by
  constructor
  · intro hvu
    exact commute_of_compression_projection hu.finalProjection hv.initialProjection
      (compression_projection_of_mul hv hvu)
  · exact hu.mul_of_interface_commute hv

/-- **Identity-curvature law.** The interface commutator vanishes exactly when two partial
identity transports compose to another partial identity transport. -/
theorem curvature_eq_zero_iff_mul
    (hu : IsPartialIdentityTransport u)
    (hv : IsPartialIdentityTransport v) :
    eventIdentityCurvature u v = 0 ↔
      IsPartialIdentityTransport (v * u) := by
  rw [eventIdentityCurvature, sub_eq_zero]
  exact hu.mul_iff_interface_commute hv |>.symm

end IsPartialIdentityTransport

end GaloisForLFunctions.HTGeometry
