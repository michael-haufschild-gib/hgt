import GaloisForLFunctions.HTGeometry.EventIdentityTransportCurvature

/-!
# Partial identity transports exist

An event transport is a partial identity when `u u* u = u`, the partial-isometry equation.  The
curvature theorems assume it and nothing produced one.  Three standard classes realize it: the zero
transport, every isometry, and every self-adjoint idempotent — so every projection of the algebra
is an event transport.  The class is closed under the star operation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A]

/-- The zero transport is a partial identity. -/
theorem isPartialIdentityTransport_zero : IsPartialIdentityTransport (0 : A) := by
  rw [IsPartialIdentityTransport]
  simp

/-- **Every isometry is a partial identity transport.** -/
theorem isPartialIdentityTransport_of_star_mul_self {u : A} (h : star u * u = 1) :
    IsPartialIdentityTransport u := by
  rw [IsPartialIdentityTransport, mul_assoc, h, mul_one]

/-- The unit is a partial identity transport. -/
theorem isPartialIdentityTransport_one : IsPartialIdentityTransport (1 : A) :=
  isPartialIdentityTransport_of_star_mul_self (by simp)

/-- **Every self-adjoint idempotent is a partial identity transport,** so every projection of the
algebra is an event transport. -/
theorem isPartialIdentityTransport_of_selfAdjoint_idempotent {u : A} (hstar : star u = u)
    (hidem : u * u = u) : IsPartialIdentityTransport u := by
  rw [IsPartialIdentityTransport, hstar, hidem, hidem]

/-- The star of a partial identity transport is one. -/
theorem IsPartialIdentityTransport.star_mem {u : A} (h : IsPartialIdentityTransport u) :
    IsPartialIdentityTransport (star u) := by
  rw [IsPartialIdentityTransport, star_star]
  have hstar := congrArg (fun x : A => star x) h
  simpa only [star_mul, star_star, mul_assoc] using hstar

end GaloisForLFunctions.HTGeometry
