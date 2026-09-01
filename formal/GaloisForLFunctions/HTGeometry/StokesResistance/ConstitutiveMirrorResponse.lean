import GaloisForLFunctions.HTGeometry.StokesResistance.MirrorSymmetricResponse
import GaloisForLFunctions.HTGeometry.StokesResistance.ConstitutiveC2Application

/-!
# Constitutive mixed-parity mirror response

This module applies Moreau's mirror-fixed symmetric-response formula to the corpus's constitutive
`C₂` parity split. On one even and one odd channel, the mirror has trace zero. Exactly two of the
three reciprocal quadratic responses survive: even-even and odd-odd. The mixed even-odd response is
the unique forbidden coefficient, matching the separate vanishing theorem for equivariant maps
between the trivial and sign carriers.
-/

open scoped BigOperators Kronecker Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

/-- One even and one odd constitutive channel. -/
def constitutiveMixedParityMirror : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then -1 else 1

/-- Mixed constitutive parity is an involution. -/
theorem constitutiveMixedParityMirror_sq :
    constitutiveMixedParityMirror * constitutiveMixedParityMirror = 1 := by
  rw [constitutiveMixedParityMirror, Matrix.diagonal_mul_diagonal]
  ext b c
  cases b <;> cases c <;> simp

/-- Equal even and odd multiplicities make the mirror character zero. -/
theorem trace_constitutiveMixedParityMirror :
    Matrix.trace constitutiveMixedParityMirror = 0 := by
  rw [constitutiveMixedParityMirror, Matrix.trace_diagonal, Fintype.sum_bool]
  simp

/-- Two of three reciprocal quadratic constitutive responses survive parity. -/
theorem constitutiveMixedParity_mirrorSymmetricResponse_finrank :
    Module.finrank ℂ
      (LinearMap.range
        (mirrorSymmetricResponseProjection constitutiveMixedParityMirror).toLin') = 2 := by
  have htrace := trace_mirrorSymmetricResponseProjection_eq_finrank
    constitutiveMixedParityMirror constitutiveMixedParityMirror_sq
  rw [trace_mirrorSymmetricResponseProjection constitutiveMixedParityMirror
      constitutiveMixedParityMirror_sq,
    trace_constitutiveMixedParityMirror] at htrace
  norm_num at htrace
  exact_mod_cast htrace.symm

end GaloisForLFunctions.HTGeometry.StokesResistance
