import GaloisForLFunctions.HTGeometry.SymmetryFractureDefectConservation
import GaloisForLFunctions.HTGeometry.EventDescentTransgression

/-!
# Event symmetry-recognition defect

For endpoint symmetry actions `source` and `target` and a proposed carrier transport `transport`,
the recognition defect

`target * transport - transport * source`

is the failure of transport to intertwine the two actions. This file proves its covariant
composition law and identifies the defect from a source involution to the identity action with
twice the symmetry-transmuting part of transport.

These are unconditional matrix identities. They are standard failure-to-intertwine and
involution-projector algebra. No physical event, spacetime, force, or dynamical identity principle
is assumed.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Failure of a carrier transport to intertwine its source and target symmetry actions. -/
def eventSymmetryRecognitionDefect
    (source target transport : Matrix n n ℂ) : Matrix n n ℂ :=
  target * transport - transport * source

/--
Recognition defects obey the covariant Leibniz law under composition of endpoint transports.
-/
theorem eventSymmetryRecognitionDefect_compose
    (source middle target first second : Matrix n n ℂ) :
    eventSymmetryRecognitionDefect source target (second * first) =
      eventSymmetryRecognitionDefect middle target second * first +
        second * eventSymmetryRecognitionDefect source middle first := by
  simp only [eventSymmetryRecognitionDefect]
  noncomm_ring

/--
For transport from a source involution to the identity action, recognition defect is exactly twice
the symmetry-transmuting part.
-/
theorem eventSymmetryRecognitionDefect_target_identity
    (source transport : Matrix n n ℂ) :
    eventSymmetryRecognitionDefect source 1 transport =
      (2 : ℂ) • symmetryTransmutingPart source transport := by
  simp only [eventSymmetryRecognitionDefect, symmetryTransmutingPart,
    involutionProjection, one_mul, Matrix.mul_smul, Matrix.mul_sub, mul_one]
  module

/-- A source `-1` action transported to a target `+1` action has defect twice the transport. -/
theorem eventSymmetryRecognitionDefect_source_neg_identity
    (transport : Matrix n n ℂ) :
    eventSymmetryRecognitionDefect (-1) 1 transport =
      (2 : ℂ) • transport := by
  simp only [eventSymmetryRecognitionDefect, mul_neg, mul_one, one_mul, sub_neg_eq_add]
  module

/-- Matching source and target identity actions have zero recognition defect. -/
theorem eventSymmetryRecognitionDefect_source_identity
    (transport : Matrix n n ℂ) :
    eventSymmetryRecognitionDefect 1 1 transport = 0 := by
  simp [eventSymmetryRecognitionDefect]

/-- The matrix recognition defect is the matrix realization of `eventSeamDefect`. -/
theorem eventSymmetryRecognitionDefect_toLin'
    (source target transport : Matrix n n ℂ) :
    (eventSymmetryRecognitionDefect source target transport).toLin' =
      eventSeamDefect target.toLin' source.toLin' transport.toLin' := by
  ext x
  simp [eventSymmetryRecognitionDefect, eventSeamDefect]

end GaloisForLFunctions.HTGeometry

