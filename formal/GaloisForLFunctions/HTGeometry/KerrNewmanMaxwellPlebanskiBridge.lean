import GaloisForLFunctions.HTGeometry.KerrNewmanEinsteinMaxwellAlgebra
import GaloisForLFunctions.HTGeometry.EventPlebanskiSimplicity

/-!
# Kerr--Newman Maxwell field in the event-coframe exterior algebra

The canonical flat-frame Kerr--Newman Maxwell matrix has support precisely in the `01` and `23`
planes.  This module maps those two coefficients to the existing event-coframe exterior algebra.
It proves the resulting wedge square and relates the pseudoscalar coefficient to the existing
Lorentz quadratic invariant and Maxwell stress magnitude.

This is an algebraic coefficient bridge.  It does not introduce a Hodge star, a curved
Kerr--Newman tetrad, Maxwell dynamics, or a physical reality condition.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Exteriorization of the `01` and `23` components of a real antisymmetric field matrix. -/
def kerrNewmanMaxwellTwoPlaneExteriorization (F : Matrix (Fin 4) (Fin 4) ℝ) :
    EventCoframeExterior :=
  eventTwoPlaneForm (F 0 1 : ℂ) (F 2 3 : ℂ)

/-- The exterior representative of the canonical parallel electric/magnetic Kerr--Newman field. -/
def kerrNewmanCanonicalMaxwellPlebanskiForm
    (electric magnetic : ℝ) : EventCoframeExterior :=
  eventTwoPlaneForm (electric : ℂ) (magnetic : ℂ)

/-- Exteriorization recovers the coefficients of the canonical Kerr--Newman Maxwell matrix. -/
theorem kerrNewmanCanonicalMaxwellPlebanskiForm_eq_exteriorization
    (electric magnetic : ℝ) :
    kerrNewmanMaxwellTwoPlaneExteriorization
        (kerrNewmanCanonicalMaxwellTwoForm electric magnetic) =
      kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic := by
  simp [kerrNewmanMaxwellTwoPlaneExteriorization, kerrNewmanCanonicalMaxwellPlebanskiForm,
    kerrNewmanCanonicalMaxwellTwoForm]

/-- The canonical electromagnetic exterior field has pseudoscalar coefficient `2 E B`. -/
theorem kerrNewmanCanonicalMaxwellPlebanskiForm_sq
    (electric magnetic : ℝ) :
    kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic *
        kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic =
      (2 * (electric : ℂ) * (magnetic : ℂ)) • eventPlebanskiVolume := by
  simpa [kerrNewmanCanonicalMaxwellPlebanskiForm] using
    eventTwoPlaneForm_sq (electric : ℂ) (magnetic : ℂ)

/-- Unit magnetic normalization of the canonical field is the first existing Plebanski form. -/
theorem kerrNewmanCanonicalMaxwellPlebanskiForm_unitMagnetic_eq_eventSigmaOne
    (electric : ℝ) :
    kerrNewmanCanonicalMaxwellPlebanskiForm electric 1 = eventSigmaOne (electric : ℂ) := by
  simp [kerrNewmanCanonicalMaxwellPlebanskiForm, eventTwoPlaneForm, eventSigmaOne]

/-- At unit magnetic normalization, the Kerr--Newman exterior field obeys the existing Plebanski
simplicity law exactly. -/
theorem kerrNewmanCanonicalMaxwellPlebanskiForm_unitMagnetic_sq_via_eventSigma
    (electric : ℝ) :
    kerrNewmanCanonicalMaxwellPlebanskiForm electric 1 *
        kerrNewmanCanonicalMaxwellPlebanskiForm electric 1 =
      (2 * (electric : ℂ)) • eventPlebanskiVolume := by
  rw [kerrNewmanCanonicalMaxwellPlebanskiForm_unitMagnetic_eq_eventSigmaOne]
  simpa [eventSigma] using eventSigma_simplicity (electric : ℂ) 0 0

/-- The Lorentz quadratic invariant and exterior pseudoscalar coefficient recover the square of
the canonical Maxwell stress magnitude. -/
theorem kerrNewmanCanonicalMaxwell_invariant_quadrature
    (electric magnetic : ℝ) :
    kerrNewmanTwoFormQuadraticInvariant
        (kerrNewmanCanonicalMaxwellTwoForm electric magnetic) ^ 2 +
      4 * (2 * electric * magnetic) ^ 2 =
        16 * kerrNewmanCanonicalMaxwellStressMagnitude electric magnetic ^ 2 := by
  rw [kerrNewmanCanonicalMaxwellTwoForm_invariant]
  simp [kerrNewmanCanonicalMaxwellStressMagnitude]
  ring

end GaloisForLFunctions.HTGeometry
