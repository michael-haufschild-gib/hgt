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

/-- Within the canonical parallel electric/magnetic ansatz, vanishing exterior square selects
exactly the pure-electric or pure-magnetic axes. -/
theorem kerrNewmanCanonicalMaxwellPlebanskiForm_sq_eq_zero_iff
    (electric magnetic : ℝ) :
    kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic *
        kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic = 0 ↔
      electric = 0 ∨ magnetic = 0 := by
  constructor
  · intro h
    rw [kerrNewmanCanonicalMaxwellPlebanskiForm_sq] at h
    have hscalar : 2 * (electric : ℂ) * (magnetic : ℂ) = 0 :=
      (smul_eq_zero.mp h).resolve_right eventPlebanskiVolume_ne_zero
    rcases mul_eq_zero.mp hscalar with htwoElectric | hmagnetic
    · rcases mul_eq_zero.mp htwoElectric with htwo | helectric
      · exact False.elim (two_ne_zero htwo)
      · exact Or.inl (Complex.ofReal_eq_zero.mp helectric)
    · exact Or.inr (Complex.ofReal_eq_zero.mp hmagnetic)
  · rintro (rfl | rfl)
    · rw [kerrNewmanCanonicalMaxwellPlebanskiForm_sq]
      simp
    · rw [kerrNewmanCanonicalMaxwellPlebanskiForm_sq]
      simp

/-- In the canonical two-plane ansatz, simultaneous vanishing of the Lorentz quadratic and
exterior pseudoscalar invariants forces the field itself to vanish. -/
theorem kerrNewmanCanonicalMaxwell_both_invariants_zero_iff
    (electric magnetic : ℝ) :
    kerrNewmanTwoFormQuadraticInvariant
        (kerrNewmanCanonicalMaxwellTwoForm electric magnetic) = 0 ∧
      kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic *
        kerrNewmanCanonicalMaxwellPlebanskiForm electric magnetic = 0 ↔
      electric = 0 ∧ magnetic = 0 := by
  constructor
  · rintro ⟨hquadratic, hwedge⟩
    rw [kerrNewmanCanonicalMaxwellTwoForm_invariant] at hquadratic
    rcases kerrNewmanCanonicalMaxwellPlebanskiForm_sq_eq_zero_iff electric magnetic |>.mp
      hwedge with helectric | hmagnetic
    · subst electric
      have hmagneticSq : magnetic ^ 2 = 0 := by
        nlinarith
      exact ⟨rfl, (sq_eq_zero_iff).mp hmagneticSq⟩
    · subst magnetic
      have helectricSq : electric ^ 2 = 0 := by
        nlinarith
      exact ⟨(sq_eq_zero_iff).mp helectricSq, rfl⟩
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp [kerrNewmanCanonicalMaxwellTwoForm_invariant]
    · rw [kerrNewmanCanonicalMaxwellPlebanskiForm_sq]
      simp

end GaloisForLFunctions.HTGeometry
