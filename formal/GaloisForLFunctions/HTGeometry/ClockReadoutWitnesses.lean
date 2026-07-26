import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy

/-!
# Realizations of the conjugation-invariant readout interface

Conjugation invariance is realized by constant readouts, by every readout of a commutative
calibration group, and — canonically — by the conjugacy-class map.  The last one is the universal
conjugation-invariant readout, so the nonabelian closed-clock observability theorem applies to it
with no interface premise: the conjugacy class of a closed holonomy is gauge invariant.
-/

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Group A]

/-! ## Realizations -/

theorem conjugationInvariantClockReadout_const {B : Type*} (b : B) :
    ConjugationInvariantClockReadout (fun _ : A => b) := fun _ _ => rfl

/-- Over a commutative calibration group every readout is conjugation invariant. -/
theorem conjugationInvariantClockReadout_of_commGroup {A : Type*} [CommGroup A]
    {B : Type*} (readout : A → B) :
    ConjugationInvariantClockReadout readout := by
  intro g a
  congr 1
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The canonical conjugation-invariant readout.**  The conjugacy-class map is conjugation
invariant. -/
theorem conjugationInvariantClockReadout_conjClasses :
    ConjugationInvariantClockReadout (ConjClasses.mk : A → ConjClasses A) := by
  intro g a
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_iff.mpr ⟨g, by group⟩

/-! ## The observability theorem with no interface premise -/

/-- **Conjugacy-class gauge invariance.**  The conjugacy class of a closed clock holonomy does not
depend on the calibration gauge, with no invariance premise. -/
theorem clockClosedConjClass_gauge_invariant {V : Type*} {G : SimpleGraph V}
    (g : V → A) (c : V → V → A) (u : V) (p : G.Walk u u) :
    ConjClasses.mk (clockWalkTransport (clockCalibrationGauge g c) p) =
      ConjClasses.mk (clockWalkTransport c p) :=
  clockClosedReadout_gauge_invariant ConjClasses.mk
    conjugationInvariantClockReadout_conjClasses g c u p

end GaloisForLFunctions.HTGeometry
