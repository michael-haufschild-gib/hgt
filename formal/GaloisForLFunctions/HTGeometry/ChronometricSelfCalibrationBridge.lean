/-
The chronometric and self-calibrating metric interfaces are one interface.

The tree carries four metric-field structures with independent rigidity proofs:

* `ChronometricMetricField Event Tangent` — a symmetric form on a fixed model fiber;
* `BundleChronometricMetric Event Fiber` — the same over a bundle of fibers;
* `SelfCalibratingMetricField Event Covector` — a symmetric form together with an unknown nonzero
  pointwise calibration;
* `BundleSelfCalibratingMetric Event Fiber` — the bundle version of the latter.

The self-calibrating structures are the chronometric ones plus a calibration channel, so each
carries the corresponding chronometric field as a reduct, and each chronometric field is the
calibration-one self-calibrating field.  This file records the two maps and the resulting
factorizations, and then *derives* the chronometric injectivity theorems from the two-mass
self-calibrating ones — exhibiting the chronometric rigidity results as the calibration-one case
rather than as independent statements.

The trivialized structures are in turn the constant-fiber case of the bundle structures, so the
same reduction identifies `ChronometricMetricField` results with `BundleChronometricMetric`
results over the constant family.

Nothing new is assumed: every theorem below is obtained from the existing two-mass identifiability
theorems by supplying their premises from the structures themselves.
-/
import GaloisForLFunctions.HTGeometry.SelfCalibratingBundleQuotientRigidity

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-! ## The trivialized bridge -/

section Trivialized

variable {Event : Type u} {Covector : Type v} [AddCommGroup Covector] [Module ℝ Covector]

/-- **Forgetting the calibration.**  A self-calibrating inverse-metric field carries an underlying
chronometric metric field, namely its symmetric form channel. -/
def SelfCalibratingMetricField.toChronometricMetricField
    (g : SelfCalibratingMetricField Event Covector) :
    ChronometricMetricField Event Covector where
  form := g.form
  symmetric := g.symmetric

@[simp] theorem SelfCalibratingMetricField.toChronometricMetricField_form
    (g : SelfCalibratingMetricField Event Covector) :
    g.toChronometricMetricField.form = g.form := rfl

@[simp] theorem SelfCalibratingMetricField.squaredInterval_toChronometricMetricField
    (g : SelfCalibratingMetricField Event Covector) (event : Event) (v : Covector) :
    g.toChronometricMetricField.squaredInterval event v = g.form event v v := rfl

/-- **The symbol channel factors through the reduct.**  The calibrated quadratic principal symbol
of the two-mass observation is the calibration times the reduct's squared interval. -/
theorem SelfCalibratingMetricField.twoMassObservation_snd_eq
    (massSq₁ massSq₂ : ℝ) (g : SelfCalibratingMetricField Event Covector)
    (event : Event) (v : Covector) :
    (SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂ g).2 event v =
      g.calibration event * g.toChronometricMetricField.squaredInterval event v := rfl

/-- **Calibrating by one.**  A chronometric metric field is the self-calibrating field whose
calibration is constant `1`. -/
def ChronometricMetricField.toSelfCalibrating
    (g : ChronometricMetricField Event Covector) :
    SelfCalibratingMetricField Event Covector where
  calibration := fun _ => 1
  calibration_ne_zero := fun _ => one_ne_zero
  form := g.form
  symmetric := g.symmetric

@[simp] theorem ChronometricMetricField.toChronometricMetricField_toSelfCalibrating
    (g : ChronometricMetricField Event Covector) :
    g.toSelfCalibrating.toChronometricMetricField = g := rfl

/-- The calibration-one embedding is injective. -/
theorem ChronometricMetricField.toSelfCalibrating_injective :
    Function.Injective
      (ChronometricMetricField.toSelfCalibrating :
        ChronometricMetricField Event Covector → SelfCalibratingMetricField Event Covector) := by
  intro g h hgh
  have := congrArg SelfCalibratingMetricField.toChronometricMetricField hgh
  simpa using this

/-- **The squared interval is the calibration-one two-mass symbol.** -/
theorem ChronometricMetricField.twoMassObservation_toSelfCalibrating_snd
    (g : ChronometricMetricField Event Covector) :
    (SelfCalibratingMetricField.twoMassObservation 1 0 g.toSelfCalibrating).2 =
      g.squaredInterval := by
  funext event v
  simp [SelfCalibratingMetricField.twoMassObservation,
    ChronometricMetricField.toSelfCalibrating, ChronometricMetricField.squaredInterval]

/-- **Chronometric identifiability is the calibration-one case of two-mass identifiability.**  The
chronometric injectivity theorem is derived here from the self-calibrating one rather than proved
again: a chronometric field is calibration-one, and on calibration-one fields the two-mass
observation is exactly the squared interval. -/
theorem ChronometricMetricField.squaredInterval_injective_of_twoMass :
    Function.Injective
      (ChronometricMetricField.squaredInterval :
        ChronometricMetricField Event Covector → Event → Covector → ℝ) := by
  intro g h heq
  refine ChronometricMetricField.toSelfCalibrating_injective ?_
  refine SelfCalibratingMetricField.twoMassObservation_injective
    (massSq₁ := (1 : ℝ)) (massSq₂ := (0 : ℝ)) (by norm_num) ?_
  refine Prod.ext ?_ ?_
  · funext event
    simp [SelfCalibratingMetricField.twoMassObservation,
      ChronometricMetricField.toSelfCalibrating]
  · rw [ChronometricMetricField.twoMassObservation_toSelfCalibrating_snd,
      ChronometricMetricField.twoMassObservation_toSelfCalibrating_snd, heq]

/-- **The two-mass observation determines the underlying chronometric field.**  Discharging the
injectivity premise from the existing two-mass theorem. -/
theorem SelfCalibratingMetricField.toChronometricMetricField_eq_of_twoMassObservation_eq
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {g h : SelfCalibratingMetricField Event Covector}
    (hdata : SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂ g =
      SelfCalibratingMetricField.twoMassObservation massSq₁ massSq₂ h) :
    g.toChronometricMetricField = h.toChronometricMetricField :=
  congrArg SelfCalibratingMetricField.toChronometricMetricField
    (SelfCalibratingMetricField.twoMassObservation_injective hmass hdata)

end Trivialized

/-! ## The bundle bridge -/

section Bundle

variable {Event : Type u} {Fiber : Event → Type v}
  [∀ x, AddCommGroup (Fiber x)] [∀ x, Module ℝ (Fiber x)]

/-- **Forgetting the calibration over a bundle.** -/
def BundleSelfCalibratingMetric.toBundleChronometricMetric
    (g : BundleSelfCalibratingMetric Event Fiber) :
    BundleChronometricMetric Event Fiber where
  form := g.form
  symmetric := g.symmetric

@[simp] theorem BundleSelfCalibratingMetric.toBundleChronometricMetric_form
    (g : BundleSelfCalibratingMetric Event Fiber) :
    g.toBundleChronometricMetric.form = g.form := rfl

@[simp] theorem BundleSelfCalibratingMetric.squaredInterval_toBundleChronometricMetric
    (g : BundleSelfCalibratingMetric Event Fiber) (x : Event) (v : Fiber x) :
    g.toBundleChronometricMetric.squaredInterval x v = g.form x v v := rfl

/-- The bundle symbol channel factors through the bundle reduct. -/
theorem BundleSelfCalibratingMetric.twoMassObservation_snd_eq
    (massSq₁ massSq₂ : ℝ) (g : BundleSelfCalibratingMetric Event Fiber)
    (x : Event) (v : Fiber x) :
    (BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂ g).2 x v =
      g.calibration x * g.toBundleChronometricMetric.squaredInterval x v := rfl

/-- **Calibrating a bundle chronometric field by one.** -/
def BundleChronometricMetric.toBundleSelfCalibrating
    (g : BundleChronometricMetric Event Fiber) :
    BundleSelfCalibratingMetric Event Fiber where
  calibration := fun _ => 1
  calibration_ne_zero := fun _ => one_ne_zero
  form := g.form
  symmetric := g.symmetric

@[simp] theorem BundleChronometricMetric.toBundleChronometricMetric_toBundleSelfCalibrating
    (g : BundleChronometricMetric Event Fiber) :
    g.toBundleSelfCalibrating.toBundleChronometricMetric = g := rfl

theorem BundleChronometricMetric.toBundleSelfCalibrating_injective :
    Function.Injective
      (BundleChronometricMetric.toBundleSelfCalibrating :
        BundleChronometricMetric Event Fiber → BundleSelfCalibratingMetric Event Fiber) := by
  intro g h hgh
  have := congrArg BundleSelfCalibratingMetric.toBundleChronometricMetric hgh
  simpa using this

theorem BundleChronometricMetric.twoMassObservation_toBundleSelfCalibrating_snd
    (g : BundleChronometricMetric Event Fiber) :
    (BundleSelfCalibratingMetric.twoMassObservation 1 0 g.toBundleSelfCalibrating).2 =
      g.squaredInterval := by
  funext x v
  simp [BundleSelfCalibratingMetric.twoMassObservation,
    BundleChronometricMetric.toBundleSelfCalibrating,
    BundleChronometricMetric.squaredInterval]

/-- **Bundle chronometric identifiability is the calibration-one case of the bundle two-mass
theorem.** -/
theorem BundleChronometricMetric.squaredInterval_injective_of_twoMass :
    Function.Injective
      (BundleChronometricMetric.squaredInterval :
        BundleChronometricMetric Event Fiber → ∀ x, Fiber x → ℝ) := by
  intro g h heq
  refine BundleChronometricMetric.toBundleSelfCalibrating_injective ?_
  refine BundleSelfCalibratingMetric.twoMassObservation_injective
    (massSq₁ := (1 : ℝ)) (massSq₂ := (0 : ℝ)) (by norm_num) ?_
  refine Prod.ext ?_ ?_
  · funext x
    simp [BundleSelfCalibratingMetric.twoMassObservation,
      BundleChronometricMetric.toBundleSelfCalibrating]
  · rw [BundleChronometricMetric.twoMassObservation_toBundleSelfCalibrating_snd,
      BundleChronometricMetric.twoMassObservation_toBundleSelfCalibrating_snd, heq]

/-- **The bundle two-mass observation determines the underlying bundle chronometric field.** -/
theorem BundleSelfCalibratingMetric.toBundleChronometricMetric_eq_of_twoMassObservation_eq
    {massSq₁ massSq₂ : ℝ} (hmass : massSq₁ ≠ massSq₂)
    {g h : BundleSelfCalibratingMetric Event Fiber}
    (hdata : BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂ g =
      BundleSelfCalibratingMetric.twoMassObservation massSq₁ massSq₂ h) :
    g.toBundleChronometricMetric = h.toBundleChronometricMetric :=
  congrArg BundleSelfCalibratingMetric.toBundleChronometricMetric
    (BundleSelfCalibratingMetric.twoMassObservation_injective hmass hdata)

end Bundle

/-! ## The trivialized structures are the constant-fiber bundle structures -/

section ConstantFiber

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

/-- A trivialized chronometric field, read as a bundle field over the constant family. -/
def ChronometricMetricField.toBundle (g : ChronometricMetricField Event Tangent) :
    BundleChronometricMetric Event (fun _ : Event => Tangent) where
  form := g.form
  symmetric := g.symmetric

/-- A constant-family bundle field, read as a trivialized field. -/
def BundleChronometricMetric.ofConstant
    (g : BundleChronometricMetric Event (fun _ : Event => Tangent)) :
    ChronometricMetricField Event Tangent where
  form := g.form
  symmetric := g.symmetric

@[simp] theorem ChronometricMetricField.ofConstant_toBundle
    (g : ChronometricMetricField Event Tangent) :
    BundleChronometricMetric.ofConstant g.toBundle = g := rfl

@[simp] theorem BundleChronometricMetric.toBundle_ofConstant
    (g : BundleChronometricMetric Event (fun _ : Event => Tangent)) :
    (BundleChronometricMetric.ofConstant g).toBundle = g := rfl

/-- **The squared interval commutes with the constant-fiber identification.** -/
@[simp] theorem ChronometricMetricField.squaredInterval_toBundle
    (g : ChronometricMetricField Event Tangent) :
    g.toBundle.squaredInterval = g.squaredInterval := rfl

/-- **The trivialized identifiability theorem is the constant-fiber bundle theorem.** -/
theorem ChronometricMetricField.squaredInterval_injective_of_bundle :
    Function.Injective
      (ChronometricMetricField.squaredInterval :
        ChronometricMetricField Event Tangent → Event → Tangent → ℝ) := by
  intro g h heq
  have hbundle : g.toBundle = h.toBundle :=
    BundleChronometricMetric.squaredInterval_injective (by simpa using heq)
  simpa using congrArg BundleChronometricMetric.ofConstant hbundle

/-- **Trivialized chronometric operator rigidity, obtained from the bundle theorem.**  The
injectivity premise of the abstract graph criterion is supplied by the constant-fiber reduction. -/
theorem continuumChronometricOperatorRigidity_of_bundle {Source : Type w}
    (law₁ law₂ : ChronometricMetricField Event Tangent → Source) :
    chronometricSolutionGraph ChronometricMetricField.squaredInterval law₁ =
        chronometricSolutionGraph ChronometricMetricField.squaredInterval law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective
    ChronometricMetricField.squaredInterval_injective_of_bundle law₁ law₂

end ConstantFiber

end GaloisForLFunctions.HTGeometry
