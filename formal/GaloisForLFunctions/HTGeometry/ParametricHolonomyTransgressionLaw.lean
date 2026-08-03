import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy

/-!
# Parametric holonomy transgression

A parameter can occur in every open edge value while remaining absent from
all closed observations.  The invariant which distinguishes genuine motion
of a connection from such endpoint recalibration is the relative holonomy of
two parameter slices.

For commutative group-valued transport on a connected graph, two reversible
edge fields are related by an endpoint gauge exactly when every relative
closed holonomy is trivial.  Thus a parameter moves the gauge-equivalence
class precisely when some closed relative holonomy is nontrivial.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {V : Type u} {A : Type v}

/-- Pointwise quotient of two edge transports. -/
def clockCalibrationRelative [Group A]
    (c d : V → V → A) : V → V → A :=
  fun x y => c x y * (d x y)⁻¹

/-- Relative closed holonomy of two parameter slices. -/
def clockClosedHolonomyTransgression {G : SimpleGraph V} [Group A]
    (c d : V → V → A) (x : V) (p : G.Walk x x) : A :=
  clockWalkTransport c p * (clockWalkTransport d p)⁻¹

/-- Gauge equivalence restricted to the observable edges of a graph. -/
def ClockCalibrationGaugeEquivalentOn (G : SimpleGraph V) [Group A]
    (c d : V → V → A) : Prop :=
  ∃ g : V → A, ∀ {x y}, G.Adj x y →
    c x y = clockCalibrationGauge g d x y

/-- Walk transport depends only on edge values along the observable graph. -/
theorem clockWalkTransport_congr_on_edges {G : SimpleGraph V} [Monoid A]
    {c d : V → V → A}
    (h : ∀ {x y}, G.Adj x y → c x y = d x y)
    {x y : V} (p : G.Walk x y) :
    clockWalkTransport c p = clockWalkTransport d p := by
  induction p with
  | nil => rfl
  | cons hxy p ih =>
      rw [clockWalkTransport_cons, clockWalkTransport_cons, h hxy, ih]

/-- Transport of the relative edge field is relative transport. -/
theorem clockWalkTransport_relative {G : SimpleGraph V} [CommGroup A]
    (c d : V → V → A) {x y : V} (p : G.Walk x y) :
    clockWalkTransport (clockCalibrationRelative c d) p =
      clockWalkTransport c p * (clockWalkTransport d p)⁻¹ := by
  induction p with
  | nil => simp
  | cons hxy p ih =>
      simp only [clockWalkTransport_cons, clockCalibrationRelative, ih, mul_inv_rev]
      simp only [mul_comm, mul_left_comm, mul_assoc]

/-- Relative transport of reversible commutative edge fields is reversible. -/
theorem clockCalibrationRelative_reversible {G : SimpleGraph V} [CommGroup A]
    {c d : V → V → A}
    (hc : ClockCalibrationReversible G c)
    (hd : ClockCalibrationReversible G d) :
    ClockCalibrationReversible G (clockCalibrationRelative c d) := by
  intro x y hxy
  rw [clockCalibrationRelative, clockCalibrationRelative, hc hxy, hd hxy]
  simp only [inv_inv, mul_inv_rev]
  ac_rfl

/-- Relative holonomy is trivial when the two slices agree. -/
@[simp] theorem clockClosedHolonomyTransgression_self
    {G : SimpleGraph V} [Group A]
    (c : V → V → A) (x : V) (p : G.Walk x x) :
    clockClosedHolonomyTransgression c c x p = 1 := by
  simp [clockClosedHolonomyTransgression]

/-- Relative holonomies compose across three parameter slices. -/
theorem clockClosedHolonomyTransgression_cocycle
    {G : SimpleGraph V} [CommGroup A]
    (c d e : V → V → A) (x : V) (p : G.Walk x x) :
    clockClosedHolonomyTransgression c e x p =
      clockClosedHolonomyTransgression c d x p *
        clockClosedHolonomyTransgression d e x p := by
  simp only [clockClosedHolonomyTransgression]
  group

/-- Endpoint gauges at either parameter slice do not change relative closed holonomy. -/
theorem clockClosedHolonomyTransgression_gauge_invariant
    {G : SimpleGraph V} [CommGroup A]
    (gc gd : V → A) (c d : V → V → A)
    (x : V) (p : G.Walk x x) :
    clockClosedHolonomyTransgression
        (clockCalibrationGauge gc c) (clockCalibrationGauge gd d) x p =
      clockClosedHolonomyTransgression c d x p := by
  rw [clockClosedHolonomyTransgression, clockClosedHolonomyTransgression,
    clockClosedHolonomy_gauge_invariant, clockClosedHolonomy_gauge_invariant]

/-- **Parametric holonomy-transgression classification.**  On a connected graph, two reversible
commutative edge fields represent the same gauge class exactly when every relative closed
holonomy is trivial. -/
theorem clockCalibrationGaugeEquivalentOn_iff_transgression_eq_one
    {G : SimpleGraph V} [CommGroup A]
    (hG : G.Connected) (c d : V → V → A)
    (hc : ClockCalibrationReversible G c)
    (hd : ClockCalibrationReversible G d) :
    ClockCalibrationGaugeEquivalentOn G c d ↔
      ∀ (x : V) (p : G.Walk x x),
        clockClosedHolonomyTransgression c d x p = 1 := by
  constructor
  · rintro ⟨g, hg⟩ x p
    have hp : clockWalkTransport c p =
        clockWalkTransport (clockCalibrationGauge g d) p :=
      clockWalkTransport_congr_on_edges hg p
    rw [clockClosedHolonomyTransgression, hp,
      clockClosedHolonomy_gauge_invariant]
    simp
  · intro htrans
    have hrelRev : ClockCalibrationReversible G (clockCalibrationRelative c d) :=
      clockCalibrationRelative_reversible hc hd
    have hrelFlat : ClockCalibrationFlat G (clockCalibrationRelative c d) := by
      intro x p
      rw [clockWalkTransport_relative]
      exact htrans x p
    obtain ⟨g, hg⟩ := clockCalibrationExact_of_flat hG
      (clockCalibrationRelative c d) hrelRev hrelFlat
    refine ⟨g, ?_⟩
    intro x y hxy
    have hxyRel := hg hxy
    rw [clockCalibrationGauge]
    calc
      c x y = clockCalibrationRelative c d x y * d x y := by
        rw [clockCalibrationRelative]
        group
      _ = ((g x)⁻¹ * g y) * d x y := by rw [hxyRel]
      _ = (g x)⁻¹ * d x y * g y := by ac_rfl

/-- A nontrivial relative closed holonomy certifies genuine parameter motion in the moduli of
connections: no endpoint recalibration relates the two slices. -/
theorem not_clockCalibrationGaugeEquivalentOn_of_transgression_ne_one
    {G : SimpleGraph V} [CommGroup A]
    (hG : G.Connected) (c d : V → V → A)
    (hc : ClockCalibrationReversible G c)
    (hd : ClockCalibrationReversible G d)
    {x : V} (p : G.Walk x x)
    (htrans : clockClosedHolonomyTransgression c d x p ≠ 1) :
    ¬ ClockCalibrationGaugeEquivalentOn G c d := by
  rw [clockCalibrationGaugeEquivalentOn_iff_transgression_eq_one hG c d hc hd]
  intro h
  exact htrans (h x p)

end GaloisForLFunctions.HTGeometry
