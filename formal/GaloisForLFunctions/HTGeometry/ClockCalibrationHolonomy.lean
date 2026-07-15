import Mathlib

/-!
# Gauge-covariant clock calibration holonomy

This module isolates the static algebra of Weyl-style clock calibration. Edge values compare
clock standards; their ordered product along a walk is observable transport. A change of local
standards acts only at the endpoints, so closed-loop holonomy is gauge invariant in an abelian
calibration group. On a connected graph, trivial holonomy on every closed walk is equivalent to
the existence of one global calibration potential.

No walk parameter is interpreted as time and no evolution law is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v
variable {V : Type u} {A : Type v}

/-- Ordered multiplicative clock-calibration transport along a finite graph walk. -/
def clockWalkTransport {G : SimpleGraph V} [One A] [Mul A] (c : V → V → A) :
    {u w : V} → G.Walk u w → A
  | _, _, .nil => 1
  | u, _, .cons (v := v) _ p => c u v * clockWalkTransport c p

@[simp] theorem clockWalkTransport_nil {G : SimpleGraph V} [One A] [Mul A]
    (c : V → V → A) (u : V) :
    clockWalkTransport c (SimpleGraph.Walk.nil : G.Walk u u) = 1 := rfl

@[simp] theorem clockWalkTransport_cons {G : SimpleGraph V} [One A] [Mul A]
    (c : V → V → A) {u w x : V} (h : G.Adj u w) (p : G.Walk w x) :
    clockWalkTransport c (.cons h p) = c u w * clockWalkTransport c p := rfl

theorem clockWalkTransport_append {G : SimpleGraph V} [Monoid A]
    (c : V → V → A) {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    clockWalkTransport c (p.append q) =
      clockWalkTransport c p * clockWalkTransport c q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, mul_assoc]

/-- Reversing an edge inverts its clock-calibration value. -/
def ClockCalibrationReversible (G : SimpleGraph V) [Inv A] (c : V → V → A) : Prop :=
  ∀ {u w}, G.Adj u w → c w u = (c u w)⁻¹

theorem clockWalkTransport_reverse {G : SimpleGraph V} [Group A]
    (c : V → V → A) (hc : ClockCalibrationReversible G c)
    {u w : V} (p : G.Walk u w) :
    clockWalkTransport c p.reverse = (clockWalkTransport c p)⁻¹ := by
  induction p with
  | nil => simp
  | @cons u w x h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, clockWalkTransport_append, ih]
      simp only [clockWalkTransport_cons, clockWalkTransport_nil, mul_one]
      rw [hc h]
      exact (mul_inv_rev _ _).symm

/-- Change of local clock standards. -/
def clockCalibrationGauge [Group A] (g : V → A) (c : V → V → A) : V → V → A :=
  fun u w => (g u)⁻¹ * c u w * g w

/-- Open-path transport changes only by the standards at its two endpoints. -/
theorem clockWalkTransport_gauge {G : SimpleGraph V} [Group A]
    (g : V → A) (c : V → V → A) {u w : V} (p : G.Walk u w) :
    clockWalkTransport (clockCalibrationGauge g c) p =
      (g u)⁻¹ * clockWalkTransport c p * g w := by
  induction p with
  | nil => simp
  | @cons u w x h p ih =>
      rw [clockWalkTransport_cons, clockWalkTransport_cons, ih]
      simp only [clockCalibrationGauge]
      group

/-- In an abelian calibration group, every closed-loop reading is independent of local standards. -/
theorem clockClosedHolonomy_gauge_invariant {G : SimpleGraph V} [CommGroup A]
    (g : V → A) (c : V → V → A) (u : V) (p : G.Walk u u) :
    clockWalkTransport (clockCalibrationGauge g c) p = clockWalkTransport c p := by
  rw [clockWalkTransport_gauge]
  simp [mul_comm]

/-- A calibration field is flat when every closed walk has unit clock holonomy. -/
def ClockCalibrationFlat (G : SimpleGraph V) [Monoid A] (c : V → V → A) : Prop :=
  ∀ (u : V) (p : G.Walk u u), clockWalkTransport c p = 1

/-- A global clock potential produces the endpoint ratio on every edge. -/
def ClockCalibrationExact (G : SimpleGraph V) [Group A] (c : V → V → A) : Prop :=
  ∃ g : V → A, ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w

/-- The clock calibration induced by one group-valued scalar field. -/
def clockRatioCalibration [Group A] (g : V → A) : V → V → A :=
  fun u w => (g u)⁻¹ * g w

/-- A scalar-induced calibration is exact on every observable graph. -/
theorem clockRatioCalibration_exact {G : SimpleGraph V} [Group A] (g : V → A) :
    ClockCalibrationExact G (clockRatioCalibration g) := by
  exact ⟨g, fun _ => rfl⟩

/-- Exact calibration telescopes to the endpoint ratio along every walk. -/
theorem clockWalkTransport_of_exact {G : SimpleGraph V} [Group A]
    (c : V → V → A) (g : V → A)
    (hc : ∀ {u w}, G.Adj u w → c u w = (g u)⁻¹ * g w)
    {u w : V} (p : G.Walk u w) :
    clockWalkTransport c p = (g u)⁻¹ * g w := by
  induction p with
  | nil => simp
  | @cons u w x h p ih =>
      rw [clockWalkTransport_cons, hc h, ih]
      group

/-- Every global calibration has no second-clock holonomy. -/
theorem clockCalibrationFlat_of_exact {G : SimpleGraph V} [Group A]
    (c : V → V → A) (h : ClockCalibrationExact G c) :
    ClockCalibrationFlat G c := by
  rcases h with ⟨g, hg⟩
  intro u p
  rw [clockWalkTransport_of_exact c g hg p]
  simp

/-- Scalar clock ratios telescope to the endpoint ratio, independently of the chosen walk. -/
theorem clockWalkTransport_ratio {G : SimpleGraph V} [Group A]
    (g : V → A) {u w : V} (p : G.Walk u w) :
    clockWalkTransport (clockRatioCalibration g) p = (g u)⁻¹ * g w :=
  clockWalkTransport_of_exact (clockRatioCalibration g) g (fun _ => rfl) p

/-- Every scalar-induced calibration has trivial loop holonomy. -/
theorem clockRatioCalibration_flat {G : SimpleGraph V} [Group A] (g : V → A) :
    ClockCalibrationFlat G (clockRatioCalibration g) :=
  clockCalibrationFlat_of_exact _ (clockRatioCalibration_exact g)

/-- On a connected graph, reversible flat clock transport reconstructs one global calibration. -/
theorem clockCalibrationExact_of_flat {G : SimpleGraph V} [Group A]
    (hG : G.Connected) (c : V → V → A)
    (hrev : ClockCalibrationReversible G c)
    (hflat : ClockCalibrationFlat G c) :
    ClockCalibrationExact G c := by
  classical
  let root : V := Classical.choice hG.nonempty
  let path : ∀ w : V, G.Walk root w := fun w => Classical.choice (hG root w)
  let g : V → A := fun w => clockWalkTransport c (path w)
  refine ⟨g, ?_⟩
  intro u w huw
  let closed : G.Walk root root :=
    (path u).append (huw.toWalk.append (path w).reverse)
  have hclosed := hflat root closed
  rw [clockWalkTransport_append, clockWalkTransport_append,
    clockWalkTransport_reverse c hrev] at hclosed
  simp only [clockWalkTransport_cons, clockWalkTransport_nil, mul_one] at hclosed
  change g u * (c u w * (g w)⁻¹) = 1 at hclosed
  have htransport : g u * c u w = g w := by
    calc
      g u * c u w = (g u * (c u w * (g w)⁻¹)) * g w := by group
      _ = 1 * g w := by rw [hclosed]
      _ = g w := one_mul _
  calc
    c u w = (g u)⁻¹ * (g u * c u w) := by group
    _ = (g u)⁻¹ * g w := by rw [htransport]

/-- **Static clock-integrability criterion.** For reversible calibration on a connected
observable graph, vanishing of every loop reading is equivalent to one global clock standard. -/
theorem clockCalibrationExact_iff_flat {G : SimpleGraph V} [Group A]
    (hG : G.Connected) (c : V → V → A)
    (hrev : ClockCalibrationReversible G c) :
    ClockCalibrationExact G c ↔ ClockCalibrationFlat G c := by
  constructor
  · exact clockCalibrationFlat_of_exact c
  · exact clockCalibrationExact_of_flat hG c hrev

/-- A nonunit loop reading is a positive obstruction: no global scalar calibration can produce
the edge field. -/
theorem not_clockCalibrationExact_of_nontrivial_holonomy
    {G : SimpleGraph V} [Group A] (c : V → V → A)
    {u : V} (p : G.Walk u u) (hp : clockWalkTransport c p ≠ 1) :
    ¬ ClockCalibrationExact G c := by
  intro hexact
  exact hp ((clockCalibrationFlat_of_exact c hexact) u p)

/-- Gauge changes preserve flatness even for a nonabelian calibration group: closed holonomy is
conjugated, and conjugation preserves the unit. -/
theorem clockCalibrationFlat_gauge {G : SimpleGraph V} [Group A]
    (g : V → A) (c : V → V → A) (hflat : ClockCalibrationFlat G c) :
    ClockCalibrationFlat G (clockCalibrationGauge g c) := by
  intro u p
  rw [clockWalkTransport_gauge, hflat u p]
  group

end GaloisForLFunctions.HTGeometry
