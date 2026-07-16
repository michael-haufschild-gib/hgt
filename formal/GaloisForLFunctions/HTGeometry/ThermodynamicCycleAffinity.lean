import GaloisForLFunctions.HTGeometry.ThermodynamicAffinityFisherBound

/-!
# Additive thermodynamic cycle affinity and multiplicative clock holonomy

For a positive directed rate field, the local thermodynamic affinity is the logarithm of the
rate ratio.  Summing these values along a graph walk therefore gives the logarithm of the
multiplicative clock calibration transported along that walk.  This module proves that identity
directly and turns the group-valued Kolmogorov/Wegscheider criterion into a scalar observable:
global detailed balance is equivalent to vanishing affinity on every closed walk.

A nonzero cycle affinity is not left as a no-go.  It discharges the existing holonomy hypotheses
and exposes an edge with strictly positive entropy production and strictly positive
Fisher/pseudo-entropy current cost.  For a Gibbs population calibration, open-path affinity is
exactly the inverse-temperature weighted endpoint energy gap and every closed affinity vanishes.

These are static values on an observation graph, not temporal evolution laws.

Physics and chemistry provenance: cycle affinities are the global thermodynamic forces of
Schnakenberg network thermodynamics and chemical reaction networks; see Schmiedl--Seifert,
arXiv:cond-mat/0605080, Polettini--Esposito, arXiv:1404.1181, and
Polettini--Falasco--Esposito, arXiv:2106.00425.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Additive thermodynamic affinity accumulated along an observable graph walk. -/
def thermodynamicWalkAffinity {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) : {u w : V} → G.Walk u w → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p =>
      thermodynamicAffinity (rate u v) (rate v u) +
        thermodynamicWalkAffinity rate p

@[simp] theorem thermodynamicWalkAffinity_nil {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (u : V) :
    thermodynamicWalkAffinity rate (SimpleGraph.Walk.nil : G.Walk u u) = 0 := rfl

@[simp] theorem thermodynamicWalkAffinity_cons {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    thermodynamicWalkAffinity rate (.cons h p) =
      thermodynamicAffinity (rate u v) (rate v u) +
        thermodynamicWalkAffinity rate p := rfl

/-- Walk affinity is additive under path concatenation. -/
theorem thermodynamicWalkAffinity_append {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    thermodynamicWalkAffinity rate (p.append q) =
      thermodynamicWalkAffinity rate p + thermodynamicWalkAffinity rate q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

/-- Exponentiating the additive walk affinity gives exactly the multiplicative rate-ratio clock
transport. -/
theorem exp_thermodynamicWalkAffinity_eq_clockWalkTransport_val
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u w : V} (p : G.Walk u w) :
    Real.exp (thermodynamicWalkAffinity rate p) =
      ((clockWalkTransport
        (rateRatioCalibration rate (fun a b => (hrate a b).ne')) p : ℝˣ) : ℝ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      rw [thermodynamicWalkAffinity_cons, Real.exp_add, ih,
        clockWalkTransport_cons]
      congr 1
      rw [thermodynamicAffinity, Real.exp_log (div_pos (hrate u v) (hrate v u))]
      simp [rateRatioCalibration]

/-- **Cycle affinity/holonomy identity.**  The scalar walk affinity is the logarithm of the
positive multiplicative clock holonomy. -/
theorem thermodynamicWalkAffinity_eq_log_clockWalkTransport
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u w : V} (p : G.Walk u w) :
    thermodynamicWalkAffinity rate p =
      Real.log
        (((clockWalkTransport
          (rateRatioCalibration rate (fun a b => (hrate a b).ne')) p : ℝˣ) : ℝ)) := by
  rw [← exp_thermodynamicWalkAffinity_eq_clockWalkTransport_val rate hrate p]
  exact (Real.log_exp _).symm

/-- Vanishing scalar walk affinity is exactly unit multiplicative rate-ratio holonomy. -/
theorem thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u w : V} (p : G.Walk u w) :
    thermodynamicWalkAffinity rate p = 0 ↔
      clockWalkTransport
        (rateRatioCalibration rate (fun a b => (hrate a b).ne')) p = 1 := by
  constructor
  · intro hzero
    apply Units.ext
    have hexp := exp_thermodynamicWalkAffinity_eq_clockWalkTransport_val rate hrate p
    rw [hzero] at hexp
    simpa using hexp.symm
  · intro hone
    have hlog := thermodynamicWalkAffinity_eq_log_clockWalkTransport rate hrate p
    rw [hone] at hlog
    simpa using hlog

/-- **Scalar Wegscheider criterion.**  On a connected observable graph, a positive rate field has
one global detailed-balance potential exactly when every closed-walk affinity vanishes. -/
theorem rateRatioCalibration_exact_iff_closedWalkAffinity_zero
    {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w) :
    ClockCalibrationExact G
        (rateRatioCalibration rate (fun a b => (hrate a b).ne')) ↔
      ∀ (u : V) (p : G.Walk u u), thermodynamicWalkAffinity rate p = 0 := by
  rw [rateRatioCalibration_exact_iff_flat hG rate
    (fun a b => (hrate a b).ne')]
  constructor
  · intro hflat u p
    exact (thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one
      rate hrate p).2 (hflat u p)
  · intro hall u p
    exact (thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one
      rate hrate p).1 (hall u p)

/-- A rate field induced by one positive vertex population has walk affinity equal to the
endpoint population affinity. -/
theorem thermodynamicWalkAffinity_vertexPopulation
    {V : Type*} {G : SimpleGraph V}
    (population : V → ℝ) (hpopulation : ∀ u, 0 < population u)
    {u w : V} (p : G.Walk u w) :
    thermodynamicWalkAffinity (fun a _ => population a) p =
      thermodynamicAffinity (population u) (population w) := by
  induction p with
  | nil => simp [thermodynamicAffinity]
  | @cons u v w h p ih =>
      rw [thermodynamicWalkAffinity_cons, ih,
        thermodynamicAffinity_compose (hpopulation u) (hpopulation v) (hpopulation w)]

/-- Along a finite Gibbs population calibration, walk affinity is exactly the
inverse-temperature weighted endpoint energy gap. -/
theorem thermodynamicWalkAffinity_finiteGibbsStateWeight
    {α : Type*} [Fintype α] {G : SimpleGraph α}
    (β : ℝ) (energy : α → ℝ) {a b : α} (p : G.Walk a b) :
    thermodynamicWalkAffinity
        (fun u _ => _root_.HTGeometry.finiteGibbsStateWeight β energy u) p =
      -β * (energy a - energy b) := by
  letI : Nonempty α := ⟨a⟩
  rw [thermodynamicWalkAffinity_vertexPopulation
    (fun u => _root_.HTGeometry.finiteGibbsStateWeight β energy u)
    (fun u => _root_.HTGeometry.finiteGibbsStateWeight_pos β energy u) p]
  rw [thermodynamicAffinity_finiteGibbsStateWeight β energy b a]
  ring

/-- Every closed Gibbs population clock has zero scalar cycle affinity. -/
theorem thermodynamicWalkAffinity_finiteGibbsStateWeight_closed
    {α : Type*} [Fintype α] {G : SimpleGraph α}
    (β : ℝ) (energy : α → ℝ) {a : α} (p : G.Walk a a) :
    thermodynamicWalkAffinity
        (fun u _ => _root_.HTGeometry.finiteGibbsStateWeight β energy u) p = 0 := by
  rw [thermodynamicWalkAffinity_finiteGibbsStateWeight]
  ring

/-- A nonzero scalar cycle affinity exposes a positive edgewise entropy-production value. -/
theorem exists_adjacent_entropyProductionValue_pos_of_walkAffinity_ne_zero
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u : V} (p : G.Walk u u)
    (haffinity : thermodynamicWalkAffinity rate p ≠ 0) :
    ∃ a b, s(a, b) ∈ p.edges ∧
      0 < entropyProductionValue (rate a b) (rate b a) := by
  apply exists_adjacent_entropyProductionValue_pos_of_nontrivial_holonomy rate hrate p
  intro hunit
  exact haffinity
    ((thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one
      rate hrate p).2 hunit)

/-- A nonzero scalar cycle affinity also exposes a positive Fisher/pseudo-entropy current cost. -/
theorem exists_adjacent_pseudoEntropyProductionValue_pos_of_walkAffinity_ne_zero
    {V : Type*} {G : SimpleGraph V}
    (rate : V → V → ℝ) (hrate : ∀ u w, 0 < rate u w)
    {u : V} (p : G.Walk u u)
    (haffinity : thermodynamicWalkAffinity rate p ≠ 0) :
    ∃ a b, s(a, b) ∈ p.edges ∧
      0 < pseudoEntropyProductionValue (rate a b) (rate b a) := by
  apply exists_adjacent_pseudoEntropyProductionValue_pos_of_nontrivial_holonomy rate hrate p
  intro hunit
  exact haffinity
    ((thermodynamicWalkAffinity_eq_zero_iff_clockWalkTransport_eq_one
      rate hrate p).2 hunit)

end

end GaloisForLFunctions.HTGeometry
