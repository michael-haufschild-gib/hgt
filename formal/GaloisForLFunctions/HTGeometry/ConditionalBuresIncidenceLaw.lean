import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw

/-!
# Conditional and bundle Bures incidence laws

The target geometry may vary with a context only after conditioning makes it
fixed inside each residual source fibre.  This module integrates the exact
occupied-body Bures law fibrewise and records the disintegration corollaries,
including return removal with one global return charge.
-/

open MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fibrewise `BIM` integrated over a context law. -/
theorem occupiedTargetBures_conditionalIncidence_integral_bound
    {Y X C : Type*} [MeasurableSpace Y] [MeasurableSpace X] [Nonempty C]
    {n : ℕ}
    (nu : Measure Y) (mu : Y → Measure X)
    [∀ y, IsFiniteMeasure (mu y)]
    (target : Y → C → Fin n → ℂ) (state : Y → X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hTargetCompact : ∀ y, IsCompact (Set.range (target y)))
    (hprod : ∀ y i j, Integrable
      (fun x => state y x i * star (state y x j)) (mu y))
    (hEventIntegrable : Integrable
      (fun y => threshold *
        (mu y).real
          (finitePositiveReporterCaptureEvent
            (target y) (state y) threshold)) nu)
    (hCapacityIntegrable : Integrable
      (fun y => compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance (mu y) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ)) nu) :
    (∫ y, threshold *
        (mu y).real
          (finitePositiveReporterCaptureEvent
            (target y) (state y) threshold) ∂nu) ≤
      ∫ y, compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance (mu y) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) ∂nu := by
  apply integral_mono hEventIntegrable hCapacityIntegrable
  intro y
  exact occupiedTargetBures_completeIncidence_minimax_bound
    (mu y) (target y) (state y) threshold hthreshold
      (hTargetCompact y) (hprod y)

/-- `BIM-C` in disintegrated global-mass form.  The equality premise is the
defining event-mass property supplied by an honest disintegration. -/
theorem occupiedTargetBures_conditionalIncidence_global_bound
    {Y X C : Type*} [MeasurableSpace Y] [MeasurableSpace X] [Nonempty C]
    {n : ℕ}
    (nu : Measure Y) (mu : Y → Measure X)
    [∀ y, IsFiniteMeasure (mu y)]
    (target : Y → C → Fin n → ℂ) (state : Y → X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (globalEventMass : ℝ)
    (hdisintegrate : globalEventMass =
      ∫ y, (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold) ∂nu)
    (hTargetCompact : ∀ y, IsCompact (Set.range (target y)))
    (hprod : ∀ y i j, Integrable
      (fun x => state y x i * star (state y x j)) (mu y))
    (hEventIntegrable : Integrable
      (fun y => (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold)) nu)
    (hCapacityIntegrable : Integrable
      (fun y => compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance (mu y) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ)) nu) :
    threshold * globalEventMass ≤
      ∫ y, compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance (mu y) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) ∂nu := by
  rw [hdisintegrate, ← integral_const_mul]
  exact occupiedTargetBures_conditionalIncidence_integral_bound
    nu mu target state threshold hthreshold hTargetCompact hprod
      (hEventIntegrable.const_mul threshold) hCapacityIntegrable

/-- Return-excised conditional Bures law.  Each fibre is restricted before
forming its covariance; after integration, return mass appears once. -/
theorem occupiedTargetBures_conditionalReturnExcised_integral_bound
    {Y X C : Type*} [MeasurableSpace Y] [MeasurableSpace X] [Nonempty C]
    {n : ℕ}
    (nu : Measure Y) (mu : Y → Measure X)
    [∀ y, IsFiniteMeasure (mu y)]
    (target : Y → C → Fin n → ℂ) (state : Y → X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Y → Set X) (hreturn : ∀ y, MeasurableSet (returnSet y))
    (hTargetCompact : ∀ y, IsCompact (Set.range (target y)))
    (hprod : ∀ y i j, Integrable
      (fun x => state y x i * star (state y x j))
        ((mu y).restrict (returnSet y)ᶜ))
    (hEventIntegrable : Integrable
      (fun y => (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold)) nu)
    (hReturnIntegrable : Integrable
      (fun y => (mu y).real (returnSet y)) nu)
    (hCapacityIntegrable : Integrable
      (fun y => compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance
          ((mu y).restrict (returnSet y)ᶜ) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) /
          threshold) nu) :
    (∫ y, (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold) ∂nu) ≤
      (∫ y, (mu y).real (returnSet y) ∂nu) +
        ∫ y, compactBuresDualCapacity
          (finitePositiveReporterSourceCovariance
            ((mu y).restrict (returnSet y)ᶜ) (state y))
          (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) /
            threshold ∂nu := by
  let cap : Y → ℝ := fun y => compactBuresDualCapacity
    (finitePositiveReporterSourceCovariance
      ((mu y).restrict (returnSet y)ᶜ) (state y))
    (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) / threshold
  have hsum : Integrable (fun y => (mu y).real (returnSet y) + cap y) nu :=
    hReturnIntegrable.add (by simpa [cap] using hCapacityIntegrable)
  calc
    (∫ y, (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold) ∂nu) ≤
        ∫ y, (mu y).real (returnSet y) + cap y ∂nu := by
      apply integral_mono hEventIntegrable hsum
      intro y
      simpa [cap] using
        occupiedTargetBures_returnExcisedIncidence_minimax_bound
          (mu y) (target y) (state y) threshold hthreshold
            (returnSet y) (hreturn y) (hTargetCompact y) (hprod y)
    _ = (∫ y, (mu y).real (returnSet y) ∂nu) + ∫ y, cap y ∂nu :=
      integral_add hReturnIntegrable (by simpa [cap] using hCapacityIntegrable)
    _ = _ := by rfl

/-- Global return-excised `BIM-C` after the two disintegration identities
for capture and return mass are supplied. -/
theorem occupiedTargetBures_conditionalReturnExcised_global_bound
    {Y X C : Type*} [MeasurableSpace Y] [MeasurableSpace X] [Nonempty C]
    {n : ℕ}
    (nu : Measure Y) (mu : Y → Measure X)
    [∀ y, IsFiniteMeasure (mu y)]
    (target : Y → C → Fin n → ℂ) (state : Y → X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Y → Set X) (hreturn : ∀ y, MeasurableSet (returnSet y))
    (globalEventMass globalReturnMass : ℝ)
    (hEventDisintegrate : globalEventMass =
      ∫ y, (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold) ∂nu)
    (hReturnDisintegrate : globalReturnMass =
      ∫ y, (mu y).real (returnSet y) ∂nu)
    (hTargetCompact : ∀ y, IsCompact (Set.range (target y)))
    (hprod : ∀ y i j, Integrable
      (fun x => state y x i * star (state y x j))
        ((mu y).restrict (returnSet y)ᶜ))
    (hEventIntegrable : Integrable
      (fun y => (mu y).real
        (finitePositiveReporterCaptureEvent
          (target y) (state y) threshold)) nu)
    (hReturnIntegrable : Integrable
      (fun y => (mu y).real (returnSet y)) nu)
    (hCapacityIntegrable : Integrable
      (fun y => compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance
          ((mu y).restrict (returnSet y)ᶜ) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) /
          threshold) nu) :
    globalEventMass ≤ globalReturnMass +
      ∫ y, compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance
          ((mu y).restrict (returnSet y)ᶜ) (state y))
        (finiteBuresOccupiedTargetBody (Set.range (target y))) ^ (2 : ℕ) /
          threshold ∂nu := by
  rw [hEventDisintegrate, hReturnDisintegrate]
  exact occupiedTargetBures_conditionalReturnExcised_integral_bound
    nu mu target state threshold hthreshold returnSet hreturn
      hTargetCompact hprod hEventIntegrable hReturnIntegrable hCapacityIntegrable

/-- **Ordinary static-local ensemble form (`SL-BIM`).**  Conditioning is
only by the seed/context, so the occupied shallow target image is fixed while
all Hamiltonian randomness remains inside the conditional covariance. -/
theorem ordinaryStaticLocalBures_returnExcised_bound
    {Seed Hamiltonian Circuit : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Hamiltonian] [Nonempty Circuit]
    {n r : ℕ}
    (seedLaw : Measure Seed) (hamiltonianLaw : Seed → Measure Hamiltonian)
    [∀ chi, IsFiniteMeasure (hamiltonianLaw chi)]
    (shallowTarget : Seed → Circuit → Fin n → ℂ)
    (replicaSource : Seed → Hamiltonian → Fin n → ℂ)
    (a : ℝ) (ha : 0 < a)
    (returnSet : Seed → Set Hamiltonian)
    (hreturn : ∀ chi, MeasurableSet (returnSet chi))
    (globalShortcutMass globalReturnMass : ℝ)
    (hShortcutDisintegrate : globalShortcutMass =
      ∫ chi, (hamiltonianLaw chi).real
        (finitePositiveReporterCaptureEvent
          (shallowTarget chi) (replicaSource chi) (a ^ r)) ∂seedLaw)
    (hReturnDisintegrate : globalReturnMass =
      ∫ chi, (hamiltonianLaw chi).real (returnSet chi) ∂seedLaw)
    (hTargetCompact : ∀ chi, IsCompact (Set.range (shallowTarget chi)))
    (hprod : ∀ chi i j, Integrable
      (fun H => replicaSource chi H i * star (replicaSource chi H j))
        ((hamiltonianLaw chi).restrict (returnSet chi)ᶜ))
    (hEventIntegrable : Integrable
      (fun chi => (hamiltonianLaw chi).real
        (finitePositiveReporterCaptureEvent
          (shallowTarget chi) (replicaSource chi) (a ^ r))) seedLaw)
    (hReturnIntegrable : Integrable
      (fun chi => (hamiltonianLaw chi).real (returnSet chi)) seedLaw)
    (hCapacityIntegrable : Integrable
      (fun chi => compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance
          ((hamiltonianLaw chi).restrict (returnSet chi)ᶜ)
          (replicaSource chi))
        (finiteBuresOccupiedTargetBody (Set.range (shallowTarget chi))) ^ (2 : ℕ) /
          a ^ r) seedLaw) :
    globalShortcutMass ≤ globalReturnMass +
      ∫ chi, compactBuresDualCapacity
        (finitePositiveReporterSourceCovariance
          ((hamiltonianLaw chi).restrict (returnSet chi)ᶜ)
          (replicaSource chi))
        (finiteBuresOccupiedTargetBody (Set.range (shallowTarget chi))) ^ (2 : ℕ) /
          a ^ r ∂seedLaw := by
  exact occupiedTargetBures_conditionalReturnExcised_global_bound
    seedLaw hamiltonianLaw shallowTarget replicaSource (a ^ r) (pow_pos ha r)
      returnSet hreturn globalShortcutMass globalReturnMass
      hShortcutDisintegrate hReturnDisintegrate hTargetCompact hprod
      hEventIntegrable hReturnIntegrable hCapacityIntegrable

end

end GaloisForLFunctions.HTGeometry
