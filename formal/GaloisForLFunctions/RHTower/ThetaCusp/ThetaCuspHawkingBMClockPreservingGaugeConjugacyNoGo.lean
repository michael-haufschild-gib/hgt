import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFESourceFixedGaugeTrivializationRigidity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity

/-!
# Clock-preserving gauge conjugacy cannot produce the HB covariance

The hardest surviving HB receiver asks literal anti-linear source-FE transport to commute with one
source-predeclared nonzero centered-QNM physical clock step. This module classifies the full
coordinate-normalization escape. Conjugating source-FE transport by any invertible packet map that
preserves the fixed physical clock preserves and reflects its covariance law. No linearity,
topology, norm, or basis hypothesis is needed.

Every nowhere-zero diagonal packet gauge is an instance. Consequently the explicit Hilbert-90
source-amplitude gauge gives the sharp separation: it trivializes the FE cocycle globally, making
transport pure reflection and conjugation, but its unit-clock covariance is still equivalent to RH.
The FE cocycle is gauge-trivial; the physical clock defect is not.

This kills all clock-preserving gauge, basis-normalization, and cocycle-trivialization proposals as
producers of the remaining HB identity. A survivor must change the physical clock, mix its
eigenspaces through non-clock-preserving dynamics, or derive covariance from the literal
Einstein--Teukolsky source.

`[NEW] [HB NO-GO] [CLOCK GAUGE] [HILBERT 90] [EXACT RH ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- An invertible packet-coordinate gauge preserving one fixed physical clock step. -/
structure HBXiPeierlsClockPreservingGauge (n : ℕ) (t : ℝ) where
  forward : HBXiPeierlsPacket → HBXiPeierlsPacket
  backward : HBXiPeierlsPacket → HBXiPeierlsPacket
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x
  forward_clock : ∀ x,
    forward (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t (forward x)

/-- The inverse of a clock-preserving gauge also preserves the same clock. -/
theorem HBXiPeierlsClockPreservingGauge.backward_clock
    {n : ℕ} {t : ℝ} (g : HBXiPeierlsClockPreservingGauge n t)
    (x : HBXiPeierlsPacket) :
    g.backward (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t (g.backward x) := by
  calc
    g.backward (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
        g.backward (hbXiPeierlsCenteredQNMPhysicalClockStep n t
          (g.forward (g.backward x))) := by rw [g.forward_backward]
    _ = g.backward (g.forward
          (hbXiPeierlsCenteredQNMPhysicalClockStep n t (g.backward x))) := by
      rw [g.forward_clock]
    _ = hbXiPeierlsCenteredQNMPhysicalClockStep n t (g.backward x) :=
      g.backward_forward _

/-- Literal source-FE transport conjugated by a clock-preserving packet gauge. -/
def hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport
    {n : ℕ} {t : ℝ} (g : HBXiPeierlsClockPreservingGauge n t)
    (x : HBXiPeierlsPacket) : HBXiPeierlsPacket :=
  g.backward (hbXiPeierlsUnitSourceFEPacketTransport (g.forward x))

/-- Covariance of gauge-conjugated source-FE transport with the same physical clock. -/
def HBXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
    {n : ℕ} {t : ℝ} (g : HBXiPeierlsClockPreservingGauge n t) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport g
        (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t
        (hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport g x)

/-- Clock covariance is invariant under every invertible clock-preserving packet gauge. -/
theorem hbXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff
    {n : ℕ} {t : ℝ} (g : HBXiPeierlsClockPreservingGauge n t) :
    HBXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant g ↔
      HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant n t := by
  constructor
  · intro hg x
    have h := congrArg g.forward (hg (g.backward x))
    simpa [HBXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant,
      hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport,
      g.forward_clock, g.forward_backward] using h
  · intro h x
    calc
      hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport g
          (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
          g.backward (hbXiPeierlsUnitSourceFEPacketTransport
            (hbXiPeierlsCenteredQNMPhysicalClockStep n t (g.forward x))) := by
              rw [hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport, g.forward_clock]
      _ = g.backward (hbXiPeierlsCenteredQNMPhysicalClockStep n t
            (hbXiPeierlsUnitSourceFEPacketTransport (g.forward x))) := by rw [h]
      _ = hbXiPeierlsCenteredQNMPhysicalClockStep n t
            (hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport g x) := by
              rw [hbXiPeierlsClockGaugeConjugatedUnitSourceFETransport, g.backward_clock]

/-- A nowhere-zero diagonal weight is a clock-preserving packet gauge. -/
def hbXiPeierlsDiagonalClockPreservingGauge
    (b : XiZeroCopy → ℂ) (hb : ∀ q, b q ≠ 0) (n : ℕ) (t : ℝ) :
    HBXiPeierlsClockPreservingGauge n t where
  forward := hbXiPeierlsWeightedPacket b
  backward := hbXiPeierlsWeightedPacket fun q => (b q)⁻¹
  backward_forward := by
    intro x
    ext q
    simp [hbXiPeierlsWeightedPacket_apply, hb q]
  forward_backward := by
    intro x
    ext q
    simp [hbXiPeierlsWeightedPacket_apply, hb q]
  forward_clock := by
    intro x
    ext q
    simp only [hbXiPeierlsWeightedPacket_apply,
      hbXiPeierlsCenteredQNMPhysicalClockStep_apply]
    ring

/-- Covariance of a diagonal-gauge presentation with the fixed physical clock. -/
def HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
    (b : XiZeroCopy → ℂ) (n : ℕ) (t : ℝ) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport b
        (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t
        (hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport b x)

/-- A nowhere-zero diagonal gauge leaves finite physical-clock covariance unchanged. -/
theorem hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff_literal
    (b : XiZeroCopy → ℂ) (hb : ∀ q, b q ≠ 0) (n : ℕ) (t : ℝ) :
    HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant b n t ↔
      HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant n t := by
  exact hbXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff
    (hbXiPeierlsDiagonalClockPreservingGauge b hb n t)

/-- Complete diagonal-gauge classification: covariance occurs only at zero time or under RH. -/
theorem hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff
    (b : XiZeroCopy → ℂ) (hb : ∀ q, b q ≠ 0) (n : ℕ) (t : ℝ) :
    HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant b n t ↔
      t = 0 ∨ RiemannHypothesis := by
  rw [hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff_literal
    b hb n t, hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff]

/-- Even the Hilbert-90 amplitude gauge, which trivializes the FE cocycle to one, leaves the
unit-clock endpoint exactly RH-strength. -/
theorem hbXiPeierlsUnitSourceAmplitudeGaugePhysicalClockStepCovariant_iff_rh :
    HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
        hbXiPeierlsUnitSourceAmplitudeGauge 0 1 ↔ RiemannHypothesis := by
  rw [hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff
    hbXiPeierlsUnitSourceAmplitudeGauge hbXiPeierlsUnitSourceAmplitudeGauge_ne_zero 0 1]
  simp

/-- Exact Hilbert-90/clock separation: the amplitude gauge makes source-FE transport pure
reflection plus conjugation, while covariance with the fixed unit clock remains equivalent to RH. -/
theorem hbXiPeierlsUnitSourceAmplitudeGaugeTrivializationClockObstruction :
    (∀ (x : HBXiPeierlsPacket) (r : XiZeroCopy),
      hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport
          hbXiPeierlsUnitSourceAmplitudeGauge x r =
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r))) ∧
    (HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
        hbXiPeierlsUnitSourceAmplitudeGauge 0 1 ↔ RiemannHypothesis) := by
  exact ⟨hbXiPeierlsUnitSourceAmplitudeGauge_conjugatedTransport_apply,
    hbXiPeierlsUnitSourceAmplitudeGaugePhysicalClockStepCovariant_iff_rh⟩

/-- Closed route-kill package: no invertible clock-preserving packet gauge can manufacture the
missing HB covariance, and the explicit cocycle-trivializing Hilbert-90 gauge remains terminal. -/
def D4HBClockPreservingGaugeConjugacyRouteKilled : Prop :=
  (∀ (n : ℕ) (t : ℝ) (g : HBXiPeierlsClockPreservingGauge n t),
    HBXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant g ↔
      HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant n t) ∧
  (∀ (b : XiZeroCopy → ℂ), (∀ q, b q ≠ 0) → ∀ (n : ℕ) (t : ℝ),
    HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant b n t ↔
      t = 0 ∨ RiemannHypothesis) ∧
  ((∀ (x : HBXiPeierlsPacket) (r : XiZeroCopy),
      hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFETransport
          hbXiPeierlsUnitSourceAmplitudeGauge x r =
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv r))) ∧
    (HBXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant
        hbXiPeierlsUnitSourceAmplitudeGauge 0 1 ↔ RiemannHypothesis))

theorem d4HBClockPreservingGaugeConjugacyRouteKilled :
    D4HBClockPreservingGaugeConjugacyRouteKilled := by
  refine ⟨?_, ?_, ?_⟩
  · intro n t g
    exact hbXiPeierlsClockGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff g
  · intro b hb n t
    exact hbXiPeierlsDiagonalGaugeConjugatedUnitSourceFEPhysicalClockStepCovariant_iff
      b hb n t
  · exact hbXiPeierlsUnitSourceAmplitudeGaugeTrivializationClockObstruction

end

end RHTower
