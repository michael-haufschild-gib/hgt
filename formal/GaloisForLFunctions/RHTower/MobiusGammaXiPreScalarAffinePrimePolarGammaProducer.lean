import GaloisForLFunctions.RHTower.EulerPreScalarGammaReporterRigidity
import GaloisForLFunctions.RHTower.MobiusGammaXiMarkedClockBoundaryRateDecoupling

/-!
# Pre-scalar affine prime–polar–Gamma producer

This module supplies the affine source object forced by zero-clock G-CE
decoupling.  Its fixed Hilbert charge combines the unique full-Euler
prime/polar reporter with the explicit archimedean Gamma coordinate before
overlap division.  Its linear mark is the two-order Möbius clock--Sonin
producer.

One joint source readout is exactly the completed division-free
prime--polar--Gamma numerator plus the marked clock commutator seam.  At zero
clock the commutator vanishes but the charge packet remains nonzero.  No Xi
divisor, continued Ward response, or scalar opposite controller occurs in the
construction.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap
open GaloisForLFunctions

theorem eulerPositiveProbability_pos
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    0 < eulerPositiveProbability sigma n :=
  div_pos (eulerPositiveMass_pos sigma n) (eulerPositiveTotal_pos hsigma)

theorem eulerPositiveStateWeight_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    eulerPositiveStateWeight sigma n ≠ 0 := by
  have hsqrt :
      Real.sqrt (eulerPositiveProbability sigma n) ≠ 0 :=
    (Real.sqrt_pos.2 (eulerPositiveProbability_pos hsigma n)).ne'
  change ((Real.sqrt (eulerPositiveProbability sigma n) : ℝ) : ℂ) ≠ 0
  exact_mod_cast hsqrt

theorem eulerPositivePreScalarGammaSource_ne_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    eulerPositivePreScalarGammaSource sigma hsigma ≠ 0 := by
  intro hzero
  let n : ℕ+ := ⟨2, by omega⟩
  have hcoord := congrArg (fun z : EulerPositiveL2 => z n) hzero
  have hsigma0 : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr hsigma.ne')
  have hlog : ((2 * Real.log (n : ℕ) : ℝ) : ℂ) ≠ 0 := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      (Real.log_pos (by norm_num)).ne'
    change ((2 * Real.log 2 : ℝ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero (by norm_num) hlog2
  have hstate : eulerPositiveStateWeight sigma n ≠ 0 :=
    eulerPositiveStateWeight_ne_zero hsigma n
  change
    ((sigma - 1 : ℝ) : ℂ) *
        (((2 * Real.log (n : ℕ) : ℝ) : ℂ) *
          eulerPositiveStateWeight sigma n) = 0 at hcoord
  exact (mul_ne_zero hsigma0 (mul_ne_zero hlog hstate)) hcoord

/-- Hilbert carrier for the explicit archimedean coordinate and the complete
positive-Euler prime/polar source. -/
abbrev MobiusGammaXiPreScalarChargeSpace :=
  WithLp 2 (ℂ × EulerPositiveL2)

/-- Marked affine carrier retaining both the charge and the two source orders. -/
abbrev MobiusGammaXiPreScalarAffineProducerSpace :=
  MobiusGammaXiPreScalarChargeSpace ×
    WithLp 2 (MobiusClockSourceL2 × MobiusClockSourceL2)

/-- Explicit archimedean coordinate before overlap division. -/
def mobiusGammaXiPreScalarArchimedeanCoordinate
    (sigma u : ℝ) : ℂ :=
  -2 * eulerPositivePreScalarGraphDenominator sigma u *
    logDeriv archFactor
      (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)

/-- Canonical Hilbert lift of the division-free prime--polar--Gamma charge. -/
def mobiusGammaXiPreScalarPrimePolarGammaCharge
  (sigma u : ℝ) (hsigma : 1 < sigma) :
    MobiusGammaXiPreScalarChargeSpace :=
  (I / 2) •
    WithLp.toLp 2 ((starRingEnd ℂ)
        (mobiusGammaXiPreScalarArchimedeanCoordinate sigma u),
      eulerPositivePreScalarGammaSource sigma hsigma)

/-- Canonical damped source probe reading the charge. -/
def mobiusGammaXiPreScalarPrimePolarGammaProbe
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    MobiusGammaXiPreScalarChargeSpace :=
  WithLp.toLp 2
    (1, eulerPositiveCriticalDampedStateLp sigma u hsigma hu)

theorem inner_mobiusGammaXiPreScalarPrimePolarGammaCharge_probe
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (mobiusGammaXiPreScalarPrimePolarGammaCharge sigma u hsigma)
        (mobiusGammaXiPreScalarPrimePolarGammaProbe sigma u hsigma hu) =
      eulerPositivePreScalarGammaXiNumerator sigma u hsigma hu := by
  simp [mobiusGammaXiPreScalarPrimePolarGammaCharge,
    mobiusGammaXiPreScalarPrimePolarGammaProbe,
    mobiusGammaXiPreScalarArchimedeanCoordinate,
    eulerPositivePreScalarGammaXiNumerator,
    WithLp.prod_inner_apply]
  ring

theorem mobiusGammaXiPreScalarPrimePolarGammaCharge_ne_zero
    {sigma u : ℝ} (hsigma : 1 < sigma) :
    mobiusGammaXiPreScalarPrimePolarGammaCharge sigma u hsigma ≠ 0 := by
  intro hzero
  have hsnd := congrArg
    (fun z : MobiusGammaXiPreScalarChargeSpace => z.snd) hzero
  change (I / 2 : ℂ) •
      eulerPositivePreScalarGammaSource sigma hsigma = 0 at hsnd
  exact (smul_ne_zero (by norm_num) (eulerPositivePreScalarGammaSource_ne_zero hsigma)) hsnd

/-- Source-native affine producer: fixed completed charge plus linear marked clock jet. -/
def mobiusGammaXiPreScalarAffineProducer
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (x : MobiusClockSourceL2) :
    MobiusGammaXiPreScalarAffineProducerSpace :=
  (mobiusGammaXiPreScalarPrimePolarGammaCharge sigma u hsigma,
    mobiusClockSoninMarkedProducer
      a c d r hc hcd hr N sigma (u : ℂ) hsigma (by simpa using hu) x)

def mobiusGammaXiPreScalarAffineChargePort
    (z : MobiusGammaXiPreScalarAffineProducerSpace) :
    MobiusGammaXiPreScalarChargeSpace :=
  z.1

def mobiusGammaXiPreScalarAffineOddJetPort
    (z : MobiusGammaXiPreScalarAffineProducerSpace) :
    MobiusClockSourceL2 :=
  mobiusClockSoninMarkedOddPort z.2

/-- Joint scalarizer, applied only after the charge and order marks are retained. -/
def mobiusGammaXiPreScalarAffineReadout
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (z : MobiusGammaXiPreScalarAffineProducerSpace) : ℂ :=
  inner ℂ (mobiusGammaXiPreScalarAffineChargePort z)
      (mobiusGammaXiPreScalarPrimePolarGammaProbe sigma u hsigma hu) +
    2 * inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (mobiusGammaXiPreScalarAffineOddJetPort z)

@[simp] theorem mobiusGammaXiPreScalarAffineProducer_chargePort
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineChargePort
        (mobiusGammaXiPreScalarAffineProducer
          a c d r hc hcd hr N sigma u hsigma hu x) =
      mobiusGammaXiPreScalarPrimePolarGammaCharge sigma u hsigma := rfl

theorem mobiusGammaXiPreScalarAffineProducer_oddJetPort
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineOddJetPort
        (mobiusGammaXiPreScalarAffineProducer
          a c d r hc hcd hr N sigma u hsigma hu x) =
      (1 / 2 : ℂ) •
        soninCofinalComplexClockCommutator
          a c d r hc hcd hr N sigma (u : ℂ) hsigma (by simpa using hu) x := by
  exact mobiusClockSoninMarkedOddPort_producer
    a c d r hc hcd hr N sigma (u : ℂ) hsigma (by simpa using hu) x

theorem mobiusGammaXiPreScalarAffineReadout_producer
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineReadout sigma u hsigma hu
        (mobiusGammaXiPreScalarAffineProducer
          a c d r hc hcd hr N sigma u hsigma hu x) =
      eulerPositivePreScalarGammaXiNumerator sigma u hsigma hu +
        inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
          (soninCofinalComplexClockCommutator
            a c d r hc hcd hr N sigma (u : ℂ) hsigma
              (by simpa using hu) x) := by
  rw [mobiusGammaXiPreScalarAffineReadout,
    mobiusGammaXiPreScalarAffineProducer_chargePort,
    inner_mobiusGammaXiPreScalarPrimePolarGammaCharge_probe,
    mobiusGammaXiPreScalarAffineProducer_oddJetPort,
    inner_smul_right]
  ring

theorem mobiusGammaXiPreScalarAffineProducer_zeroClock_oddJet
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineOddJetPort
        (mobiusGammaXiPreScalarAffineProducer
          a c d r hc hcd hr N sigma 0 hsigma (by norm_num) x) = 0 := by
  exact mobiusClockSoninMarkedOddPort_zeroClock
    a c d r hc hcd hr N sigma hsigma x

theorem mobiusGammaXiPreScalarAffineProducer_zeroClock_ne_zero
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineProducer
      a c d r hc hcd hr N sigma 0 hsigma (by norm_num) x ≠ 0 := by
  intro hzero
  have hfst := congrArg Prod.fst hzero
  exact (mobiusGammaXiPreScalarPrimePolarGammaCharge_ne_zero hsigma) hfst

theorem mobiusGammaXiPreScalarAffineReadout_zeroClock
    (a c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) (N : ℕ)
    (sigma : ℝ) (hsigma : 1 < sigma) (x : MobiusClockSourceL2) :
    mobiusGammaXiPreScalarAffineReadout sigma 0 hsigma (by norm_num)
        (mobiusGammaXiPreScalarAffineProducer
          a c d r hc hcd hr N sigma 0 hsigma (by norm_num) x) =
      eulerPositivePreScalarGammaXiNumerator
        sigma 0 hsigma (by norm_num) := by
  rw [mobiusGammaXiPreScalarAffineReadout]
  rw [mobiusGammaXiPreScalarAffineProducer_chargePort,
    inner_mobiusGammaXiPreScalarPrimePolarGammaCharge_probe,
    mobiusGammaXiPreScalarAffineProducer_zeroClock_oddJet]
  simp

/-- Canonical actual affine source at zero clock. -/
def canonicalMobiusGammaXiPreScalarAffineZeroClockProducer (N : ℕ) :
    MobiusGammaXiPreScalarAffineProducerSpace :=
  mobiusGammaXiPreScalarAffineProducer
    4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
    2 0 (by norm_num) (by norm_num) canonicalMobiusClockMarkedSource

/-- Canonical actual affine source at one positive clock. -/
def canonicalMobiusGammaXiPreScalarAffinePositiveClockProducer (N : ℕ) :
    MobiusGammaXiPreScalarAffineProducerSpace :=
  mobiusGammaXiPreScalarAffineProducer
    4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
    2 1 (by norm_num) (by norm_num) canonicalMobiusClockMarkedSource

/-- Premise-free capstone: every canonical zero-clock packet is nonzero solely
because its completed charge survives while its commutator jet vanishes; at
positive clock the same affine packet reads the completed prime--polar--Gamma
numerator plus the exact marked commutator seam. -/
theorem canonicalMobiusGammaXiPreScalarAffineProducer_closed :
    (∀ N,
      canonicalMobiusGammaXiPreScalarAffineZeroClockProducer N ≠ 0 ∧
      mobiusGammaXiPreScalarAffineChargePort
          (canonicalMobiusGammaXiPreScalarAffineZeroClockProducer N) =
        mobiusGammaXiPreScalarPrimePolarGammaCharge 2 0 (by norm_num) ∧
      mobiusGammaXiPreScalarAffineOddJetPort
          (canonicalMobiusGammaXiPreScalarAffineZeroClockProducer N) = 0 ∧
      mobiusGammaXiPreScalarAffineReadout 2 0 (by norm_num) (by norm_num)
          (canonicalMobiusGammaXiPreScalarAffineZeroClockProducer N) =
        eulerPositivePreScalarGammaXiNumerator
          2 0 (by norm_num) (by norm_num)) ∧
    (∀ N,
      mobiusGammaXiPreScalarAffineChargePort
          (canonicalMobiusGammaXiPreScalarAffinePositiveClockProducer N) =
        mobiusGammaXiPreScalarPrimePolarGammaCharge 2 1 (by norm_num) ∧
      mobiusGammaXiPreScalarAffineOddJetPort
          (canonicalMobiusGammaXiPreScalarAffinePositiveClockProducer N) =
        (1 / 2 : ℂ) •
          soninCofinalComplexClockCommutator
            4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
            2 1 (by norm_num) (by norm_num)
            canonicalMobiusClockMarkedSource ∧
      mobiusGammaXiPreScalarAffineReadout 2 1 (by norm_num) (by norm_num)
          (canonicalMobiusGammaXiPreScalarAffinePositiveClockProducer N) =
        eulerPositivePreScalarGammaXiNumerator
            2 1 (by norm_num) (by norm_num) +
          inner ℂ (infiniteMobiusCriticalFisherTangentLp 2 (by norm_num))
            (soninCofinalComplexClockCommutator
              4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
              2 1 (by norm_num) (by norm_num)
              canonicalMobiusClockMarkedSource)) := by
  constructor
  · intro N
    refine ⟨?_, rfl, ?_, ?_⟩
    · exact mobiusGammaXiPreScalarAffineProducer_zeroClock_ne_zero
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
        2 (by norm_num) canonicalMobiusClockMarkedSource
    · exact mobiusGammaXiPreScalarAffineProducer_zeroClock_oddJet
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
        2 (by norm_num) canonicalMobiusClockMarkedSource
    · exact mobiusGammaXiPreScalarAffineReadout_zeroClock
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
        2 (by norm_num) canonicalMobiusClockMarkedSource
  · intro N
    refine ⟨rfl, ?_, ?_⟩
    · exact mobiusGammaXiPreScalarAffineProducer_oddJetPort
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
        2 1 (by norm_num) (by norm_num) canonicalMobiusClockMarkedSource
    · exact mobiusGammaXiPreScalarAffineReadout_producer
        4 2 3 3 (by norm_num) (by norm_num) (by norm_num) N
        2 1 (by norm_num) (by norm_num) canonicalMobiusClockMarkedSource

end RHTower
