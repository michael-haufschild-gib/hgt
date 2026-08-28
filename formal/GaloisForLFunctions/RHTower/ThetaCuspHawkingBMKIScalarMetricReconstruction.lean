import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSelfDualDeformedTwoJetVertex
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedHorizonRegularBranch

/-!
# Exact massless topological KI reconstruction on Birmingham--Mokhtari jets

The four-dimensional Birmingham--Mokhtari background has `n = 2`, `K = -1`, `M = 0`,
`f(r) = r^2 - 1`.  Specializing the Kodama--Ishibashi scalar reconstruction coefficients to
this background collapses them to

`P_X = 16 m^2 k^2`, `Q_X = 4m(2-r^2)`, `P_Y = 0`, `Q_Y = -4mr^2`, `P_Z = 4m`,

where `m = k^2 + 2`.  Converting from `r` to the Birmingham--Mokhtari variable
`z = 1-rho^2`, `rho = r^-1`, gives the gauge-invariant orbit below.  `zInv` is kept as an
algebraic inverse-coordinate variable, so every theorem is unconditional.

The key cancellation is

`2 rho Ztilde - (X+Y) = rho (k^2+2) Phi`.

Thus the master field is already encoded algebraically in the reconstructed metric invariants;
all first-radial-jet terms cancel.  For an actual Xi divisor the factor `k^2+2` is proved nonzero,
so a reduced reconstruction recovers the exact hypergeometric monodromy mode with no hypothesis.
This supplies the missing scalar master-to-metric bridge.  It does not yet identify the resulting
scalar/vector chiral combination with the Plebanski light-cone field.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [KI RECONSTRUCTION]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Gauge-invariant scalar-type KI orbit in the massless four-dimensional topological black-hole
background.  `Ztilde` is the real algebraic factor before multiplication by `i*omega`. -/
structure D4KIScalarGaugeInvariantOrbit where
  X : ℂ
  Y : ℂ
  Ztilde : ℂ
  Z : ℂ
  FttMixed : ℂ
  FrrMixed : ℂ
  FrtMixed : ℂ
  angularTrace : ℂ

/-- Exact `X` invariant after the massless `n=2`, `K=-1` KI specialization and BM change of
variable. -/
def d4KIScalarMasslessTopologicalX
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) : ℂ :=
  omega ^ 2 * rho * zInv * J.value - kSq * rho * J.value +
    2 * rho * (2 * rho ^ 2 - 1) * J.first

/-- Exact `Y` invariant after the same specialization. -/
def d4KIScalarMasslessTopologicalY
    (rho zInv omega : ℂ) (J : D4ComplexRadialTwoJet) : ℂ :=
  -omega ^ 2 * rho * zInv * J.value - 2 * rho * J.first

/-- Frequency-free KI mixed invariant. -/
def d4KIScalarMasslessTopologicalZtilde
    (rho : ℂ) (J : D4ComplexRadialTwoJet) : ℂ :=
  J.value - 2 * (1 - rho ^ 2) * J.first

/-- Exact scalar-type KI gauge-invariant metric reconstruction from a BM master two-jet. -/
def d4KIScalarGaugeInvariantOrbitOfBMMaster
    (rho zInv omega kSq : ℂ)
    (J : D4ComplexRadialTwoJet) : D4KIScalarGaugeInvariantOrbit :=
  let X := d4KIScalarMasslessTopologicalX rho zInv omega kSq J
  let Y := d4KIScalarMasslessTopologicalY rho zInv omega J
  let Ztilde := d4KIScalarMasslessTopologicalZtilde rho J
  let Z := Complex.I * omega * Ztilde
  { X := X
    Y := Y
    Ztilde := Ztilde
    Z := Z
    FttMixed := (X - Y) / 2
    FrrMixed := (-X + Y) / 2
    FrtMixed := Z
    angularTrace := -(X + Y) / 4 }

/-- The two orbit-space diagonal mixed components are exactly traceless. -/
theorem d4KIScalarGaugeInvariantOrbitOfBMMaster_Frr_eq_neg_Ftt
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    (d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).FrrMixed =
      -(d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).FttMixed := by
  simp [d4KIScalarGaugeInvariantOrbitOfBMMaster]
  ring

/-- The frequency pole cancels from `X+Y`; only the angular value and BM first jet remain. -/
theorem d4KIScalarMasslessTopologicalX_add_Y
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    d4KIScalarMasslessTopologicalX rho zInv omega kSq J +
        d4KIScalarMasslessTopologicalY rho zInv omega J =
      -kSq * rho * J.value - 4 * rho * (1 - rho ^ 2) * J.first := by
  simp [d4KIScalarMasslessTopologicalX, d4KIScalarMasslessTopologicalY]
  ring

/-- Exact angular-trace formula of the reconstructed metric. -/
theorem d4KIScalarGaugeInvariantOrbitOfBMMaster_angularTrace
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    (d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).angularTrace =
      rho / 4 * (kSq * J.value + 4 * (1 - rho ^ 2) * J.first) := by
  simp [d4KIScalarGaugeInvariantOrbitOfBMMaster,
    d4KIScalarMasslessTopologicalX, d4KIScalarMasslessTopologicalY]
  ring

/-- Sharp KI master-recovery identity.  All BM radial-derivative terms cancel. -/
theorem d4KIScalarGaugeInvariantOrbitOfBMMaster_masterRecovery
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    2 * rho *
          (d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).Ztilde -
        ((d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).X +
          (d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).Y) =
      rho * (kSq + 2) * J.value := by
  simp [d4KIScalarGaugeInvariantOrbitOfBMMaster,
    d4KIScalarMasslessTopologicalX, d4KIScalarMasslessTopologicalY,
    d4KIScalarMasslessTopologicalZtilde]
  ring

/-- Reduced master-recovery numerator, independent of the potentially vanishing chart factor
`rho`. -/
theorem d4KIScalarGaugeInvariantOrbitOfBMMaster_reducedMasterRecovery
    (rho zInv omega kSq : ℂ) (J : D4ComplexRadialTwoJet) :
    2 * (d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega kSq J).Ztilde +
        kSq * J.value + 4 * (1 - rho ^ 2) * J.first =
      (kSq + 2) * J.value := by
  simp [d4KIScalarGaugeInvariantOrbitOfBMMaster,
    d4KIScalarMasslessTopologicalZtilde]
  ring

/-- Exact BM value/first/second jet of the actual Xi-fibre monodromy mode. -/
def d4BMXiMixedHorizonExactMonodromyTwoJet
    (n k : ℕ) (q : XiZeroCopy) (z : ℂ) : D4ComplexRadialTwoJet where
  value := d4BMXiMixedHorizonExactMonodromyMode n k q z
  first := d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z
  second := d4BMXiMixedHorizonExactMonodromyModeSecondDerivative n k q z

/-- Scalar KI harmonic gap on an actual Xi fibre. -/
def d4KIXiScalarHarmonicGap (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q) + 2

/-- Actual Xi fibres never hit the exceptional scalar harmonic `k^2+2=0`.  Nonzero real part of
the continued BM angular momentum rules out the only possible complex square collision. -/
theorem d4KIXiScalarHarmonicGap_ne_zero (q : XiZeroCopy) :
    d4KIXiScalarHarmonicGap q ≠ 0 := by
  let chi := d4BMXiMixedHorizonAngularMomentum q
  have hchi : chi.re ≠ 0 := d4BMXiMixedHorizonAngularMomentum_re_ne_zero q
  intro h
  change (1 / 4 + chi ^ 2) + 2 = 0 at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hchiIm : chi.im = 0 := by
    have hprod : chi.re * chi.im = 0 := by
      nlinarith [him]
    rcases mul_eq_zero.mp hprod with hRe | hIm
    · exact (hchi hRe).elim
    · exact hIm
  rw [hchiIm] at hre
  norm_num at hre
  nlinarith [sq_nonneg chi.re]

/-- Exact Xi-fibre scalar KI metric orbit. -/
def d4KIXiScalarGaugeInvariantOrbit
    (rho zInv omega : ℂ) (n k : ℕ) (q : XiZeroCopy) (z : ℂ) :
    D4KIScalarGaugeInvariantOrbit :=
  d4KIScalarGaugeInvariantOrbitOfBMMaster rho zInv omega
    (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q))
    (d4BMXiMixedHorizonExactMonodromyTwoJet n k q z)

/-- Unconditional recovery of the exact Xi monodromy master field from the reduced reconstructed
metric numerator.  Division is safe because the physical Xi harmonic gap is never zero. -/
theorem d4KIXiScalarGaugeInvariantOrbit_recovers_exactMonodromyMode
    (rho zInv omega : ℂ) (n k : ℕ) (q : XiZeroCopy) (z : ℂ) :
    (2 * (d4KIXiScalarGaugeInvariantOrbit rho zInv omega n k q z).Ztilde +
          thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q) *
            d4BMXiMixedHorizonExactMonodromyMode n k q z +
          4 * (1 - rho ^ 2) *
            d4BMXiMixedHorizonExactMonodromyModeDerivative n k q z) /
        d4KIXiScalarHarmonicGap q =
      d4BMXiMixedHorizonExactMonodromyMode n k q z := by
  have hrec := d4KIScalarGaugeInvariantOrbitOfBMMaster_reducedMasterRecovery
    rho zInv omega
      (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (xiSpectralPoint q))
      (d4BMXiMixedHorizonExactMonodromyTwoJet n k q z)
  rw [div_eq_iff (d4KIXiScalarHarmonicGap_ne_zero q)]
  simpa [d4KIXiScalarGaugeInvariantOrbit,
    d4BMXiMixedHorizonExactMonodromyTwoJet,
    d4KIXiScalarHarmonicGap, mul_comm] using hrec

end

end RHTower
