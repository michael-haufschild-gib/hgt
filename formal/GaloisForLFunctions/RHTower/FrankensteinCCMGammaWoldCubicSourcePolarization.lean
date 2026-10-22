import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockCubic
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaXiHardySymmetricSquareWeld
import GaloisForLFunctions.RHTower.FrankensteinKreinCCMRoutePSignedConormalResidueBridge

/-!
# CCM--Gamma source polarization of the Wold cubic horizontal rate

The Wold cubic horizon sees the real horizontal rate
`2 * Re (rho - 1/2)`.  Inserting that rate directly into a one-variable completed residue is not
legitimate: real part is not holomorphic.  This module constructs the missing source-side
replacement rather than assuming such a transport.

For each Xi-selected support, the literal signed primitive-depth/CCM completed trace is multiplied
by its pole gauge, its centered Mellin coordinate, and the inverse analytic multiplicity.  Its
removable limit is exactly `rho - 1/2`, with coefficient and multiplicity normalization proved from
the existing Gamma-source residue theorem.  Two independent variables are then selected at a
strict-right copy and its Schwarz-conjugate copy.  Cubing occurs only after the two separately
holomorphic residue gauges have been added.  Successive source limits give

`((rho - 1/2) + conj (rho - 1/2))^(3 : ℕ) = (2 * Re (rho - 1/2))^(3 : ℕ)`.

Multiplication by the finite prime-clock coefficient identifies this literal two-fibre source
landing with the existing Wold cubic horizon response exactly.  Thus third-jet transport is no
longer blocked by sesquiholomorphic scalarization.  This theorem supplies incidence, not the still
missing completed-source order inequality.
-/

open Complex Filter Function Set WithTop Topology MeasureTheory
open scoped BigOperators ComplexOrder
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Multiplicity-normalized centered pole gauge of the literal completed primitive-depth source.
The factor `-I` changes the signed Gamma residue `I m` to the physical multiplicity `m`. -/
def frankensteinCCMGammaCenteredResidueGauge
    (rho : XiDivisorSupport) (u : ℂ) : ℂ :=
  ((u - criticalMellinXiPole rho) *
      (-I * xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace u) *
      (u + 1 - 1 / 2)) /
    (inverseTiltedXiMultiplicity rho : ℂ)

/-- Source/Gamma naturality recovers one centered Xi coordinate, with no simple-zero premise. -/
theorem tendsto_frankensteinCCMGammaCenteredResidueGauge
    (rho : XiDivisorSupport) :
    Tendsto (frankensteinCCMGammaCenteredResidueGauge rho)
      (nhdsWithin (criticalMellinXiPole rho)
        ({criticalMellinXiPole rho}ᶜ))
      (nhds ((rho : ℂ) - 1 / 2)) := by
  have htrace :=
    (xiGammaEulerPrimitiveJointDepthPoleFilledCompletedTrace_residue rho).const_mul (-I)
  have hcoord : Tendsto (fun u : ℂ => u + 1 - 1 / 2)
      (nhdsWithin (criticalMellinXiPole rho)
        ({criticalMellinXiPole rho}ᶜ))
      (nhds ((rho : ℂ) - 1 / 2)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    convert (by fun_prop : ContinuousAt (fun u : ℂ => u + 1 - 1 / 2)
      (criticalMellinXiPole rho)).tendsto using 1
    rw [criticalMellinXiPole_add_one]
  have hmNat : inverseTiltedXiMultiplicity rho ≠ 0 :=
    Nat.ne_of_gt (inverseTiltedXiMultiplicity_pos rho)
  have hm : (inverseTiltedXiMultiplicity rho : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hmNat
  have h := (htrace.mul hcoord).div_const
    (inverseTiltedXiMultiplicity rho : ℂ)
  convert h using 1
  · funext u
    rw [frankensteinCCMGammaCenteredResidueGauge]
    ring_nf
  · field_simp [hm]
    rw [Complex.I_sq]
    ring_nf

/-- Two independent source pole gauges, selected at a retained Xi fibre and its Schwarz mate.
The nonlinear cube is formed before either removable source limit is taken. -/
def frankensteinCCMGammaSchwarzCenteredCubicSource
    (q : XiRightZeroCopy) (N : ℕ) (u v : ℂ) : ℂ :=
  (sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ (3 : ℕ) : ℂ) *
    (frankensteinCCMGammaCenteredResidueGauge q.1.1 u +
      frankensteinCCMGammaCenteredResidueGauge
        (xiRightZeroCopyConjEquiv q).1.1 v) ^ (3 : ℕ)

/-- First source landing retains the full conjugate-fibre pole gauge. -/
def frankensteinCCMGammaSchwarzCenteredCubicFirstLanding
    (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) : ℂ :=
  (sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ (3 : ℕ) : ℂ) *
    (xiRightCenteredZero q +
      frankensteinCCMGammaCenteredResidueGauge
        (xiRightZeroCopyConjEquiv q).1.1 v) ^ (3 : ℕ)

/-- First selected residue is coefficient-faithful and leaves the Schwarz source leg uncollapsed. -/
theorem tendsto_frankensteinCCMGammaSchwarzCenteredCubicSource_first
    (q : XiRightZeroCopy) (N : ℕ) (v : ℂ) :
    Tendsto (fun u : ℂ =>
      frankensteinCCMGammaSchwarzCenteredCubicSource q N u v)
      (nhdsWithin (criticalMellinXiPole q.1.1)
        ({criticalMellinXiPole q.1.1}ᶜ))
      (nhds (frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N v)) := by
  have h := (tendsto_frankensteinCCMGammaCenteredResidueGauge q.1.1).add_const
    (frankensteinCCMGammaCenteredResidueGauge
      (xiRightZeroCopyConjEquiv q).1.1 v)
  have hpow := h.pow 3
  have hmul := hpow.const_mul
    (sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ (3 : ℕ) : ℂ)
  simpa [frankensteinCCMGammaSchwarzCenteredCubicSource,
    frankensteinCCMGammaSchwarzCenteredCubicFirstLanding,
    xiRightCenteredZero_eq_support_sub_half] using hmul

/-- **Source-polarized Wold descent.**  The second selected CCM/Gamma residue is exactly the
finite Wold cubic response.  The real horizontal cube is produced from two independent holomorphic
source variables; it is not inserted as a nonholomorphic continuation. -/
theorem tendsto_frankensteinCCMGammaSchwarzCenteredCubicFirstLanding
    (q : XiRightZeroCopy) (N : ℕ) :
    Tendsto (frankensteinCCMGammaSchwarzCenteredCubicFirstLanding q N)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (sourceZeroHorizontalWoldPrimeClockCubicResponse q.1 N : ℂ)) := by
  have h := tendsto_frankensteinCCMGammaCenteredResidueGauge
    (xiRightZeroCopyConjEquiv q).1.1
  have hconst : Tendsto (fun _ : ℂ => xiRightCenteredZero q)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (xiRightCenteredZero q)) := tendsto_const_nhds
  have hsum : Tendsto (fun v : ℂ =>
      xiRightCenteredZero q +
        frankensteinCCMGammaCenteredResidueGauge
          (xiRightZeroCopyConjEquiv q).1.1 v)
      (nhdsWithin
        (criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1)
        ({criticalMellinXiPole (xiRightZeroCopyConjEquiv q).1.1}ᶜ))
      (nhds (xiRightCenteredZero q +
        (((xiRightZeroCopyConjEquiv q).1.1 : ℂ) - 1 / 2))) := by
    exact hconst.add h
  have hpow := hsum.pow 3
  have hmul := hpow.const_mul
    (sourceHorizontalWoldResidualPrimitiveCubicCoefficient N /
      xiMassNthPrimeLogHeight N ^ (3 : ℕ) : ℂ)
  have hconj :
      (((xiRightZeroCopyConjEquiv q).1.1 : ℂ) - 1 / 2) =
        (starRingEnd ℂ) (xiRightCenteredZero q) := by
    rw [← xiRightCenteredZero_eq_support_sub_half,
      xiRightCenteredZero_conj]
  have hpair :
      xiRightCenteredZero q +
          (((xiRightZeroCopyConjEquiv q).1.1 : ℂ) - 1 / 2) =
        ((primeDepthBVWoldXiCenteredRate q.1.1 : ℝ) : ℂ) := by
    rw [hconj,
      HedenmalmThetaSource.primeDepthBVWoldXiCenteredRate_right_eq_two_mul_re]
    apply Complex.ext <;> simp
    ring_nf
  convert hmul using 1
  · funext v
    rfl
  · rw [hpair, sourceZeroHorizontalWoldPrimeClockCubicResponse]
    push_cast
    ring_nf

end

end RHTower
