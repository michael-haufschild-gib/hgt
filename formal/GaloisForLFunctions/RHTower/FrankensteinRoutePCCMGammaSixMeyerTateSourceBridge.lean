import GaloisForLFunctions.RHTower.FrankensteinRoutePCCMGammaSixTwoSheetCarrier
import GaloisForLFunctions.RHTower.DeningerGammaSixCofinalMeyerTateXiGreenBoundary

/-!
# Literal Meyer--Tate source production for the P/CCM two-sheet carrier

The P/CCM two-sheet carrier must not be treated as an arbitrarily chosen
horizontal vector.  This module realizes every finite P-tail cell from a
literal ordinary-prime rational-adelic CCM degree-one source, followed by the
completed Meyer--Tate differential, before the two-sheet orientation lift.

The ordinary-prime component of the P label feeds the literal source atom;
its depth component remains in the P-tail coefficient multiplying the
source-produced graph class.  Thus this closes source provenance but does not
pretend to have constructed structural depth or divisor selection.  It is
deliberately not an annihilation theorem.  The missing law remains a
non-universal, reflection-equivariant, Xi-selected relation on these source
cells.
-/

open Complex Filter Topology
open scoped TensorProduct

namespace RHTower

noncomputable section

/-- The anti-diagonal two-sheet lift turns one completed Gamma-six graph class
into the retained horizontal orientation, without taking a scalar trace. -/
def frankensteinTwoSheetMeyerTateAntiLift
    (z : DeningerGammaSixCofinalSingularGraph) : FrankensteinTwoSheetGraph :=
  WithLp.toLp 2 (((1 / 2 : ℂ) • z), ((-1 / 2 : ℂ) • z))

/-- Literal ordinary-prime, cofinal-depth Meyer--Tate degree-one source. -/
def frankensteinRoutePMeyerTateRawSource
    (pe : Nat.Primes × ℕ) (n : ℕ) :
    DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  ccmRationalAdelicOrdinaryPrimeCycleAtom pe.1 ⊗ₜ[ℂ]
    deningerGammaSixCofinalAveragingPacket n

/-- Literal ordinary-prime Meyer--Tate source cell carrying one P-tail
coefficient before horizontal transport. -/
def frankensteinRoutePMeyerTateFiniteSourceCell
    (pe : Nat.Primes × ℕ) (n : ℕ) : FrankensteinTwoSheetGraph :=
  (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
    frankensteinTwoSheetMeyerTateAntiLift
      (deningerGammaSixCofinalMeyerTateCompletedDifferential
        (frankensteinRoutePMeyerTateRawSource pe n))

/-- The P source and the divisor-selected Xi Green source inhabit the same
Meyer--Tate degree-one carrier.  The latter is exactly the reflected Green
coefficient times the former before either differential or scalar readout. -/
theorem deningerGammaSixCofinalXiGreenDegreeOneChain_eq_green_smul_routePMeyerTateRawSource
    (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (n : ℕ) :
    deningerGammaSixCofinalXiGreenDegreeOneChain pe.1 q n =
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
        frankensteinRoutePMeyerTateRawSource pe n := by
  simp only [deningerGammaSixCofinalXiGreenDegreeOneChain,
    frankensteinRoutePMeyerTateRawSource, TensorProduct.tmul_smul]

/-- On every literal prime source atom, the Meyer--Tate source cell is exactly
the coefficient-faithful P-tail finite two-sheet cell. -/
theorem frankensteinRoutePMeyerTateFiniteSourceCell_eq_tailFluxTwoSheetFiniteCell
    (pe : Nat.Primes × ℕ) (n : ℕ) :
    frankensteinRoutePMeyerTateFiniteSourceCell pe n =
      frankensteinRoutePTailFluxTwoSheetFiniteCell pe n := by
  simp only [frankensteinRoutePMeyerTateFiniteSourceCell,
    deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom,
    frankensteinTwoSheetMeyerTateAntiLift,
    frankensteinRoutePTailFluxTwoSheetFiniteCell,
    frankensteinTwoSheetFiniteOrientationPacket]

/-- The literal prime source cells converge in the unscalarized two-sheet
carrier to the retained P-tail horizontal class. -/
theorem tendsto_frankensteinRoutePMeyerTateFiniteSourceCell
    (pe : Nat.Primes × ℕ) :
    Tendsto (frankensteinRoutePMeyerTateFiniteSourceCell pe) atTop
      (nhds (frankensteinRoutePTailFluxTwoSheetCell pe)) := by
  simpa only [frankensteinRoutePMeyerTateFiniteSourceCell_eq_tailFluxTwoSheetFiniteCell]
    using tendsto_frankensteinRoutePTailFluxTwoSheetFiniteCell pe

/-- Every finite literal source cell has the exact horizontal physical
readout of its P-tail coefficient; no finite-stage scalarization occurs. -/
theorem frankensteinTwoSheetPhysicalTransport_meyerTateFiniteSourceCell
    (pe : Nat.Primes × ℕ) (n : ℕ) (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinRoutePMeyerTateFiniteSourceCell pe n) =
      (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
        deningerGammaSixFixedSoninPhysicalReceiver g := by
  rw [frankensteinRoutePMeyerTateFiniteSourceCell_eq_tailFluxTwoSheetFiniteCell,
    frankensteinRoutePTailFluxTwoSheetFiniteCell, map_smul,
    frankensteinTwoSheetPhysicalTransport_finiteOrientationPacket]

/-- **Source-level no-go.**  A literal ordinary-prime Meyer--Tate source cell
cannot have vanishing horizontal transport away from neutral grade.  Hence the
missing selected Stokes law cannot be ordinary boundary blindness. -/
theorem frankensteinTwoSheetPhysicalTransport_meyerTateFiniteSourceCell_eq_zero_iff
    (pe : Nat.Primes × ℕ) (n : ℕ) (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinRoutePMeyerTateFiniteSourceCell pe n) = 0 ↔ g = 0 := by
  rw [frankensteinTwoSheetPhysicalTransport_meyerTateFiniteSourceCell,
    smul_eq_zero, Complex.ofReal_eq_zero,
    deningerGammaSixFixedSoninPhysicalReceiver_eq_zero_iff]
  simp only [(routePPrimitiveBurnolApertureDefectFlux_pos pe).ne', false_or]

/-- **Coefficient-faithful, non-equivariant common-carrier alignment.**  At
one divisor's horizontal grade, the P two-sheet transport and the
divisor-selected Xi Green transport are two scalar multiples of the same
literal Sonin receiver.  No coefficient is divided out or summed away. -/
theorem frankensteinPCCMMeyerTateXiGreenPhysicalAlignment
    (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (n : ℕ) :
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
      frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (frankensteinRoutePMeyerTateFiniteSourceCell pe n) =
      (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
        deningerGammaSixCofinalGraphPhysicalTransport
          (2 * (q.1 : ℂ).re - 1)
          (deningerGammaSixCofinalMeyerTateCompletedDifferential
            (deningerGammaSixCofinalXiGreenDegreeOneChain pe.1 q n)) := by
  rw [frankensteinTwoSheetPhysicalTransport_meyerTateFiniteSourceCell,
    deningerGammaSixCofinalGraphPhysicalTransport_xiGreenFiniteChain]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The aligned common-carrier transport vanishes exactly at the critical
line.  This is a source-level RH detector, not an RH proof. -/
theorem frankensteinPCCMMeyerTateXiGreenPhysicalAlignment_left_eq_zero_iff
    (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (n : ℕ) :
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
      frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (frankensteinRoutePMeyerTateFiniteSourceCell pe n) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [frankensteinTwoSheetPhysicalTransport_meyerTateFiniteSourceCell,
    smul_smul, smul_eq_zero, mul_eq_zero,
    reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff,
    Complex.ofReal_eq_zero,
    deningerGammaSixFixedSoninPhysicalReceiver_eq_zero_iff]
  simp only [(routePPrimitiveBurnolApertureDefectFlux_pos pe).ne', false_or]
  have hgrade :
      2 * (q.1 : ℂ).re - 1 = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [hgrade, or_self]

/-- Exact reducer for the remaining source producer.  If a selected,
reflection-compatible Stokes law makes the two coefficient-faithful common
carrier transports anti-align, then their already-proved alignment forces
that divisor copy onto the critical line.  The anti-alignment premise is the
open source law; it is not asserted here. -/
theorem frankensteinPCCMMeyerTateXiGreenAntiAlignment_forces_criticalLine
    (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (n : ℕ)
    (hanti :
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
          frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
            (frankensteinRoutePMeyerTateFiniteSourceCell pe n) +
        (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
          deningerGammaSixCofinalGraphPhysicalTransport
            (2 * (q.1 : ℂ).re - 1)
            (deningerGammaSixCofinalMeyerTateCompletedDifferential
              (deningerGammaSixCofinalXiGreenDegreeOneChain pe.1 q n)) = 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  let A : DeningerGammaSixSoninPhysicalOperator :=
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
      frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (frankensteinRoutePMeyerTateFiniteSourceCell pe n)
  let B : DeningerGammaSixSoninPhysicalOperator :=
    (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
      deningerGammaSixCofinalGraphPhysicalTransport
        (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalMeyerTateCompletedDifferential
          (deningerGammaSixCofinalXiGreenDegreeOneChain pe.1 q n))
  have halign : A = B := by
    exact frankensteinPCCMMeyerTateXiGreenPhysicalAlignment pe q n
  have hdouble : A + A = 0 := by
    calc
      A + A = A + B := congrArg (fun x => A + x) halign
      _ = 0 := by simpa only [A, B] using hanti
  have hA : A = 0 := by
    rw [← two_smul ℂ A, smul_eq_zero] at hdouble
    simpa using hdouble
  apply frankensteinPCCMMeyerTateXiGreenPhysicalAlignment_left_eq_zero_iff pe q n |>.mp
  simpa only [A] using hA

end

end RHTower
