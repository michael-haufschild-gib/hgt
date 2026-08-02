import GaloisForLFunctions.RHTower.MobiusThetaInternalJetSourceLocalSpanning
import GaloisForLFunctions.RHTower.RiemannDenseSourceClosedAdmissionLaw
import GaloisForLFunctions.RHTower.DeningerCalderonWittCompletedXiHellingerGammaPureHodgeCoface

/-!
# Local physical-jet to completed Hellinger--Gamma incidence bridge

The internally promoted Möbius--theta source retains the first nonzero Xi
jet at every divisor support, including arbitrary multiplicity.  This file
uses that source coefficient as the coefficient of the canonical completed
Calderón--Witt incidence vector at the first multiplicity copy.

The resulting completed incidence is nonzero, decodes to the same physical
source coefficient times the actual Gamma incidence witness, and is
recovered by the completed Hellinger--Gamma adjacent coface for every real
modular displacement.  Thus physical-jet provenance and Hodge-incidence
provenance meet coefficient-faithfully at every local divisor block.

This is the local joint marginal required by conservative resolved graph
descent.  It does not assert the missing global closed-graph grade
separation: raw coface recovery still holds both on and off the critical
line.
-/

open Complex Set Finset Filter Topology

namespace RHTower

noncomputable section

open CompletedXiHellingerGammaPureHodgeCoface
open PrimitivePromotedCellHodgeRigidity
open PrimitivePromotedPureHodgeCountertransport
open PrimitivePromotedPureHodgeModularTransgression
open PrimitivePromotedHellingerGammaPureHodgeCoface

/-- First multiplicity copy of a divisor support. -/
def thetaInternalJetLeadingZeroCopy (rho : XiDivisorSupport) : XiZeroCopy :=
  ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩

/-- Diagonal physical source moment at the first nonzero Xi jet order. -/
def thetaInternalJetLeadingSourceCoefficient (rho : XiDivisorSupport) : ℂ :=
  thetaInternalJetLocalMomentMatrix rho
    ⟨0, xiSupportMultiplicity_pos rho⟩
    ⟨0, xiSupportMultiplicity_pos rho⟩

/-- The leading physical source coefficient is the first nonzero Xi jet. -/
theorem thetaInternalJetLeadingSourceCoefficient_eq (rho : XiDivisorSupport) :
    thetaInternalJetLeadingSourceCoefficient rho =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) := by
  exact thetaInternalJetLocalMomentMatrix_diag rho _

/-- The leading physical source coefficient never vanishes. -/
theorem thetaInternalJetLeadingSourceCoefficient_ne_zero (rho : XiDivisorSupport) :
    thetaInternalJetLeadingSourceCoefficient rho ≠ 0 := by
  rw [thetaInternalJetLeadingSourceCoefficient_eq]
  exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho

/-- The canonical completed incidence vector has normalized coefficient one. -/
theorem deningerCanonicalCompletedIncidenceVector_coefficient
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionCoefficient p q hpq r
        (deningerCanonicalCompletedIncidenceVector p q hpq r) = 1 := by
  have h := congrArg
    (deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate p q hpq)
    (deningerCanonicalCompletedIncidenceVector_sourceValue p q hpq r)
  simpa [deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue,
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness] using h

/-- Completed incidence carrying the first nonzero physical theta-source jet. -/
def thetaInternalJetLeadingCompletedIncidence
    (p q : Nat.Primes) (hpq : p ≠ q) (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  thetaInternalJetLeadingSourceCoefficient rho •
    deningerCanonicalCompletedIncidenceVector p q hpq
      (thetaInternalJetLeadingZeroCopy rho)

/-- The chosen completed incidence coefficient is exactly the physical source moment. -/
theorem thetaInternalJetLeadingCompletedIncidence_coefficient
    (p q : Nat.Primes) (hpq : p ≠ q) (rho : XiDivisorSupport) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionCoefficient p q hpq
        (thetaInternalJetLeadingZeroCopy rho)
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho) =
      thetaInternalJetLeadingSourceCoefficient rho := by
  rw [thetaInternalJetLeadingCompletedIncidence, map_smul,
    deningerCanonicalCompletedIncidenceVector_coefficient]
  simp

/-- No local physical multiplicity direction disappears in completed incidence. -/
theorem thetaInternalJetLeadingCompletedIncidence_ne_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (rho : XiDivisorSupport) :
    thetaInternalJetLeadingCompletedIncidence p q hpq rho ≠ 0 := by
  intro hzero
  have hcoefficient := congrArg
    (deningerCalderonWittCrossPrimeXiIncidenceCompletionCoefficient p q hpq
      (thetaInternalJetLeadingZeroCopy rho)) hzero
  rw [thetaInternalJetLeadingCompletedIncidence_coefficient, map_zero] at hcoefficient
  exact thetaInternalJetLeadingSourceCoefficient_ne_zero rho hcoefficient

/-- Decoding gives the same physical source coefficient times the actual Gamma witness. -/
theorem thetaInternalJetLeadingCompletedIncidence_sourceValue
    (p q : Nat.Primes) (hpq : p ≠ q) (rho : XiDivisorSupport) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue p q hpq
        (thetaInternalJetLeadingZeroCopy rho)
        (thetaInternalJetLeadingCompletedIncidence p q hpq rho) =
      thetaInternalJetLeadingSourceCoefficient rho •
        deningerCalderonWittCrossPrimeGammaWitness hpq := by
  rw [thetaInternalJetLeadingCompletedIncidence, map_smul,
    deningerCanonicalCompletedIncidenceVector_sourceValue]

/-- Leading physical jet placed on the actual gauged odd pure-Hodge cell. -/
def thetaInternalJetLeadingGaugedPureHodgePrimitive
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (rho : XiDivisorSupport) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  thetaInternalJetLeadingSourceCoefficient rho •
    hellingerGammaGaugedPureHodgePrimitive hpq a n

/-- The joint local physical/Hodge primitive remains in every primary admission sector. -/
theorem thetaInternalJetLeadingGaugedPureHodgePrimitive_mem_actual
    {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℝ) (n : ℕ)
    (rho : XiDivisorSupport) :
    thetaInternalJetLeadingGaugedPureHodgePrimitive hpq a n rho ∈
      actualCellGammaAdmittedHodgeSector b := by
  exact Submodule.smul_mem _ _
    (hellingerGammaGaugedPureHodgePrimitive_mem_actual hpq a b n)

/-- Its unsquared secondary trace is physical leading-jet coefficient times Gamma trace. -/
theorem thetaInternalJetLeadingGaugedPureHodgePrimitive_trace_eq
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (rho : XiDivisorSupport) :
    pureHodgeCellPoincareTrace
        (shiftedPureOrderedDistinctCellPair hpq n n)
        (thetaInternalJetLeadingGaugedPureHodgePrimitive hpq a n rho) =
      thetaInternalJetLeadingSourceCoefficient rho *
        hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n := by
  rw [thetaInternalJetLeadingGaugedPureHodgePrimitive, map_smul]
  rfl

/--
Local conservative detector: since the physical leading jet is nonzero,
the joined unsquared Hodge trace vanishes exactly at zero displacement.
-/
theorem thetaInternalJetLeadingGaugedPureHodgePrimitive_trace_eq_zero_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (rho : XiDivisorSupport) :
    pureHodgeCellPoincareTrace
        (shiftedPureOrderedDistinctCellPair hpq n n)
        (thetaInternalJetLeadingGaugedPureHodgePrimitive hpq a n rho) = 0 ↔
      a = 0 := by
  rw [thetaInternalJetLeadingGaugedPureHodgePrimitive_trace_eq]
  constructor
  · intro hzero
    have htrace : hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n = 0 :=
      (mul_eq_zero.mp hzero).resolve_left
        (thetaInternalJetLeadingSourceCoefficient_ne_zero rho)
    exact (hellingerGammaGaugedPureHodgeSecondaryTrace_eq_zero_iff hpq a n).mp htrace
  · intro ha
    rw [(hellingerGammaGaugedPureHodgeSecondaryTrace_eq_zero_iff hpq a n).mpr ha,
      mul_zero]

/-- The physical leading jet coefficient has an exact completed Hellinger coface recovery. -/
theorem thetaInternalJetLeadingCompletedIncidence_cofaceRecovery_tendsto
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ)
    (rho : XiDivisorSupport) :
    Tendsto
      (fun N : ℕ => hellingerGammaCompletedCofaceRecovery hpq a
        (∑ n ∈ Finset.range N,
          hellingerGammaCompletedAdjacentCoface hpq a n
            (thetaInternalJetLeadingCompletedIncidence p q hpq rho)))
      atTop
      (𝓝 (thetaInternalJetLeadingCompletedIncidence p q hpq rho)) := by
  exact hellingerGammaCompletedCofaceRecovery_tendsto_xi hpq a _

end

end RHTower
