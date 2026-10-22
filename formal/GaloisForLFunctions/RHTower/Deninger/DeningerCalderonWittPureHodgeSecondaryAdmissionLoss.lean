import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedHellingerGammaPureHodgeCoface
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiGreenIncidenceComparison

/-!
# Pure-Hodge secondary admission loss

The global Deninger--Calderon--Witt Gamma witness detects the critical line:
at a nonzero modular displacement it is not in the global Gamma-admitted
Hodge sector.  There is nevertheless a canonical rank-one lift of that
witness to the primitive-promoted pure-Hodge cell sector, and every value of
this lift is actually admitted there.

Thus primary pure-Hodge admission cannot reflect the global secondary Gamma
class.  The final theorem gives the exact witness-level information-loss
classification, without assuming the Riemann hypothesis or any positivity
statement.
-/

namespace RHTower

open PrimitivePromotedCellHodgeRigidity
open PrimitivePromotedPureHodgeCountertransport
open PrimitivePromotedPureHodgeModularTransgression

noncomputable section

/--
Rank-one secondary lift: read the normalized global cross-prime incidence
coordinate and place it on the depth-zero odd pure-Hodge transgression.
-/
def deningerCalderonWittPureHodgeSecondaryLift
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
      xiGammaEulerCalderonWittCellMilnorIncidence :=
  (LinearMap.toSpanSingleton ℂ
      xiGammaEulerCalderonWittCellMilnorIncidence
      (pureHodgeCellOddTransgression a
        (shiftedPureOrderedDistinctCellPair hpq 0 0))).comp
    (deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate p q hpq)

/-- The canonical global Gamma witness lifts exactly to the odd pure-Hodge cell. -/
theorem deningerCalderonWittPureHodgeSecondaryLift_witness
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    deningerCalderonWittPureHodgeSecondaryLift hpq a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) =
      pureHodgeCellOddTransgression a
        (shiftedPureOrderedDistinctCellPair hpq 0 0) := by
  simp [deningerCalderonWittPureHodgeSecondaryLift,
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness]

/-- Every lifted value belongs to every actual pure-Hodge admission sector. -/
theorem deningerCalderonWittPureHodgeSecondaryLift_mem_actual
    {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence) :
    deningerCalderonWittPureHodgeSecondaryLift hpq a s ∈
      actualCellGammaAdmittedHodgeSector b := by
  exact Submodule.smul_mem _ _
    (pureHodgeCellOddTransgression_mem_actual a b
      (shiftedPureOrderedDistinctCellPair hpq 0 0))

/-- The lift is a chain map for the identity secondary boundary models. -/
theorem deningerCalderonWittPureHodgeSecondaryLift_chain
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    (LinearMap.id :
      xiGammaEulerCalderonWittCellMilnorIncidence →ₗ[ℂ]
        xiGammaEulerCalderonWittCellMilnorIncidence).comp
        (deningerCalderonWittPureHodgeSecondaryLift hpq a) =
      (deningerCalderonWittPureHodgeSecondaryLift hpq a).comp
        (LinearMap.id :
        deningerCalderonWittGlobalMilnorIncidence →ₗ[ℂ]
          deningerCalderonWittGlobalMilnorIncidence) := by
  apply LinearMap.ext
  intro s
  rfl

/-- Global Gamma admission maps into actual primary pure-Hodge admission. -/
theorem deningerCalderonWittPureHodgeSecondaryLift_map_le_actual
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    (deningerCalderonWittGammaAdmittedHodgeSector a).map
        (deningerCalderonWittPureHodgeSecondaryLift hpq a) ≤
      actualCellGammaAdmittedHodgeSector a := by
  intro y hy
  obtain ⟨s, _hs, rfl⟩ := hy
  exact deningerCalderonWittPureHodgeSecondaryLift_mem_actual hpq a a s

/--
Exact canonical information-loss classification: the global witness is
excluded while its pure-Hodge lift is admitted exactly away from the critical
modular displacement.
-/
theorem deningerCalderonWittPureHodgeSecondaryLift_witness_admission_gap_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) :
    deningerCalderonWittCrossPrimeGammaWitness hpq ∉
        deningerCalderonWittGammaAdmittedHodgeSector a ∧
      deningerCalderonWittPureHodgeSecondaryLift hpq a
          (deningerCalderonWittCrossPrimeGammaWitness hpq) ∈
        actualCellGammaAdmittedHodgeSector a ↔
      a ≠ 0 := by
  constructor
  · intro hgap ha
    exact hgap.1
      ((deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
        hpq a 0).mpr ha)
  · intro ha
    constructor
    · intro hmem
      exact ha
        ((deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
          hpq a 0).mp hmem)
    · exact deningerCalderonWittPureHodgeSecondaryLift_mem_actual hpq a a _

/-- Off the critical line, the pure-Hodge lift does not reflect admission. -/
theorem deningerCalderonWittPureHodgeSecondaryLift_not_admission_reflecting
    {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0) :
    ¬ ∀ s : deningerCalderonWittGlobalMilnorIncidence,
        deningerCalderonWittPureHodgeSecondaryLift hpq a s ∈
            actualCellGammaAdmittedHodgeSector a →
          s ∈ deningerCalderonWittGammaAdmittedHodgeSector a := by
  intro hreflect
  have hgap :=
    (deningerCalderonWittPureHodgeSecondaryLift_witness_admission_gap_iff hpq a).mpr ha
  exact hgap.1 (hreflect _ hgap.2)

end

end RHTower
