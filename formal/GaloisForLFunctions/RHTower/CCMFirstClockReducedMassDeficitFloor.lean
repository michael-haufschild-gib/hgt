import GaloisForLFunctions.RHTower.CCMFirstClockPrimePowerTowerCollapse
import GaloisForLFunctions.RHTower.CCMFirstClockTailLowerBoundCompleteness

/-!
# Literal CCM lower-floor as a reduced positive-mass deficit

After complete prime-power tower collapse, this module packages the exact remaining cancellation
problem as one signed difference of nonnegative source masses.  The reduced deficit is the residual
bad prime-tower mass minus the archimedean half-wave budget and every unconditionally oriented good
prime tower.  It is exactly `-π` times the literal published CCM first-clock source.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Excess of the irreducible bad prime-tower mass over the archimedean budget and every
unconditionally oriented good prime tower. -/
def ccmFirstClockReducedMassDeficit (L : ℝ) : ℝ :=
  ccmFirstClockReducedBadTowerResidual L -
    (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
      ccmFirstClockReducedGoodTowerMass L)

/-- Exact cancellation law after complete prime-power tower collapse. -/
theorem pi_mul_ccmPublishedSourceSineCoefficient_eq_neg_reducedMassDeficit
    {L : ℝ} (hL : 0 < L) :
    Real.pi * ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) =
      -ccmFirstClockReducedMassDeficit L := by
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  rw [pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime
      hL hperiod,
    ccmFirstClockPrimeSineMass_eq_reducedGood_sub_bad,
    ccmFirstClockReducedMassDeficit]
  ring

/-- A pointwise lower floor for the literal CCM source is exactly the matching upper ceiling
for the reduced positive-mass deficit. -/
theorem ccmPublishedSourceSineCoefficient_lowerBound_iff_reducedMassDeficit_upperBound
    {C L : ℝ} (hL : Real.pi / 2 ≤ L) :
    -C ≤ ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L) ↔
      ccmFirstClockReducedMassDeficit L ≤ Real.pi * C := by
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) hL
  have hid :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_neg_reducedMassDeficit hLpos
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- The reduced bad-over-good mass deficit has a fixed ceiling on some physical aperture tail. -/
def CCMFirstClockReducedMassDeficitEventuallyBoundedAbove : Prop :=
  ∃ C A : ℝ, 0 ≤ C ∧ Real.pi / 2 ≤ A ∧
    ∀ L : ℝ, A ≤ L →
      ccmFirstClockReducedMassDeficit L ≤ Real.pi * C

/-- Exact equivalence between the source lower floor and the reduced mass-deficit ceiling. -/
theorem ccmFirstClockReducedMassDeficitEventuallyBoundedAbove_iff_sourceEventuallyBoundedBelow :
    CCMFirstClockReducedMassDeficitEventuallyBoundedAbove ↔
      CCMFirstClockPublishedSourceEventuallyBoundedBelow := by
  constructor
  · rintro ⟨C, A, hC, hA, hdeficit⟩
    refine ⟨C, A, hC, hA, ?_⟩
    intro L hAL
    exact
      (ccmPublishedSourceSineCoefficient_lowerBound_iff_reducedMassDeficit_upperBound
        (hA.trans hAL)).2 (hdeficit L hAL)
  · rintro ⟨C, A, hC, hA, hsource⟩
    refine ⟨C, A, hC, hA, ?_⟩
    intro L hAL
    exact
      (ccmPublishedSourceSineCoefficient_lowerBound_iff_reducedMassDeficit_upperBound
        (hA.trans hAL)).1 (hsource L hAL)

/-- **Literal CCM lower-floor classification.**  A uniform `O(1)` ceiling on the excess of
outer-prime/exceptional bad mass over archimedean and stable-tower mass is exactly RH. -/
theorem ccmFirstClockReducedMassDeficitEventuallyBoundedAbove_iff_rh :
    CCMFirstClockReducedMassDeficitEventuallyBoundedAbove ↔ RiemannHypothesis := by
  rw [ccmFirstClockReducedMassDeficitEventuallyBoundedAbove_iff_sourceEventuallyBoundedBelow,
    ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh]

/-- Under failure of RH the reduced bad-over-good mass deficit exceeds every fixed nonnegative
ceiling on every physical aperture tail. -/
theorem not_rh_implies_ccmFirstClockReducedMassDeficit_unboundedAbove_on_every_tail
    (hRH : ¬ RiemannHypothesis) (C A : ℝ)
    (hC : 0 ≤ C) (hA : Real.pi / 2 ≤ A) :
    ∃ L : ℝ, A ≤ L ∧
      Real.pi * C < ccmFirstClockReducedMassDeficit L := by
  obtain ⟨L, hAL, hsource⟩ :=
    not_rh_implies_ccmFirstClockPublishedSource_unboundedBelow_on_every_tail
      hRH C A hC hA
  refine ⟨L, hAL, ?_⟩
  have hLpos : 0 < L :=
    lt_of_lt_of_le (by positivity : 0 < Real.pi / 2) (hA.trans hAL)
  have hid :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_neg_reducedMassDeficit hLpos
  nlinarith [Real.pi_pos]

end

end RHTower
