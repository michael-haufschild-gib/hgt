import GaloisForLFunctions.RHTower.CCMUnitaryPolarSourceAtlas
import GaloisForLFunctions.RHTower.ZetaStoneIsodivisorialSource

/-!
# Complete one-clock source/divisor tomography

This module closes the composition seam between the literal first CCM clock,
its crease--pole--frequency atlas, the complete centered Xi divisor and
canonical product, and the Stone-universal inverse obstruction.
-/

open CategoryTheory Topology TopologicalSpace
open Set Filter

namespace RHTower

open Complex
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

noncomputable section

/-- Exact forward content of the literal one-clock crease--pole--frequency
atlas at a positive aperture. -/
def CCMSingleClockForwardAtlas (A : ℝ) : Prop :=
  (∀ k : ℕ, 1 < k →
    ∃ d : ℝ,
      HasDerivWithinAt ccmFirstClockArithmeticTrace
        (d + ccmFirstClockPrimeEntrySlope k)
        (Set.Ici (Real.log k)) (Real.log k) ∧
      HasDerivWithinAt ccmFirstClockArithmeticTrace d
        (Set.Iic (Real.log k)) (Real.log k) ∧
      (-(Real.log k) / (2 * Real.pi) *
          ((d + ccmFirstClockPrimeEntrySlope k) - d)) *
            Real.exp (Real.log k / 2) =
        ArithmeticFunction.vonMangoldt k) ∧
  (∀ s : ℂ, 1 < s.re →
    (meromorphicOrderAt (xiRectangularWeilFullContinuation A) s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) ∧
  (∀ q : XiRightZeroCopy,
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation A)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient A q) =
      (xiRightMultiplicity q : ℂ)) ∧
  (∀ L : ℝ, Real.pi / 2 ≤ L →
    ccmFirstClockPolarSubtractedSource L =
      2 * (ccmFirstClockCriticalRationalDivisor L).re) ∧
  Continuous (fun L => 2 * xiLineScrewSeries L) ∧
  IsBohrAlmostPeriodic (fun L => 2 * xiLineScrewSeries L) ∧
  Tendsto
    (fun L => ccmFirstClockPolarSubtractedSource L -
      2 * xiLineScrewSeries L) atTop (𝓝 0) ∧
  (∀ lam : ℝ, lam ≠ 0 →
    -((lam : ℂ) ^ (2 : ℕ)) *
        bohrCoefficient
          (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
      (xiCriticalAbsoluteOrdinateMultiplicity lam : ℂ))

/-- The published first CCM clock supplies the exact forward atlas at every
positive aperture. -/
theorem ccmSingleClock_forwardAtlas
    {A : ℝ} (hA : 0 < A) :
    CCMSingleClockForwardAtlas A := by
  exact ccmFirstClockCreasePolarFrequencyAtlas hA

/-- A divisor-only observable cannot admit any source reconstruction map on
a Stone fibre containing two distinct source coordinates.  This is stronger
than failure of continuous reconstruction: no set-theoretic left inverse
exists. -/
theorem zetaStone_divisorOnlySourceReconstruction_impossible
    {Y : Type*} (observable : (ℂ → ℂ) → Y)
    (hobservable : IsPositiveHalfPlaneDivisorProfile observable)
    (S : LightProfinite) (base : S)
    (j k : Unit ⊕ Clopens (lightToProfinite.obj S))
    (hjk : j ≠ k) :
    ¬ ∃ recover : Y → (Unit ⊕ Clopens (lightToProfinite.obj S)),
        Function.LeftInverse recover
          (fun i => observable (zetaStoneContinuedSource S base i)) := by
  rintro ⟨recover, hrecover⟩
  apply hjk
  calc
    j = recover (observable (zetaStoneContinuedSource S base j)) :=
      (hrecover j).symm
    _ = recover (observable (zetaStoneContinuedSource S base k)) :=
      congrArg recover
        (zetaStone_divisorProfile_constant observable hobservable S base j k)
    _ = k := hrecover k

/-- **Complete one-clock source/divisor tomography.**  One literal first CCM
clock recovers every prime-power atom, every strict-right pole with
multiplicity, every critical ordinate with multiplicity after polar
subtraction, and hence the complete centered Xi divisor and normalized
canonical product.  Conversely, arbitrary pointed Stone recurrence chambers
occur inside a single complete-divisor fibre, and no divisor-only observable
can reconstruct two distinct source coordinates. -/
theorem ccmSingleClock_completeSourceDivisorTomography
    {A : ℝ} (hA : 0 < A) :
    CCMSingleClockForwardAtlas A ∧
    Function.Bijective xiUnitaryPolarAtlasToZeroCopy ∧
    (∀ z : ℂ,
      canonicalProductE1Indexed xiUnitaryPolarAtlasSpectralPoint z =
        xiCanonicalProduct z) ∧
    (∀ (S : LightProfinite) (base : S) (pi : ℕ ≃ Nat.Primes),
      primeRecurringPatternChamber pi (zetaStonePrimeOrientation S base) =
        pointedStoneConstraint S base) ∧
    (∀ (Y : Type*) (observable : (ℂ → ℂ) → Y),
      IsPositiveHalfPlaneDivisorProfile observable →
      ∀ (S : LightProfinite) (base : S)
        (j k : Unit ⊕ Clopens (lightToProfinite.obj S)),
        j ≠ k →
        ¬ ∃ recover : Y → (Unit ⊕ Clopens (lightToProfinite.obj S)),
            Function.LeftInverse recover
              (fun i => observable (zetaStoneContinuedSource S base i))) := by
  refine ⟨ccmSingleClock_forwardAtlas hA,
    xiUnitaryPolarAtlasEquiv.bijective,
    xiUnitaryPolarAtlasCanonicalProduct_eq, ?_, ?_⟩
  · intro S base pi
    exact zetaStone_recurringPatternChamber_eq S base pi
  · intro Y observable hobservable S base j k hjk
    exact zetaStone_divisorOnlySourceReconstruction_impossible
      observable hobservable S base j k hjk

end

end RHTower
