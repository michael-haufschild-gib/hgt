import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffDiagonalRH
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail
import GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius
import GaloisForLFunctions.RHTower.PrimeArchConnesReflectionMain
import GaloisForLFunctions.RHTower.PrimeArchVerifiedHeightAccretivity
import GaloisForLFunctions.RHTower.PrimeArchBernsteinPencil
import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase
import GaloisForLFunctions.RHTower.PrimeArchBernsteinNegativeMassAbscissa

/-!
# Cofinal prime-source, Hausdorff, and zero-temperature master theorem

The endpoint prime-polar source, a scalar cofinal Bernstein negativity defect, a deep calibrated
Hausdorff quadrant, and one simultaneous finite-volume/zero-temperature section carry the same
transverse Xi datum.  The finite thermal partition has an exact free-energy rate equal to the
horizontal support radius.  At the critical value, uniform boundedness may be weakened all the
way to subexponential growth; pointwise Hausdorff positivity may be weakened to vanishing total
negative Bernstein mass along one cofinal degree schedule.  These are still equivalent to the
source endpoint, positivity in the fixed Eisenstein-at-two chamber on any infinite sparse set of
Hankel degrees, local finite KMS/Wightman closure, Connes reflection positivity, and RH.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **Cofinal source--temperature master theorem.**  For every simultaneous cofinal finite-system
and cooling schedule, the normalized logarithmic partition converges to the exact projective
reflection radius.  At radius zero the arithmetic endpoint, irreducible Eisenstein Hankel
positivity on any infinite degree set, arbitrarily large positive complete Hausdorff diagonals,
cofinal vanishing of the aggregate negative Bernstein mass, a single deep Hausdorff quadrant,
zero free-energy density, subexponential finite-system growth, recurrent boundedness, finite KMS
closure, and Connes reflection positivity are one condition. -/
theorem primeArchCofinalSourceTemperatureMaster
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop)
    {D : Set ℕ} (hD : D.Infinite)
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    let Z : ℕ → ℝ := fun j =>
      xiThermalProjectiveColdTruncation (size j) (cold j)
    let F : ℕ → ℝ := fun j => Real.log (Z j) / (cold j : ℝ)
    let sourceEndpoint : Prop :=
      LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal)
    let hausdorffEndpoint : Prop :=
      CofinalScaledHausdorffQuadrantNonnegative
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment
    let sparseEisensteinEndpoint : Prop :=
      PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D
    let cofinalDiagonalEndpoint : Prop :=
      CofinalScaledHausdorffDiagonalsNonnegative
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment
    let aggregateNegativeMassEndpoint : Prop :=
      CofinalHausdorffBernsteinNegativeMassVanishing
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment
    let exactBernsteinZeroEndpoint : Prop :=
      ∀ N : ℕ,
        hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) N = 0
    let exactBernsteinOrderUnitEndpoint : Prop :=
      ∀ N : ℕ,
        bernsteinCoefficientL1
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) (N + 1) =
          normalizedPrimeArchMoment 0
    let bernsteinSubexponentialEndpoint : Prop :=
      SubexponentialAtNatInfinity primeArchEndpointBernsteinTotalVariation
    let bernsteinNegativeMassSubexponentialEndpoint : Prop :=
      PrimeArchBernsteinNegativeMassSubexponential
    let subexponential : Prop :=
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        Z j ≤ Real.exp (epsilon * (cold j : ℝ))
    let recurrentBound : Prop := ∃ C : ℝ, ∃ᶠ j : ℕ in atTop, Z j ≤ C
    Tendsto F atTop (nhds xiProjectiveReflectionRadius) ∧
    (sourceEndpoint ↔ sparseEisensteinEndpoint) ∧
    (sparseEisensteinEndpoint ↔ cofinalDiagonalEndpoint) ∧
    (cofinalDiagonalEndpoint ↔ aggregateNegativeMassEndpoint) ∧
    (aggregateNegativeMassEndpoint ↔ exactBernsteinZeroEndpoint) ∧
    (exactBernsteinZeroEndpoint ↔ exactBernsteinOrderUnitEndpoint) ∧
    (exactBernsteinOrderUnitEndpoint ↔ bernsteinSubexponentialEndpoint) ∧
    (bernsteinSubexponentialEndpoint ↔
      bernsteinNegativeMassSubexponentialEndpoint) ∧
    (bernsteinNegativeMassSubexponentialEndpoint ↔ hausdorffEndpoint) ∧
    (hausdorffEndpoint ↔ Tendsto F atTop (nhds 0)) ∧
    (Tendsto F atTop (nhds 0) ↔ subexponential) ∧
    (subexponential ↔ recurrentBound) ∧
    (recurrentBound ↔ PrimeArchFiniteKMSWightmanLocalMomentClosure) ∧
    (PrimeArchFiniteKMSWightmanLocalMomentClosure ↔
      PrimeArchComplexReflectionPositiveGram) ∧
    (PrimeArchComplexReflectionPositiveGram ↔ RiemannHypothesis) := by
  dsimp only
  let F : ℕ → ℝ := fun j =>
    Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
      (cold j : ℝ)
  have hrate : Tendsto F atTop (nhds xiProjectiveReflectionRadius) :=
    tendsto_xiThermalProjectiveColdTruncation_log_div_cold size cold hsize hcold
  have hquadrant :
      CofinalScaledHausdorffQuadrantNonnegative
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
        RiemannHypothesis :=
    cofinalScaledPrimeArchHausdorffQuadrantNonnegative_iff_riemannHypothesis
  have hsparse :
      PrimeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative D ↔
        RiemannHypothesis :=
    primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis hD
  have hdiagonal :
      CofinalScaledHausdorffDiagonalsNonnegative
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
        RiemannHypothesis :=
    cofinalScaledPrimeArchHausdorffDiagonalsNonnegative_iff_riemannHypothesis
  have hnegativeMass :
      CofinalHausdorffBernsteinNegativeMassVanishing
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
        RiemannHypothesis :=
    cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis
  have hexactMass :
      CofinalHausdorffBernsteinNegativeMassVanishing
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
        ∀ N : ℕ,
          hausdorffBernsteinNegativeMass
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) N = 0 :=
    cofinalHausdorffBernsteinNegativeMassVanishing_iff_forall_eq_zero
      primeArchEndpointHausdorffRadius normalizedPrimeArchMoment
  have hsourceQuadrant :
      LSeries.abscissaOfAbsConv
            (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
        CofinalScaledHausdorffQuadrantNonnegative
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment :=
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffQuadrant
      hL hN
  have horderUnit : RiemannHypothesis ↔
      ∀ N : ℕ,
        bernsteinCoefficientL1
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) (N + 1) =
          normalizedPrimeArchMoment 0 :=
    riemannHypothesis_iff_forall_primeArchBernsteinCoefficientL1_eq_mass
  have hbernsteinSubexponential : RiemannHypothesis ↔
      SubexponentialAtNatInfinity primeArchEndpointBernsteinTotalVariation :=
    riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential
  have hbernsteinNegativeMassSubexponential : RiemannHypothesis ↔
      PrimeArchBernsteinNegativeMassSubexponential :=
    riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential
  have hexactRH :
      (∀ N : ℕ,
          hausdorffBernsteinNegativeMass
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) N = 0) ↔
        RiemannHypothesis :=
    hexactMass.symm.trans hnegativeMass
  have hfree : RiemannHypothesis ↔ Tendsto F atTop (nhds 0) := by
    simpa only [F] using
      (riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero
        size cold hsize hcold)
  have hsub : RiemannHypothesis ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤
          Real.exp (epsilon * (cold j : ℝ)) :=
    riemannHypothesis_iff_thermalProjectiveCofinalSubexponential
      size cold hsize hcold
  have hfreq : RiemannHypothesis ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C :=
    riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveCofinalSection
      size cold hsize hcold
  have hKMS : PrimeArchFiniteKMSWightmanLocalMomentClosure ↔ RiemannHypothesis :=
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis
  have hgram : PrimeArchComplexReflectionPositiveGram ↔ RiemannHypothesis :=
    primeArchComplexReflectionPositiveGram_iff_riemannHypothesis
  refine ⟨hrate,
    hsourceQuadrant.trans (hquadrant.trans hsparse.symm),
    hsparse.trans hdiagonal.symm,
    hdiagonal.trans hnegativeMass.symm,
    hexactMass,
    hexactRH.trans horderUnit,
    horderUnit.symm.trans hbernsteinSubexponential,
    primeArchBernsteinNegativeMassSubexponential_iff_totalVariation.symm,
    hbernsteinNegativeMassSubexponential.symm.trans hquadrant.symm,
    hquadrant.trans hfree, hfree.symm.trans hsub,
    hsub.symm.trans hfreq, hfreq.symm.trans hKMS.symm,
    hKMS.trans hgram.symm, hgram⟩

/-- **Verified-prefix ultraviolet compression.**  Once the Xi divisor is known to be critical
through height `H`, the entire cofinal Hausdorff/KMS defect is equivalent to passivity only in the
remaining positive-frequency tail above any `R` with `R + 1 / 2 ≤ H`.  The verified prefix is
therefore spent exactly once: it removes the matching compact frequency band, while the scalar
aggregate negative Bernstein mass carries the undischarged tail. -/
theorem continuedPrimeArchPositiveFrequencyAbove_iff_cofinalBernsteinNegativeMass_of_verifiedHeight
    (H R : ℝ) (hverified : RHVerifiedThrough H) (hband : R + 1 / 2 ≤ H) :
    ContinuedPrimeArchPositiveFrequencyAbove R ↔
      CofinalHausdorffBernsteinNegativeMassVanishing
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment := by
  exact
    (continuedPrimeArchPositiveFrequencyAbove_iff_rh_of_verifiedHeight
      H R hverified hband).trans
      cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.symm

/-- **Scale-resolved cofinal spectrum.**  At every nonnegative horizontal scale, the arithmetic
abscissa bound and the projective support-radius bound are identical, while every cofinal thermal
section recovers that radius as its exact zero-temperature free-energy density. -/
theorem primeArchCofinalSourceTemperatureSpectrum
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop)
    {L alpha : ℝ} (hL : 0 < L) (halpha : 0 ≤ alpha) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    Tendsto
        (fun j : ℕ =>
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ))
        atTop (nhds xiProjectiveReflectionRadius) ∧
      (LSeries.abscissaOfAbsConv
            (xiRectangularPrimeGammaTailNegativeDirichletCoefficient L N) ≤
          ((1 + alpha : ℝ) : EReal) ↔
        xiProjectiveReflectionRadius ≤ alpha) := by
  exact ⟨
    tendsto_xiThermalProjectiveColdTruncation_log_div_cold size cold hsize hcold,
    primeGamma_abscissa_le_iff_projectiveReflectionRadius_le hL halpha hN⟩

end

end RHTower

namespace RHTower

/-- Unconditional ultraviolet compression at the source-pure threshold four: the signed
positive-frequency tail above four is exactly the cofinal Hausdorff/Bernstein negative-mass
vanishing.  The verified-height hypothesis is discharged by the endpoint height gap through
`9 / 2`. -/
theorem continuedPrimeArchPositiveFrequencyAbove_four_iff_cofinalBernsteinNegativeMass :
    ContinuedPrimeArchPositiveFrequencyAbove 4 ↔
      CofinalHausdorffBernsteinNegativeMassVanishing
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment :=
  continuedPrimeArchPositiveFrequencyAbove_iff_cofinalBernsteinNegativeMass_of_verifiedHeight
    (9 / 2) 4 rhVerifiedThrough_nine_halves (by norm_num)

/-- **Canonical scalar ultraviolet core.**  The apparently weaker subexponential Bernstein
negative-mass condition is exactly cofinal vanishing of that one nonnegative scalar defect. -/
theorem primeArchBernsteinNegativeMassSubexponential_iff_cofinalBernsteinNegativeMass :
    PrimeArchBernsteinNegativeMassSubexponential ↔
      CofinalHausdorffBernsteinNegativeMassVanishing
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment :=
  riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential.symm.trans
    cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.symm

/-- **Direct ultraviolet compression.**  Positive-frequency passivity above four is exactly the
same scalar Bernstein core; no thermodynamic or divisor-indexed intermediate is needed. -/
theorem primeArchBernsteinNegativeMassSubexponential_iff_positiveFrequencyAbove_four :
    PrimeArchBernsteinNegativeMassSubexponential ↔
      ContinuedPrimeArchPositiveFrequencyAbove 4 :=
  primeArchBernsteinNegativeMassSubexponential_iff_cofinalBernsteinNegativeMass.trans
    continuedPrimeArchPositiveFrequencyAbove_four_iff_cofinalBernsteinNegativeMass.symm

end RHTower
