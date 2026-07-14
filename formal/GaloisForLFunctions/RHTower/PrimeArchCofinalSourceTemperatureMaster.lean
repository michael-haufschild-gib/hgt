import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffQuadrantRH
import GaloisForLFunctions.RHTower.PrimeArchThetaHankelDegreeTail
import GaloisForLFunctions.RHTower.XiThermalProjectiveFreeEnergyRadius
import GaloisForLFunctions.RHTower.PrimeArchConnesReflectionMain

/-!
# Cofinal prime-source, Hausdorff, and zero-temperature master theorem

The endpoint prime-polar source, a deep calibrated Hausdorff quadrant, and one simultaneous
finite-volume/zero-temperature section carry the same transverse Xi datum.  The finite thermal
partition has an exact free-energy rate equal to the horizontal support radius.  At the critical
value, uniform boundedness may be weakened all the way to subexponential growth; this is still
equivalent to the source endpoint, positivity in the fixed Eisenstein-at-two chamber on any
infinite sparse set of Hankel degrees, local finite KMS/Wightman closure, Connes reflection
positivity, and RH.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **Cofinal source--temperature master theorem.**  For every simultaneous cofinal finite-system
and cooling schedule, the normalized logarithmic partition converges to the exact projective
reflection radius.  At radius zero the arithmetic endpoint, a single deep Hausdorff quadrant,
irreducible Eisenstein Hankel positivity on any infinite degree set, zero free-energy density,
subexponential finite-system growth, recurrent boundedness, finite KMS closure, and Connes
reflection positivity are one condition. -/
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
    let subexponential : Prop :=
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        Z j ≤ Real.exp (epsilon * (cold j : ℝ))
    let recurrentBound : Prop := ∃ C : ℝ, ∃ᶠ j : ℕ in atTop, Z j ≤ C
    Tendsto F atTop (nhds xiProjectiveReflectionRadius) ∧
    (sourceEndpoint ↔ sparseEisensteinEndpoint) ∧
    (sparseEisensteinEndpoint ↔ hausdorffEndpoint) ∧
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
  have hsourceQuadrant :
      LSeries.abscissaOfAbsConv
            (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
        CofinalScaledHausdorffQuadrantNonnegative
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment :=
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_cofinalHausdorffQuadrant
      hL hN
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
    hsparse.trans hquadrant.symm,
    hquadrant.trans hfree, hfree.symm.trans hsub,
    hsub.symm.trans hfreq, hfreq.symm.trans hKMS.symm,
    hKMS.trans hgram.symm, hgram⟩

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
