import GaloisForLFunctions.RHTower.PrimeArchCofinalSourceTemperatureMaster
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetKMSMaster

/-!
# Cofinal thermal sections are governed by one exact orientation charge

The cofinal source--temperature theorem identifies every cofinal finite-volume/cooling section
with RH through its zero free-energy rate, subexponential growth, and recurrent boundedness.  The
exact off-line-quartet theorem identifies RH with vanishing of one intrinsic thermal orientation
energy.  Combining the two shows that this single, schedule-independent scalar charge governs
every cofinal two-scale thermal section, as well as the source-pure positive-frequency threshold.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **Cofinal orientation-charge universality.**  Vanishing of the exact quartet thermal
orientation charge is equivalent to the cofinal Bernstein defect, the source-pure response above
four, and each of the three asymptotic regimes of every simultaneous cofinal finite-system and
cooling schedule.  Thus changing either cofinal schedule creates no new zero-temperature phase
criterion. -/
theorem primeArchCofinalOrientationChargeUniversality
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    (CofinalHausdorffBernsteinNegativeMassVanishing
        primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
      xiThermalOrientationEnergy = 0) ∧
    (ContinuedPrimeArchPositiveFrequencyAbove 4 ↔
      xiThermalOrientationEnergy = 0) ∧
    (xiThermalOrientationEnergy = 0 ↔
      Tendsto
        (fun j : ℕ =>
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ))
        atTop (nhds 0)) ∧
    (xiThermalOrientationEnergy = 0 ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤
          Real.exp (epsilon * (cold j : ℝ))) ∧
    (xiThermalOrientationEnergy = 0 ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C) := by
  have horientation : xiThermalOrientationEnergy = 0 ↔ RiemannHypothesis :=
    xiThermalOrientationEnergy_eq_zero_iff_rh
  have hcofinal :
      CofinalHausdorffBernsteinNegativeMassVanishing
          primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ↔
        RiemannHypothesis :=
    cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis
  have hfree : RiemannHypothesis ↔
      Tendsto
        (fun j : ℕ =>
          Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
            (cold j : ℝ))
        atTop (nhds 0) :=
    riemannHypothesis_iff_tendsto_thermalProjectiveCofinalFreeEnergy_zero
      size cold hsize hcold
  have hsub : RiemannHypothesis ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤
          Real.exp (epsilon * (cold j : ℝ)) :=
    riemannHypothesis_iff_thermalProjectiveCofinalSubexponential
      size cold hsize hcold
  have hfrequent : RiemannHypothesis ↔
      ∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
        xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C :=
    riemannHypothesis_iff_exists_frequently_bounded_thermalProjectiveCofinalSection
      size cold hsize hcold
  exact ⟨hcofinal.trans horientation.symm,
    continuedPrimeArchPositiveFrequencyAbove_four_iff_cofinalBernsteinNegativeMass.trans
      (hcofinal.trans horientation.symm),
    horientation.trans hfree,
    horientation.trans hsub,
    horientation.trans hfrequent⟩

end

end RHTower
