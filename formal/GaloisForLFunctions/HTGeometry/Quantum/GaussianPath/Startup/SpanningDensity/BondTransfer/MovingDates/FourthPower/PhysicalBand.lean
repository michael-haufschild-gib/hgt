import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.MergerSlack.RepeatPrice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.ForestPacking.PhysicalDensity

/-! # A single physical fourth-power band from a polynomial date through time one -/
open Filter MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit FixedHorizon RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- On almost every infinite draw, every sufficiently long prefix pays
more than one full sweep plus order K t⁴, uniformly from a date of
order K⁻³⁄⁶⁴ through time one. -/
theorem gaussian_polynomial_fourth_power_band :
    ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let s := (1/(j:ℝ))^12
      0<s ∧ s≤1 ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 ∧
        ∀ t∈Icc s 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
          (1+b*t^4)*((n+1:ℕ):ℝ)<(k:ℝ) := by
  obtain ⟨c,hc,hrep⟩ := gaussian_fourth_power_repeats
  exact polynomial_band_of_repeats (by decide : 4≤8) hc hrep

#print axioms gaussian_polynomial_fourth_power_band
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
