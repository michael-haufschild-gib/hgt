import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeResidueHasASignedPolarLimit
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCanonicalCriticalClockEntersFromTheNegativeSide

/-!
# The critical upward-prime residue is supported at the pole

Every positive critical ratio has the same signed, rank-one upward-prime
residue on fixed conductor pairs. This individual-channel limit imposes
no upper bound on the ratio and asserts no sign for the complete form.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CompletedArithmeticForms
  RenormalizedIntersectionTheory

/-- The signed upward-prime residue at every positive critical ratio. -/
theorem tendsto_critical_upwardPrime_residual {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (Real.log N / c N) *
      ⟪upwardPrimeVector φ (c N) N (normalizedRamanujanHorizonVector m N) -
          shellCorrection φ (c N) m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫) atTop
      (𝓝 (if m = 1 ∧ l = 1 then -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (Real.eulerMascheroniConstant + 1) else 0)) := by
  exact tendsto_upwardPrime_residual_signed_limit hφ hsupp hM hc
    (criticalCurve_facts hc hR hcrit).1
    (criticalCurve_pow_log_div_natCast hc hR hcrit 4 2) hm hl

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_critical_upwardPrime_residual
