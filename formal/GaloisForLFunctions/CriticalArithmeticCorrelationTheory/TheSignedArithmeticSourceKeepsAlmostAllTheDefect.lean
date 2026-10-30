import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.DirectedPrimeRowsPreserveTheDefect
import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleIsInfinitesimalRelativeToThePrimeDefect

/-!
# The signed arithmetic source retains almost all the prime defect

The sharp ratio-prime counterterm, directed non-ratio rows, and the exact
pole moments are combined before taking a lower bound. At every fixed
overlap, each error spends an arbitrarily small share of the prime-edge
defect. The remainder is uniformly bounded by coefficient mass.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology RHTower
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics

/-- The full prime and pole source after adding the logarithmic counterterm. -/
def overlapArithmeticEnergy (g : ℝ → ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  overlapPrimeEnergy g N x +
    2 * ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N x g u * Real.exp (u / 2))) / (∫ u, g u ^ 2)

/-- Uniform mass cost after dividing a prescribed defect loss among the three source bounds. -/
def arithmeticRelativeCost (K ε : ℝ) : ℝ :=
  ε / 3 + nonRatioRelativeCost K (ε / 3) + poleRelativeCost K (ε / 3) -
    Real.eulerMascheroniConstant

/-- Every fraction below one of the prime defect survives in the actual signed
arithmetic source, uniformly over widths, compact profiles, and signed packets. -/
theorem eventually_overlapArithmeticEnergy_ge_defect {K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℝ, 0 < w → w ≤ 1 → w ≤ K / N →
      ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      (∀ u, u ∉ Set.Icc 0 w → g u = 0) → 0 < ∫ u, g u ^ 2 →
      ∀ x : ℕ → ℝ,
        (1 - ε) * poleDefect N x - arithmeticRelativeCost K ε *
          (∑ n ∈ Icc 1 N, x n ^ 2) ≤ overlapArithmeticEnergy g N x := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε3
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 3]
    with N hN₀' hN w hw0 hw1 hwK g hg hgc hsupp hG x
  have hr := hN₀ N hN₀' x
  have hn := (div_le_iff₀ hG).mpr (by
    simpa only [mul_comm (∫ u, g u ^ 2)] using
      abs_nonRatioForm_le_relative_defect hg hgc hsupp hw0.le hw1 hK hε3
        (by omega : 1 ≤ N) hwK x)
  have hnr := (div_le_div_of_nonneg_right (le_abs_self (nonRatioForm g N x)) hG.le).trans hn
  have hpole : -(ε / 3 * poleDefect N x +
        poleRelativeCost K (ε / 3) * ∑ n ∈ Icc 1 N, x n ^ 2) ≤
      2 * ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        (∫ u, atomicTest N x g u * Real.exp (u / 2))) / (∫ u, g u ^ 2) := by
    apply (le_div_iff₀ hG).mpr
    have habs := two_mul_abs_poleMoments_le_relative_defect
      hg hgc hsupp hw0 hw1 hε3 hN hwK x
    have hsign := neg_abs_le ((∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
      (∫ u, atomicTest N x g u * Real.exp (u / 2)))
    nlinarith only [habs, hsign]
  have heq : primeSum (atomicTest N x g) / (∫ u, g u ^ 2) =
      atomicWeilForm N x + nonRatioForm g N x / (∫ u, g u ^ 2) := by
    rw [primeSum_atomicTest_eq_ratio_add hg hgc hsupp hw0.le]
    field_simp [hG.ne']
  unfold overlapArithmeticEnergy overlapPrimeEnergy arithmeticRelativeCost
  rw [heq]
  linarith only [hr, hnr, hpole]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_overlapArithmeticEnergy_ge_defect
