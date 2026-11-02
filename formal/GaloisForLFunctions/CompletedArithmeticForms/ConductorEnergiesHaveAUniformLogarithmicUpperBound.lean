import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheOverlapThatResolvesATwistIsAnExactThreshold

/-!
# A logarithmic conductor bound uniform in overlap

Monotonicity reduces every overlap at least one to the bound at overlap one.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Completed conductor energy grows at most logarithmically in the conductor,
uniformly over all overlaps at least one. -/
theorem completedConductorEnergy_le_logarithmic_uniform {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m ≤
      |completeWeilSelfFinitePart φ 1| + 2 * Real.log m + 3 := by
  have hmono := completedConductorEnergy_anti hφ hsupp hM zero_lt_one hc hm
  have hone := completedConductorEnergy_le_of_one_le hφ hsupp hM (le_refl (1 : ℝ)) hm
  simp only [one_pow, mul_one] at hone
  exact hmono.trans hone

#print axioms completedConductorEnergy_le_logarithmic_uniform

end GaloisForLFunctions.CompletedArithmeticForms
