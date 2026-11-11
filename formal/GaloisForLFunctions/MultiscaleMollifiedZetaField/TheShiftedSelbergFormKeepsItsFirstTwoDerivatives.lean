import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCoupledShiftedSelbergFormHasThePolynomialLimit
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedPolynomialJetsConverge

/-!
# The first two derivatives of the literal shifted Selberg form

The Euler identity holds off the coupled line, so its directional
derivatives are the derivatives of the original finite Möbius–gcd sum.
The corrected polynomial jet limits therefore apply to that sum itself.
-/

open Filter Topology Polynomial

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

theorem shiftedSelbergProfileForm_eq_correctedProfileJetSum
    (P : ℝ → ℝ) (N : ℕ) (c v : ℝ) :
    shiftedSelbergProfileForm P N c v = correctedProfileJetSum P P N c v 0 0 := by
  rw [shiftedSelbergProfileForm_eq_corrected]
  simp only [correctedProfileJetSum, realNormalizedCorrectionCoeffJet_zero]

/-- Literal first and second directional derivatives of the finite gcd sum. -/
theorem shiftedSelbergProfileForm_derivatives (P : ℝ → ℝ) (N : ℕ) (c v κ ν : ℝ) :
    deriv (fun z => shiftedSelbergProfileForm P N (c + κ * z) (v + ν * z)) 0 =
      correctedProfileFirstJet P P N c v κ ν 0 0 ∧
    iteratedDeriv 2 (fun z => shiftedSelbergProfileForm P N (c + κ * z) (v + ν * z)) 0 =
      correctedProfileSecondJet P P N c v κ ν 0 0 := by
  simp_rw [shiftedSelbergProfileForm_eq_correctedProfileJetSum]
  exact correctedProfile_derivatives P P N 0 0 c v κ ν

/-- The first frozen-direction derivative has its polynomial integral limit. -/
theorem tendsto_shiftedSelbergProfileForm_deriv (P : ℝ[X]) (hP : P.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (κ ν : ℝ) :
    Tendsto (fun N => deriv (fun z =>
      shiftedSelbergProfileForm P.eval N (-2 * v N + κ * z) (v N + ν * z)) 0)
      atTop (𝓝 (polynomialProfileFirstLimit P P v₀ κ ν 0)) := by
  have he (N : ℕ) := (shiftedSelbergProfileForm_derivatives P.eval N (-2 * v N) (v N) κ ν).1
  simp_rw [he]
  exact tendsto_correctedProfileFirstJet P P hP hP hv κ ν 0

/-- The second frozen-direction derivative has its polynomial integral limit. -/
theorem tendsto_shiftedSelbergProfileForm_iteratedDeriv_two (P : ℝ[X]) (hP : P.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (κ ν : ℝ) :
    Tendsto (fun N => iteratedDeriv 2 (fun z =>
      shiftedSelbergProfileForm P.eval N (-2 * v N + κ * z) (v N + ν * z)) 0)
      atTop (𝓝 (polynomialProfileSecondLimit P P v₀ κ ν 0)) := by
  have he (N : ℕ) := (shiftedSelbergProfileForm_derivatives P.eval N (-2 * v N) (v N) κ ν).2
  simp_rw [he]
  exact tendsto_correctedProfileSecondJet P P hP hP hv κ ν 0

end GaloisForLFunctions.MultiscaleMollifiedZetaField
