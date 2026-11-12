import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest

/-!
# Linear Fourier decay admits the full Gamma energy

The square-root bound for the Gamma bracket turns a first-order spectral
decay bound into an integrable power majorant. No smoothness or compact
support of a physical profile is required.
-/

noncomputable section
open MeasureTheory Filter

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open _root_.RHTower

/-- Continuous spectral data with first-order decay have finite Gamma energy. -/
theorem integrable_gammaEnergy_of_linear_decay {H : ℝ → ℂ} (hH : Continuous H)
    {M : ℝ} (hdec : ∀ r : ℝ, (1 + |r|) * ‖H r‖ ≤ M) :
    Integrable (fun r : ℝ => ‖H r‖ ^ 2 * EF.gammaBracket r) := by
  let C := digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi
  have hi : Integrable (fun r : ℝ =>
      M ^ 2 * (|C| + 2) * (1 + ‖r‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by norm_num)).const_mul _
  apply hi.mono'
    (((hH.norm.pow 2).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable)
  refine Eventually.of_forall fun r => ?_
  have hp : 0 < 1 + |r| := by positivity
  have hn : ‖H r‖ ≤ M / (1 + |r|) := by
    rw [le_div_iff₀ hp, mul_comm]
    exact hdec r
  have hn2 : ‖H r‖ ^ 2 ≤ M ^ 2 / (1 + |r|) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hg := WeilSpectral.abs_gammaBracket_le_sqrt r
  have hs : 1 ≤ Real.sqrt (1 + |r|) :=
    Real.one_le_sqrt.mpr (by linarith only [abs_nonneg r])
  have hg' : |EF.gammaBracket r| ≤ (|C| + 2) * Real.sqrt (1 + |r|) := by
    change |EF.gammaBracket r| ≤ C + 2 * Real.sqrt (1 + |r|) at hg
    nlinarith only [hg, hs, abs_nonneg C, le_abs_self C]
  have he : Real.sqrt (1 + |r|) / (1 + |r|) ^ 2 =
      (1 + ‖r‖) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hp]
    norm_num
  change ‖‖H r‖ ^ 2 * EF.gammaBracket r‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ M ^ 2 / (1 + |r|) ^ 2 * ((|C| + 2) * Real.sqrt (1 + |r|)) :=
      mul_le_mul hn2 hg' (abs_nonneg _) (by positivity)
    _ = M ^ 2 * (|C| + 2) * (Real.sqrt (1 + |r|) / (1 + |r|) ^ 2) := by ring
    _ = _ := by rw [he]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
