import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilTrialEnergiesAreSimpleAndProper
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerThresholdOfTheOverlapRatioIsOne
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Self-energy at every strictly separated width ratio

The width `c/N` eventually lies below the exact logarithmic spacing for every
`0<c<1`. Compact twice differentiable profiles are Lipschitz, so the quantitative
Robin remainder applies without an additional regularity premise. Its scalar
finite part includes the Gamma constant with its exact normalization.
-/

noncomputable section

open MeasureTheory Filter Topology RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics ArithmeticLorentzianGeometry SpacingScaleHarmonicAnalysis

/-- Every fixed ratio below one eventually gives strictly separated atoms. -/
theorem eventually_div_horizon_lt_atomSpacing {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ N : ℕ in atTop, 0 < c / N ∧ c / N ≤ 1 ∧ c / N < atomSpacing N := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (c / (1 - c))
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlarge : c / (1 - c) < (N : ℝ) :=
    hN₀.trans_le (by exact_mod_cast hN)
  have hprod : c < (N : ℝ) * (1 - c) := (div_lt_iff₀ (sub_pos.mpr hc1)).mp hlarge
  refine ⟨div_pos hc0 hN0, (div_le_one hN0).mpr (hc1.le.trans hN1R), ?_⟩
  apply lt_of_lt_of_le _ (inv_succ_le_atomSpacing hN1)
  rw [div_lt_div_iff₀ hN0 (by positivity)]
  nlinarith only [hprod]

/-- The common normalized diagonal after removing its logarithmic and finite parts. -/
def completeWeilSelfError (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  2 * gammaHardyPhaseRate 0 +
    levyEnergy (atomDilate φ (c / N)) / (∫ u, atomDilate φ (c / N) u ^ 2) -
      Real.log N - (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant)

private theorem exists_profile_lipschitz {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) :
    ∃ K : ℝ, ∀ u v, |φ u - φ v| ≤ K * |u - v| := by
  have hcs : HasCompactSupport φ :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hφ (by norm_num)
  refine ⟨K, fun u v => ?_⟩
  simpa only [Real.dist_eq] using hK.dist_le_mul u v

private theorem completeWeil_self_scalar_identity (φ : ℝ → ℝ) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    2 * gammaHardyPhaseRate 0 + Real.log (1 / (c / N)) + profileRobin φ - Real.log N =
      completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (1 / (c / N)) - Real.log N = -Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hN0.ne']
    ring
  have hs : completeWeilSelfFinitePart φ c =
      -Real.log (2 * Real.pi) - Real.log c + bumpRobin φ 1 / (∫ u, φ u ^ 2) := by
    rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
      Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc.ne']
    ring
  have h := finitePart_profileRobin_eq φ
  rw [hs]
  linarith only [h, hlog]

/-- The actual normalized self-error is at most a constant times `c/N`. -/
theorem abs_completeWeilSelfError_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {N : ℕ} (hN : 1 ≤ N) :
    |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := by
  obtain ⟨K, hK⟩ := exists_profile_lipschitz hφ hsupp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr
    (hc1.le.trans (by exact_mod_cast hN))
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 hM
  have h := abs_levyEnergy_atomDilate_sub_le hφ hsupp hM hw0 hw1 hK
  have heq : completeWeilSelfError φ c N =
      (levyEnergy (atomDilate φ (c / N)) -
        (Real.log (1 / (c / N)) + profileRobin φ) *
          ∫ u, atomDilate φ (c / N) u ^ 2) / (∫ u, atomDilate φ (c / N) u ^ 2) := by
    rw [completeWeilSelfError, ← completeWeil_self_scalar_identity φ hc0 hN]
    field_simp [hG.ne']
    ring
  rw [heq, abs_div, abs_of_pos hG, div_le_iff₀ hG]
  exact h

/-- The complete self-energy has the stated finite part for every separated ratio. -/
theorem tendsto_completeWeilSelfError {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (completeWeilSelfError φ c) atTop (𝓝 0) := by
  have hw : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => Real.exp (1 / 2) / 2 * (c / N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hw.const_mul (Real.exp (1 / 2) / 2)
  have hbound : ∀ᶠ N : ℕ in atTop,
      |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact abs_completeWeilSelfError_le hφ hsupp hM hc0 hc1 hN
  have habs := squeeze_zero' (Eventually.of_forall fun N => abs_nonneg (completeWeilSelfError φ c N))
    hbound hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
