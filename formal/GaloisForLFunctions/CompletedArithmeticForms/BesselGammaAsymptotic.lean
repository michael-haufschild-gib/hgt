import GaloisForLFunctions.CompletedArithmeticForms.BesselSharpPrefix
import GaloisForLFunctions.CompletedArithmeticForms.GammaQuarterFloor
import Mathlib.Analysis.SpecificLimits.Basic

/-!+# The natural Gamma asymptotic of a fixed radial tail

The complete Mellin mass has an exact Gamma recurrence. The finite
prefix costs one frequency power, while the quarter-line reserve pays
two. Their quotient therefore has an explicit inverse-frequency error.
-/

open Complex Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The Gamma weight carried by the highest radial power. -/
def besselNaturalGammaWeight (τ : ℝ) : ℝ :=
  ‖Complex.Gamma ((9 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2

theorem besselNaturalGammaWeight_pos {τ : ℝ} (hτ : 1 ≤ τ) :
    0 < besselNaturalGammaWeight τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  exact lt_of_lt_of_le (mul_pos (mul_pos gammaQuarterReserve_pos (sq_pos_of_pos hτ0))
    (Real.exp_pos _)) (gammaQuarterReserve_mul_sq_exp_le hτ)

/-- A single Gamma recurrence identifies the lower complete mass exactly. -/
theorem besselNaturalGammaWeight_recurrence (τ : ℝ) :
    besselNaturalGammaWeight τ = (τ ^ 2 + 25 / 16) *
      ‖Complex.Gamma ((5 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  have hz : (5 / 4 : ℂ) + (τ : ℂ) * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hG := Complex.Gamma_add_one ((5 / 4 : ℂ) + (τ : ℂ) * I) hz
  rw [show (5 / 4 : ℂ) + (τ : ℂ) * I + 1 = (9 / 4 : ℂ) + (τ : ℂ) * I by ring] at hG
  unfold besselNaturalGammaWeight
  rw [hG, norm_mul, mul_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  <;> ring

private theorem normalized_zero_mass {τ : ℝ} (hτ : 1 ≤ τ) :
    besselFirstAtomTailDensity τ 0 / besselNaturalGammaWeight τ =
      1 - (3 / 2 : ℝ) / (τ ^ 2 + 25 / 16) := by
  have hW := besselNaturalGammaWeight_pos hτ
  have hD : 0 < τ ^ 2 + (25 / 16 : ℝ) := by positivity
  have hr := besselNaturalGammaWeight_recurrence τ
  rw [besselFirstAtomTailDensity_zero_eq]
  change (besselNaturalGammaWeight τ - (3 / 2 : ℝ) *
    ‖Complex.Gamma ((5 / 4 : ℂ) + (τ : ℂ) * I)‖ ^ 2) / _ = _
  field_simp [hW.ne', hD.ne']
  nlinarith only [hr]

/-- Every fixed positive cutoff has an explicit inverse-frequency normalized error. -/
theorem abs_besselFirstAtomTailDensity_div_gamma_sub_one_le {q τ : ℝ}
    (hq : 0 < q) (hτ : 1 ≤ τ) :
    |besselFirstAtomTailDensity τ q / besselNaturalGammaWeight τ - 1| ≤
      (3 * besselDensityPrefixCost q / gammaQuarterReserve + 3 / 2) / τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by norm_num) hτ
  have hC := besselDensityPrefixCost_nonneg hq.le
  have hg := gammaQuarterReserve_pos
  have hW := besselNaturalGammaWeight_pos hτ
  have hprefix := abs_besselFirstAtomTailDensity_sub_zero_le hq hτ0.le
  have hfloor := gammaQuarterReserve_mul_sq_exp_le hτ
  have hpay := mul_le_mul_of_nonneg_left hfloor
    (by positivity : 0 ≤ 3 * besselDensityPrefixCost q / (gammaQuarterReserve * τ))
  have hcancel : (3 * besselDensityPrefixCost q / (gammaQuarterReserve * τ)) *
      (gammaQuarterReserve * τ ^ 2 * Real.exp (-Real.pi * τ)) =
        3 * besselDensityPrefixCost q * τ * Real.exp (-Real.pi * τ) := by
    field_simp [hg.ne', hτ0.ne']
  rw [hcancel] at hpay
  have hsmall : |(besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0) /
      besselNaturalGammaWeight τ| ≤ 3 * besselDensityPrefixCost q / (gammaQuarterReserve * τ) := by
    rw [abs_div, abs_of_pos hW]
    apply (div_le_iff₀ hW).mpr
    refine (hprefix.trans ?_).trans hpay
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    nlinarith only [mul_nonneg hC (sub_nonneg.mpr hτ)]
  have hD : 0 < τ ^ 2 + (25 / 16 : ℝ) := by positivity
  have hterm : (3 / 2 : ℝ) / (τ ^ 2 + 25 / 16) ≤ (3 / 2 : ℝ) / τ := by
    apply div_le_div_of_nonneg_left (by norm_num) hτ0
    nlinarith only [hτ, sq_nonneg (τ - 1)]
  have he : besselFirstAtomTailDensity τ q / besselNaturalGammaWeight τ - 1 =
      (besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0) /
        besselNaturalGammaWeight τ - (3 / 2 : ℝ) / (τ ^ 2 + 25 / 16) := by
    rw [sub_div, normalized_zero_mass hτ]
    ring
  rw [he]
  calc
    _ ≤ |(besselFirstAtomTailDensity τ q - besselFirstAtomTailDensity τ 0) /
        besselNaturalGammaWeight τ| + |(3 / 2 : ℝ) / (τ ^ 2 + 25 / 16)| := abs_sub _ _
    _ ≤ 3 * besselDensityPrefixCost q / (gammaQuarterReserve * τ) + (3 / 2 : ℝ) / τ := by
      rw [abs_of_pos (div_pos (by norm_num) hD)]
      exact add_le_add hsmall hterm
    _ = _ := by ring

/-- A fixed radial cutoff retains asymptotically the full natural Gamma mass. -/
theorem tendsto_besselFirstAtomTailDensity_div_gamma {q : ℝ} (hq : 0 < q) :
    Tendsto (fun τ => besselFirstAtomTailDensity τ q / besselNaturalGammaWeight τ)
      atTop (𝓝 1) := by
  have hlim : Tendsto (fun τ : ℝ =>
      (3 * besselDensityPrefixCost q / gammaQuarterReserve + 3 / 2) / τ) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun τ : ℝ => τ⁻¹) atTop (𝓝 0)).const_mul
        (3 * besselDensityPrefixCost q / gammaQuarterReserve + 3 / 2)
  have hz : Tendsto (fun τ => besselFirstAtomTailDensity τ q /
      besselNaturalGammaWeight τ - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with τ hτ
    simpa only [Real.norm_eq_abs] using abs_besselFirstAtomTailDensity_div_gamma_sub_one_le hq hτ
  have hh := hz.add_const 1
  simpa only [sub_add_cancel, zero_add] using hh

#print axioms abs_besselFirstAtomTailDensity_div_gamma_sub_one_le
#print axioms tendsto_besselFirstAtomTailDensity_div_gamma

end GaloisForLFunctions.CompletedArithmeticForms
