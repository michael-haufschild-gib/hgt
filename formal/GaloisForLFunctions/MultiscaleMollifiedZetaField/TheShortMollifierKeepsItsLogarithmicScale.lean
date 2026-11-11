import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff
import GaloisForLFunctions.RHTower.LevinsonShiftedLinearMollifier

/-!
# The short cutoff and one admissible coefficient family

Taking the natural floor preserves the exponent `13/50` on the logarithmic
scale. The shifted linear mollifier at `R/log U` has unit head, real
coefficients, and the polynomial mass bound required by the dyadic gate.
-/

open Complex Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The integer cutoff at the selected sub-square-root exponent. -/
def shortLevinsonCutoff (U : ℝ) : ℕ := ⌊U ^ (13 / 50 : ℝ)⌋₊

/-- Coefficients fixed at the upper-height displacement before the gate chooses its abscissa. -/
def shortLevinsonCoefficients (R U : ℝ) : ℕ → ℂ :=
  levinsonShiftedLinearMollifierCoeff (shortLevinsonCutoff U) (1 / 2 - R / Real.log U)

/-- An explicit admissible mass bound for these coefficients. -/
def shortLevinsonCoefficientMass (U : ℝ) : ℝ :=
  ((shortLevinsonCutoff U + 1 : ℕ) : ℝ) ^ 5

theorem tendsto_shortLevinsonCutoff : Tendsto shortLevinsonCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 50))

/-- The floor does not change the normalized logarithmic length. -/
theorem tendsto_log_shortLevinsonCutoff_div_log :
    Tendsto (fun U => Real.log (shortLevinsonCutoff U : ℝ) / Real.log U) atTop (𝓝 (13 / 50 : ℝ)) := by
  have hp := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 50)
  have hh := (Sieve.tendsto_log_natFloor_div_log_one.comp hp).mul_const (13 / 50 : ℝ)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with U hU
  have hU0 : 0 < U := by linarith only [hU]
  have hlog : Real.log U ≠ 0 := (Real.log_pos (by linarith only [hU])).ne'
  dsimp only [shortLevinsonCutoff, Function.comp_def]
  rw [Real.log_rpow hU0]
  field_simp [hlog]
  ring

/-- The cutoff stays below the upper edge with room for the gate's mass bound. -/
theorem eventually_shortLevinsonCutoff_add_one_le :
    ∀ᶠ U : ℝ in atTop, ((shortLevinsonCutoff U + 1 : ℕ) : ℝ) ≤ U - 1 := by
  have hp : Tendsto (fun U : ℝ => U ^ (13 / 50 : ℝ) / U) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 37 / 50)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    rw [show -(37 / 50 : ℝ) = 13 / 50 - 1 by norm_num, Real.rpow_sub hU, Real.rpow_one]
  filter_upwards [hp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (4 : ℝ)] with U hratio hU
  have hU0 : 0 < U := by linarith only [hU]
  have hpow := (div_lt_iff₀ hU0).mp hratio
  have hfloor : (shortLevinsonCutoff U : ℝ) ≤ U ^ (13 / 50 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hU0.le _)
  push_cast
  linarith only [hpow, hfloor, hU]

/-- One explicit family satisfies every coefficient condition of the dyadic gate. -/
theorem eventually_shortLevinsonCoefficients_admissible (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ U : ℝ in atTop,
      1 ≤ shortLevinsonCutoff U ∧ shortLevinsonCoefficients R U 1 = 1 ∧
      (∀ n ∈ Finset.Icc 1 (shortLevinsonCutoff U), ‖shortLevinsonCoefficients R U n‖ ≤ 1) ∧
      (∀ n ∈ Finset.Icc 1 (shortLevinsonCutoff U),
        (starRingEnd ℂ) (shortLevinsonCoefficients R U n) = shortLevinsonCoefficients R U n) ∧
      1 ≤ shortLevinsonCoefficientMass U ∧
      (∑ n ∈ Finset.Icc 1 (shortLevinsonCutoff U),
        ‖shortLevinsonCoefficients R U n‖ * (n : ℝ) ^ (4 : ℝ)) ≤ shortLevinsonCoefficientMass U ∧
      Real.log (shortLevinsonCoefficientMass U) ≤ 5 * Real.log (U - 1) := by
  filter_upwards [tendsto_shortLevinsonCutoff.eventually_ge_atTop 2,
    eventually_shortLevinsonCutoff_add_one_le, eventually_ge_atTop (4 : ℝ)] with U hN hNU hU
  have hN' : 1 < shortLevinsonCutoff U := by omega
  have hLU : 0 < Real.log U := Real.log_pos (by linarith only [hU])
  have hσ : 1 / 2 - R / Real.log U ≤ 1 / 2 := sub_le_self _ (div_nonneg hR hLU.le)
  have hM1 : (1 : ℝ) ≤ ((shortLevinsonCutoff U + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ shortLevinsonCutoff U + 1 by omega)
  refine ⟨by omega, levinsonShiftedLinearMollifierCoeff_one hN' _, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact norm_levinsonShiftedLinearMollifierCoeff_le_one hN' (Finset.mem_Icc.mp hn).1 hσ
  · intro n _
    exact star_levinsonShiftedLinearMollifierCoeff _ _ n
  · exact one_le_pow₀ hM1
  · exact sum_norm_levinsonShiftedLinearMollifierCoeff_mul_pow_four_le hN' hσ
  · unfold shortLevinsonCoefficientMass
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans_le hM1) hNU) (by norm_num)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
