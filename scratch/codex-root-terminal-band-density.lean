import GaloisForLFunctions.RHTower.MobiusDivisorTerminalBandRigidity
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem tendsto_criticalContinuousAbel_log_normalized :
    Tendsto (fun M : ℕ => criticalContinuousAbel (M : ℝ) * Real.log M /
      ((M : ℝ) * Real.sqrt M)) atTop (𝓝 0) := by
  apply tendsto_sum_mobiusDivisorDilationChannel_log_normalized.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  rw [criticalContinuousAbel_nat_eq_dilation_sum M hM]

private theorem tendsto_log_div_sqrt_nat :
    Tendsto (fun M : ℕ => Real.log M / Real.sqrt M) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
    h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop)

theorem tendsto_omitted_middle_band_density_zero
    (P : ℕ → Finset ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ᶠ M : ℕ in atTop,
      ∀ p ∈ mobiusDivisorSelectionPrimes M, p * p ≤ M → p ∈ P M)
    (hcell : ∀ᶠ M : ℕ in atTop,
      ∀ p ∈ mobiusDivisorSelectionPrimes M \ P M, M ≤ 2 * p)
    (hbudget : ∀ᶠ M : ℕ in atTop,
      mobiusDivisorSelectionEnergy M (P M) ≤ C * (M : ℝ) ^ (2 : ℕ)) :
    Tendsto (fun M : ℕ =>
      ((((mobiusDivisorSelectionPrimes M \ P M).filter
        (fun p => 4 * p ≤ 3 * M)).card : ℝ) * Real.log M / (M : ℝ)))
      atTop (𝓝 0) := by
  let κ : ℝ := 2 * Real.eulerMascheroniConstant - 1
  have hκ : 0 < κ := by
    dsimp [κ]
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hsource : Tendsto (fun M : ℕ =>
      |criticalContinuousAbel (M : ℝ) * Real.log M /
        ((M : ℝ) * Real.sqrt M)|) atTop (𝓝 0) := by
    simpa using tendsto_criticalContinuousAbel_log_normalized.abs
  have hrest : Tendsto (fun M : ℕ => Real.sqrt C *
      (Real.log M / Real.sqrt M)) atTop (𝓝 0) := by
    simpa using tendsto_log_div_sqrt_nat.const_mul (Real.sqrt C)
  have hupper : Tendsto (fun M : ℕ => (8 / κ) *
      (|criticalContinuousAbel (M : ℝ) * Real.log M /
        ((M : ℝ) * Real.sqrt M)| +
       Real.sqrt C * (Real.log M / Real.sqrt M))) atTop (𝓝 0) := by
    simpa using (hsource.add hrest).const_mul (8 / κ)
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
    have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1r
    have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  · filter_upwards [hcover, hcell, hbudget, eventually_ge_atTop (2 : ℕ)]
      with M hcoverM hcellM hbudgetM hM
    let n : ℝ := (((mobiusDivisorSelectionPrimes M \ P M).filter
      (fun p => 4 * p ≤ 3 * M)).card : ℝ)
    have hM1 : 1 ≤ M := by omega
    have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hroot : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMr
    have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM1r
    have hden : 0 < (M : ℝ) * Real.sqrt M := mul_pos hMr hroot
    have hrootBudget : Real.sqrt (mobiusDivisorSelectionEnergy M (P M)) ≤
        Real.sqrt C * (M : ℝ) := by
      calc
        _ ≤ Real.sqrt (C * (M : ℝ) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hbudgetM
        _ = _ := by rw [Real.sqrt_mul hC, Real.sqrt_sq hMr.le]
    have hband := omitted_middle_band_card_le_energy M (P M) hM1 hcoverM hcellM
    change κ * (Real.sqrt (M : ℝ) / 8) * n ≤
      |criticalContinuousAbel (M : ℝ)| +
        Real.sqrt (mobiusDivisorSelectionEnergy M (P M)) at hband
    have hbase : κ * (Real.sqrt (M : ℝ) / 8) * n ≤
        |criticalContinuousAbel (M : ℝ)| + Real.sqrt C * (M : ℝ) :=
      hband.trans (add_le_add le_rfl hrootBudget)
    have hfactor : 0 ≤ (8 / κ) *
        (Real.log M / ((M : ℝ) * Real.sqrt M)) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hbase hfactor
    have hnorm : |criticalContinuousAbel (M : ℝ)| * Real.log M /
        ((M : ℝ) * Real.sqrt M) =
        |criticalContinuousAbel (M : ℝ) * Real.log M /
          ((M : ℝ) * Real.sqrt M)| := by
      rw [abs_div, abs_mul, abs_of_nonneg hlog, abs_of_pos hden]
    change n * Real.log M / (M : ℝ) ≤ _
    calc
      n * Real.log M / (M : ℝ) =
          (κ * (Real.sqrt (M : ℝ) / 8) * n) *
            ((8 / κ) * (Real.log M / ((M : ℝ) * Real.sqrt M))) := by
          field_simp
      _ ≤ (|criticalContinuousAbel (M : ℝ)| + Real.sqrt C * (M : ℝ)) *
            ((8 / κ) * (Real.log M / ((M : ℝ) * Real.sqrt M))) := hmul
      _ = (8 / κ) *
            (|criticalContinuousAbel (M : ℝ) * Real.log M /
                ((M : ℝ) * Real.sqrt M)| +
              Real.sqrt C * (Real.log M / Real.sqrt M)) := by
          rw [← hnorm]
          field_simp

end RHTower
