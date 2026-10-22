import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureVerticalGammaTail
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureLatticePoleGammaVMBudget
import GaloisForLFunctions.RHTower.XiWardCubicReflectionLoewnerCodiagonalIncidence

/-!
# Bounded safe-line height-two HCF source increment

The cross-height HCF candidate starts from the literal completed
Euler--Gamma current on `Re s = 3 / 2`.  This module supplies its finite
source-side estimate: after a height-two difference, every channel is
uniformly bounded past the Gamma-tail threshold.  The difference is a
four-leg quadratic input after taking its squared norm.

The result remains entirely on the absolute-Euler side.  The open HCF step is
to continue this positive square to a noncancelling transverse divisor trace.
-/

open Complex LSeries

namespace RHTower

noncomputable section

/-- Literal height-two increment of the completed HCF Euler--Gamma current. -/
def criticalFeatureVerticalTwoSourceIncrement (t : ℝ) : ℂ :=
  xiWardCubicCompletedArithmeticCurrent (criticalFeatureEulerVMArchPoint (t + 2)) -
    xiWardCubicCompletedArithmeticCurrent (criticalFeatureEulerVMArchPoint t)

theorem criticalFeatureEulerVMArchPoint_add_two_I (t : ℝ) :
    criticalFeatureEulerVMArchPoint (t + 2) =
      criticalFeatureEulerVMArchPoint t + 2 * I := by
  simp [criticalFeatureEulerVMArchPoint]
  ring

/-- Exact safe-source split of the height-two increment. -/
theorem criticalFeatureVerticalTwoSourceIncrement_eq_channels (t : ℝ) :
    criticalFeatureVerticalTwoSourceIncrement t =
      (criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹ +
        ((criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹) +
        (logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + 2)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)) := by
  unfold criticalFeatureVerticalTwoSourceIncrement xiWardCubicCompletedArithmeticCurrent
  ring

theorem norm_inv_criticalFeatureEulerVMArchPoint_le (t : ℝ) :
    ‖(criticalFeatureEulerVMArchPoint t)⁻¹‖ ≤ 2 / 3 := by
  have hnorm : (3 / 2 : ℝ) ≤ ‖criticalFeatureEulerVMArchPoint t‖ := by
    rw [← criticalFeatureEulerVMArchPoint_re t]
    exact Complex.re_le_norm _
  have hpos : 0 < ‖criticalFeatureEulerVMArchPoint t‖ := by linarith
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith

theorem norm_inv_criticalFeatureEulerVMArchPoint_sub_one_le (t : ℝ) :
    ‖(criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ ≤ 2 := by
  have hre : (criticalFeatureEulerVMArchPoint t - 1).re = 1 / 2 := by
    rw [Complex.sub_re, criticalFeatureEulerVMArchPoint_re]
    norm_num
  have hnorm : (1 / 2 : ℝ) ≤ ‖criticalFeatureEulerVMArchPoint t - 1‖ := by
    rw [← hre]
    exact Complex.re_le_norm _
  have hpos : 0 < ‖criticalFeatureEulerVMArchPoint t - 1‖ := by linarith
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith

/-- The literal height-two source increment is uniformly bounded in the safe
Euler half-plane outside the finite Gamma threshold. -/
theorem exists_norm_criticalFeatureVerticalTwoSourceIncrement_le :
    ∃ C R : ℝ, 0 ≤ C ∧ 2 ≤ R ∧ ∀ t : ℝ,
      R ≤ ‖criticalFeatureEulerVMArchPoint t‖ →
        ‖criticalFeatureVerticalTwoSourceIncrement t‖ ≤ C := by
  obtain ⟨K, R, hK, hR, hgamma⟩ :=
    exists_norm_logDeriv_GammaR_vertical_two_shift_le
  let A : ℝ := ∑' n : ℕ, ‖LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨16 / 3 + K / 2 + 2 * A, R, by positivity, hR, ?_⟩
  intro t ht
  have htwo : 2 ≤ ‖criticalFeatureEulerVMArchPoint t‖ := hR.trans ht
  have hpointPos : 0 < (criticalFeatureEulerVMArchPoint t).re := by
    rw [criticalFeatureEulerVMArchPoint_re]
    norm_num
  have hshift := criticalFeatureEulerVMArchPoint_add_two_I t
  have hgammaRaw := hgamma (criticalFeatureEulerVMArchPoint t) hpointPos ht
  have hgamma' :
      ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ ≤ K / 2 := by
    calc
      ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ =
        ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t + 2 * I) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ := by rw [hshift]
      _ ≤ K / ‖criticalFeatureEulerVMArchPoint t‖ := hgammaRaw
      _ ≤ K / 2 := div_le_div_of_nonneg_left hK (by norm_num) htwo
  have hA_t := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le t
  have hA_t2 := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le (t + 2)
  change ‖criticalFeatureVerticalTwoSourceIncrement t‖ ≤ _
  rw [criticalFeatureVerticalTwoSourceIncrement_eq_channels]
  have hfirst : ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
      (criticalFeatureEulerVMArchPoint t)⁻¹‖ ≤ 4 / 3 := by
    calc
      ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹‖ ≤
          ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹‖ +
            ‖(criticalFeatureEulerVMArchPoint t)⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 / 3 + 2 / 3 := by
        gcongr
        · exact norm_inv_criticalFeatureEulerVMArchPoint_le _
        · exact norm_inv_criticalFeatureEulerVMArchPoint_le _
      _ = 4 / 3 := by norm_num
  have hsecond : ‖(criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
      (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ ≤ 4 := by
    calc
      ‖(criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ ≤
          ‖(criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹‖ +
            ‖(criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := by
        gcongr
        · exact norm_inv_criticalFeatureEulerVMArchPoint_sub_one_le _
        · exact norm_inv_criticalFeatureEulerVMArchPoint_sub_one_le _
      _ = 4 := by norm_num
  have hprime : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint (t + 2)) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint t)‖ ≤ 2 * A := by
    calc
      _ ≤ ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + 2))‖ +
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)‖ := norm_sub_le _ _
      _ ≤ A + A := by simpa only [A] using add_le_add hA_t2 hA_t
      _ = 2 * A := by ring
  calc
    ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹ +
        ((criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹) +
        (logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + 2)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t))‖ ≤
        ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹‖ +
        ‖(criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ +
        ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ +
        ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + 2)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)‖ := by
      calc
        _ = ‖((criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹ +
          ((criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹)) +
          ((logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + 2)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t)))‖ := by
          congr 1; ring
        _ ≤ ‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹ +
          ((criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹)‖ +
          ‖(logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + 2)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t))‖ := norm_add_le _ _
        _ ≤ (‖(criticalFeatureEulerVMArchPoint (t + 2))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹‖ +
          ‖(criticalFeatureEulerVMArchPoint (t + 2) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖) +
          (‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + 2)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ +
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + 2)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t)‖) := by
          gcongr
          · exact norm_add_le _ _
          · exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ 16 / 3 + K / 2 + 2 * A := by linarith

end

end RHTower
