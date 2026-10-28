import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryHasAGammaGap
import GaloisForLFunctions.ArithmeticIndexDescent.TheXiEdgeFieldHasLogarithmicGrowth
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry

/-!
# The square-prime boundary retains a positive Gamma share

Line-conjugate zero pairs give logarithmic growth of the completed Xi field
on the zero-free edge. Digamma has only logarithmic growth, so the exact
square-boundary gap retains a fixed fraction of the original Gamma symbol
at large frequencies. Its positive scalar floor handles the remaining
compact interval without introducing a frequency-dependent reserve.
-/

noncomputable section
open Complex Real Set
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

theorem gammaIncrementSymbol_nonneg (t : ℝ) : 0 ≤ gammaIncrementSymbol t :=
  mul_nonneg (by norm_num) (sub_nonneg.mpr (gammaHardyPhaseRate_zero_le_levy t))

theorem gammaIncrementSymbol_neg (t : ℝ) :
    gammaIncrementSymbol (-t) = gammaIncrementSymbol t := by
  simp only [gammaIncrementSymbol, gammaHardyPhaseRate_neg]

theorem gammaIncrementSymbol_abs (t : ℝ) :
    gammaIncrementSymbol |t| = gammaIncrementSymbol t := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, gammaIncrementSymbol_neg]

theorem continuous_gammaIncrementSymbol : Continuous gammaIncrementSymbol :=
  (continuous_gammaHardyPhaseRate.sub continuous_const).const_mul 2

private theorem xi_edge_field_abs (t : ℝ) :
    (logDeriv xi ((1 : ℂ) + 2 * ((|t| : ℝ) : ℂ) * I)).re =
      (logDeriv xi ((1 : ℂ) + 2 * (t : ℂ) * I)).re := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    have hleft : (1 : ℂ) + 2 * ((-t : ℝ) : ℂ) * I =
        (1 : ℂ) - ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    have hright : (1 : ℂ) + ((2 * t : ℝ) : ℂ) * I =
        (1 : ℂ) + 2 * (t : ℂ) * I := by push_cast; ring
    rw [hleft, ← hright]
    simpa only [Complex.ofReal_one] using re_logDeriv_xi_conj_line 1 (2 * t)

private theorem two_lt_log_four_pi_reserve : 2 < Real.log (4 * Real.pi) := by
  have h8 : (8 : ℝ) < 4 * Real.pi := by linarith only [Real.pi_gt_d2]
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 8) h8
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [he] at hl
  linarith only [hl, Real.log_two_gt_d9]

/-- The scalar floor and the completed Xi field are simultaneous parts of the same gap. -/
theorem eulerConstant_add_xi_le_gammaIncrement_sub_squarePrimeRegular
    {t : ℝ} (ht : t ≠ 0) :
    Real.eulerMascheroniConstant +
        2 * (logDeriv xi ((1 : ℂ) + 2 * (t : ℂ) * I)).re ≤
      gammaIncrementSymbol t - squarePrimeRegularSymbol t := by
  rw [gammaIncrement_sub_squarePrimeRegular_eq ht]
  have hcosh : Real.pi / (2 * Real.cosh (Real.pi * t)) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      (by linarith only [Real.one_le_cosh (Real.pi * t)])
  have hrat : 2 / (1 + 4 * t ^ 2) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + 4 * t ^ 2)).mpr
    nlinarith only [sq_nonneg t]
  linarith only [hcosh, hrat, two_lt_log_four_pi_reserve]

/-- The original Gamma increment has a logarithmic upper bound at large positive frequency. -/
theorem exists_gammaIncrement_le_two_log :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ t → gammaIncrementSymbol t ≤ 2 * Real.log t := by
  let C : ℝ := digammaVerticalLogConstant - (Complex.digamma (1 / 4 : ℂ)).re
  refine ⟨max 2 (Real.exp C), le_max_left _ _, ?_⟩
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_max_left _ _).trans ht
  have hte : Real.exp C ≤ t := (le_max_right _ _).trans ht
  have hc : C ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos C) hte
    rwa [Real.log_exp] at h
  have hn := norm_digamma_vertical_le_log (σ := 1 / 4) (t := t / 2)
    (by norm_num) (by linarith only [ht2]) (by linarith only [ht2])
  have he : (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I) =
      (1 / 4 : ℂ) + I * (t : ℂ) / 2 := by push_cast; ring
  rw [he] at hn
  have hr := Complex.re_le_norm (Complex.digamma ((1 / 4 : ℂ) + I * (t : ℂ) / 2))
  have hl : Real.log (t / 2) ≤ Real.log t :=
    Real.log_le_log (by linarith only [ht2]) (by linarith only [ht2])
  rw [gammaIncrementSymbol_eq_digamma]
  dsimp only [C] at hc
  linarith only [hc, hn, hr, hl]

/-- One positive fraction of Gamma and one positive mass floor survive the square boundary together. -/
theorem exists_squarePrime_regular_retained_gamma :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      δ * gammaIncrementSymbol t + Real.eulerMascheroniConstant / 2 ≤
        gammaIncrementSymbol t - squarePrimeRegularSymbol t := by
  obtain ⟨c, hc, TX, hTX, hxi⟩ := exists_xi_edge_logarithmic_lower
  obtain ⟨TG, hTG, hg⟩ := exists_gammaIncrement_le_two_log
  let T : ℝ := max TX TG
  have hT4 : (4 : ℝ) ≤ T := hTX.trans (le_max_left _ _)
  have hγ : 0 < Real.eulerMascheroniConstant :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  have hlarge (t : ℝ) (ht : T ≤ |t|) :
      Real.eulerMascheroniConstant + c * gammaIncrementSymbol t ≤
        gammaIncrementSymbol t - squarePrimeRegularSymbol t := by
    have hpos : 0 < |t| := lt_of_lt_of_le (by linarith only [hT4]) ht
    have hTXt : TX ≤ |t| := (le_max_left _ _).trans ht
    have hTGt : TG ≤ |t| := (le_max_right _ _).trans ht
    have hx := hxi (2 * |t|) (by linarith only [hTXt, hpos])
    have he : ((1 : ℂ) + ((2 * |t| : ℝ) : ℂ) * I) =
        (1 : ℂ) + 2 * ((|t| : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, xi_edge_field_abs] at hx
    have hl : Real.log |t| ≤ Real.log (2 * |t|) :=
      Real.log_le_log hpos (by linarith only [hpos])
    have hx' : c * Real.log |t| ≤
        (logDeriv xi ((1 : ℂ) + 2 * (t : ℂ) * I)).re :=
      (mul_le_mul_of_nonneg_left hl hc.le).trans hx
    have hgt := hg |t| hTGt
    rw [gammaIncrementSymbol_abs] at hgt
    have hpay := mul_le_mul_of_nonneg_left hgt hc.le
    have htne : t ≠ 0 := fun hz => by simp only [hz, abs_zero] at hpos; exact lt_irrefl _ hpos
    have hbase := eulerConstant_add_xi_le_gammaIncrement_sub_squarePrimeRegular htne
    linarith only [hx', hpay, hbase]
  obtain ⟨z, _hz, hmax⟩ := (isCompact_Icc (a := -T) (b := T)).exists_isMaxOn
    ⟨0, by constructor <;> linarith only [hT4]⟩ continuous_gammaIncrementSymbol.continuousOn
  let M : ℝ := max 1 (gammaIncrementSymbol z)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  let δ : ℝ := min c (Real.eulerMascheroniConstant / (2 * M))
  have hδ : 0 < δ := lt_min hc (div_pos hγ (mul_pos (by norm_num) hM))
  refine ⟨δ, hδ, ?_⟩
  intro t
  by_cases ht : |t| ≤ T
  · have hgt : gammaIncrementSymbol t ≤ M :=
      (hmax (abs_le.mp ht)).trans (le_max_right _ _)
    have hdM : δ * M ≤ Real.eulerMascheroniConstant / 2 := by
      calc
        _ ≤ (Real.eulerMascheroniConstant / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hM.le
        _ = _ := by field_simp [hM.ne']
    have hdG := (mul_le_mul_of_nonneg_left hgt hδ.le).trans hdM
    have hfloor := eulerConstant_le_gammaIncrement_sub_squarePrimeRegular t
    linarith only [hdG, hfloor]
  · have hl := hlarge t (not_le.mp ht).le
    have hdG : δ * gammaIncrementSymbol t ≤ c * gammaIncrementSymbol t :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (gammaIncrementSymbol_nonneg t)
    linarith only [hl, hdG, hγ]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_gammaIncrement_le_two_log
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_squarePrime_regular_retained_gamma
