import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy

/-!
# The Gamma symbol and its logarithmic remainder

The exact Fourier normalization transfers Gamma integrability between
physical and spectral coordinates. Evenness and the conductor asymptotic
give a bounded remainder away from zero and a fixed logarithmic majorant
for all dilations of strength at least one.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- The Gamma symbol in the Fourier transform's `2π` normalization. -/
def confiningGammaSymbol (ξ : ℝ) : ℝ := 2 * gammaHardyPhaseRate (2 * Real.pi * ξ)

theorem archForm_eq_integral_confiningGammaSymbol (F : ℝ → ℝ) :
    archForm F = ∫ ξ : ℝ, confiningGammaSymbol ξ * ‖𝓕 (cx F) ξ‖ ^ 2 :=
  WeilLevyPole.integral_paperFT_sq_mul_gammaBracket (cx F)

theorem CriticalHalfLineEnergyDomain.integrable_confiningGammaSymbol {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (fun ξ => confiningGammaSymbol ξ * ‖𝓕 (cx F) ξ‖ ^ 2) := by
  simpa only [confiningGammaSymbol, mul_assoc] using
    hF.integrable_gammaHardyFourier.const_mul 2

/-- Integrability in normalized Fourier coordinates recovers the literal Gamma domain. -/
theorem integrable_gammaBracket_of_confiningGammaSymbol {F : ℝ → ℝ}
    (hF : Integrable (fun ξ => confiningGammaSymbol ξ * ‖𝓕 (cx F) ξ‖ ^ 2)) :
    Integrable (fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) := by
  let c : ℝ := -(1 / (2 * Real.pi))
  have hc : c ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero (by positivity))
  apply (hF.comp_mul_left' (R := c) hc).congr
  exact Eventually.of_forall fun r => by
    have he : 2 * Real.pi * (c * r) = -r := by
      dsimp only [c]
      field_simp
    change confiningGammaSymbol (c * r) * ‖𝓕 (cx F) (c * r)‖ ^ 2 =
      ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r
    rw [confiningGammaSymbol, fourier_eq_paperFT_neg_two_pi_mul, he, neg_neg,
      gammaHardyPhaseRate_neg, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate]
    ring

theorem continuous_confiningGammaSymbol : Continuous confiningGammaSymbol :=
  (continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id)).const_mul 2

theorem confiningGammaSymbol_neg (ξ : ℝ) : confiningGammaSymbol (-ξ) = confiningGammaSymbol ξ := by
  dsimp only [confiningGammaSymbol]
  rw [mul_neg, gammaHardyPhaseRate_neg]

theorem confiningGammaSymbol_abs (ξ : ℝ) : confiningGammaSymbol |ξ| = confiningGammaSymbol ξ := by
  by_cases hξ : 0 ≤ ξ
  · rw [abs_of_nonneg hξ]
  · rw [abs_of_neg (lt_of_not_ge hξ), confiningGammaSymbol_neg]

theorem confiningGammaSymbol_sub_log_tendsto_zero :
    Tendsto (fun ξ => confiningGammaSymbol ξ - Real.log ξ) atTop (𝓝 0) := by
  have ht : Tendsto (fun ξ : ℝ => 2 * Real.pi * ξ) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have h := (gammaHardyPhaseRate_sub_log_conductor_tendsto_zero.comp ht).const_mul 2
  have he (ξ : ℝ) :
      2 * (gammaHardyPhaseRate (2 * Real.pi * ξ) -
        Real.log ((2 * Real.pi * ξ) / (2 * Real.pi)) / 2) =
      confiningGammaSymbol ξ - Real.log ξ := by
    rw [mul_div_cancel_left₀ ξ (by positivity : 2 * Real.pi ≠ 0)]
    dsimp only [confiningGammaSymbol]
    ring
  simpa only [Function.comp_def, mul_zero] using h.congr he

/-- Both frequency tails have the same exact logarithmic normalization. -/
theorem exists_confiningGammaSymbol_log_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ξ : ℝ, T ≤ |ξ| →
      |confiningGammaSymbol ξ - Real.log (|ξ|)| ≤ ε := by
  have hlim := confiningGammaSymbol_sub_log_tendsto_zero.abs
  simp only [abs_zero] at hlim
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (ge_mem_nhds hε))
  refine ⟨max T 1, le_max_right _ _, ?_⟩
  intro ξ hξ
  have hh := hT |ξ| ((le_max_left _ _).trans hξ)
  rwa [confiningGammaSymbol_abs] at hh

/-- The global Gamma floor is inherited from the exact Weil bracket. -/
theorem confiningGammaSymbol_lower (ξ : ℝ) :
    -(10 + Real.log 4) ≤ confiningGammaSymbol ξ := by
  have h := WeilWorkPBAP.joint_gamma_lower_log (2 * Real.pi * ξ)
  have hl := Real.log_nonneg (show 1 ≤ 2 + |2 * Real.pi * ξ| by
    linarith only [abs_nonneg (2 * Real.pi * ξ)])
  rw [WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate] at h
  change _ ≤ confiningGammaSymbol ξ at h
  linarith only [h, hl]

/-- The logarithmic remainder is bounded outside the unit window; the symbol is bounded inside. -/
theorem exists_confiningGammaSymbol_log_remainder_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ ξ : ℝ, 1 ≤ |ξ| → |confiningGammaSymbol ξ - Real.log (|ξ|)| ≤ C) ∧
      (∀ ξ : ℝ, |ξ| ≤ 1 → |confiningGammaSymbol ξ| ≤ C) := by
  obtain ⟨T, hT, htail⟩ := exists_confiningGammaSymbol_log_tail zero_lt_one
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_confiningGammaSymbol.continuousOn (s := Icc (-T) T))
  have hlogT := Real.log_nonneg hT
  refine ⟨|B| + Real.log T + 1, by positivity, ?_, ?_⟩
  · intro ξ hξ1
    by_cases hξ : T ≤ |ξ|
    · exact (htail ξ hξ).trans (by linarith only [hlogT, abs_nonneg B])
    · have hm : ξ ∈ Icc (-T) T := abs_le.mp (le_of_lt (lt_of_not_ge hξ))
      have hh := hB ξ hm
      rw [Real.norm_eq_abs] at hh
      have hl := Real.log_nonneg hξ1
      have hlu := Real.log_le_log (zero_lt_one.trans_le hξ1) (le_of_lt (lt_of_not_ge hξ))
      have hab : |confiningGammaSymbol ξ - Real.log (|ξ|)| ≤
          |confiningGammaSymbol ξ| + |Real.log (|ξ|)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (confiningGammaSymbol ξ) (-Real.log |ξ|)
      rw [abs_of_nonneg hl] at hab
      linarith only [hab, hh, le_abs_self B, hlu]
  · intro ξ hξ
    have hh := hB ξ (abs_le.mp (hξ.trans hT))
    rw [Real.norm_eq_abs] at hh
    linarith only [hh, le_abs_self B, hlogT]

/-- A logarithmic singularity at zero is the only loss in the global symbol comparison. -/
theorem exists_confiningGammaSymbol_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ ξ : ℝ, |confiningGammaSymbol ξ| ≤ C + |Real.log (|ξ|)|) ∧
      (∀ ξ : ℝ, 1 ≤ |ξ| → |Real.log (|ξ|)| ≤ C + |confiningGammaSymbol ξ|) := by
  obtain ⟨C, hC, hlarge, hsmall⟩ := exists_confiningGammaSymbol_log_remainder_bound
  refine ⟨C, hC, ?_, ?_⟩
  · intro ξ
    by_cases hξ : |ξ| ≤ 1
    · exact (hsmall ξ hξ).trans (by linarith only [abs_nonneg (Real.log |ξ|)])
    · calc
        _ = |(confiningGammaSymbol ξ - Real.log |ξ|) + Real.log (|ξ|)| := by rw [sub_add_cancel]
        _ ≤ |confiningGammaSymbol ξ - Real.log (|ξ|)| + |Real.log (|ξ|)| := abs_add_le _ _
        _ ≤ _ := add_le_add (hlarge ξ (lt_of_not_ge hξ).le) le_rfl
  · intro ξ hξ
    have hh : |Real.log |ξ| - confiningGammaSymbol ξ| ≤ C := by
      rw [abs_sub_comm]
      exact hlarge ξ hξ
    calc
      _ = |(Real.log |ξ| - confiningGammaSymbol ξ) + confiningGammaSymbol ξ| := by rw [sub_add_cancel]
      _ ≤ |Real.log |ξ| - confiningGammaSymbol ξ| + |confiningGammaSymbol ξ| := abs_add_le _ _
      _ ≤ _ := add_le_add hh le_rfl

/-- Difference between the dilated Gamma symbol and the limiting logarithm. -/
def confiningGammaError (a ξ : ℝ) : ℝ :=
  confiningGammaSymbol (a * ξ) - Real.log a - Real.log |ξ|

theorem confiningGammaError_eq {a ξ : ℝ} (ha : 0 < a) (hξ : ξ ≠ 0) :
    confiningGammaError a ξ = confiningGammaSymbol (a * ξ) - Real.log |a * ξ| := by
  rw [abs_mul, abs_of_pos ha, Real.log_mul ha.ne' (abs_pos.mpr hξ).ne']
  dsimp only [confiningGammaError]
  ring

/-- The remainder converges at every nonzero frequency. -/
theorem tendsto_confiningGammaError {ξ : ℝ} (hξ : ξ ≠ 0) :
    Tendsto (fun a : ℝ => confiningGammaError a ξ) atTop (𝓝 0) := by
  have ht : Tendsto (fun a : ℝ => |ξ| * a) atTop atTop :=
    tendsto_id.const_mul_atTop (abs_pos.mpr hξ)
  apply (confiningGammaSymbol_sub_log_tendsto_zero.comp ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have habs : |a * ξ| = |ξ| * a := by rw [abs_mul, abs_of_pos ha, mul_comm]
  change confiningGammaSymbol (|ξ| * a) - Real.log (|ξ| * a) = confiningGammaError a ξ
  rw [confiningGammaError_eq ha hξ, ← habs, confiningGammaSymbol_abs]

/-- A fixed logarithmic majorant controls every dilation of strength at least one. -/
theorem exists_confiningGammaError_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 1 ≤ a → ∀ {ξ : ℝ}, ξ ≠ 0 →
      |confiningGammaError a ξ| ≤ C + |Real.log (|ξ|)| := by
  obtain ⟨C, hC, hlarge, hsmall⟩ := exists_confiningGammaSymbol_log_remainder_bound
  refine ⟨C, hC, ?_⟩
  intro a ha1 ξ hξ
  have ha : 0 < a := zero_lt_one.trans_le ha1
  rw [confiningGammaError_eq ha hξ]
  by_cases hz : 1 ≤ |a * ξ|
  · exact (hlarge (a * ξ) hz).trans (by linarith only [abs_nonneg (Real.log |ξ|)])
  · have hz1 : |a * ξ| ≤ 1 := (lt_of_not_ge hz).le
    have hσ := abs_le.mp (hsmall (a * ξ) hz1)
    have hlogz := Real.log_nonpos (abs_nonneg (a * ξ)) hz1
    have hξle : |ξ| ≤ |a * ξ| := by
      rw [abs_mul, abs_of_pos ha]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (abs_nonneg ξ)
    have hlogx := Real.log_le_log (abs_pos.mpr hξ) hξle
    apply abs_le.mpr
    constructor
    · linarith only [hσ.1, hlogz, abs_nonneg (Real.log |ξ|)]
    · linarith only [hσ.2, hlogx, neg_abs_le (Real.log |ξ|)]

#print axioms archForm_eq_integral_confiningGammaSymbol
#print axioms CriticalHalfLineEnergyDomain.integrable_confiningGammaSymbol
#print axioms exists_confiningGammaSymbol_log_tail
#print axioms confiningGammaSymbol_lower
#print axioms exists_confiningGammaSymbol_log_bound
#print axioms integrable_gammaBracket_of_confiningGammaSymbol
#print axioms tendsto_confiningGammaError
#print axioms exists_confiningGammaError_bound
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
