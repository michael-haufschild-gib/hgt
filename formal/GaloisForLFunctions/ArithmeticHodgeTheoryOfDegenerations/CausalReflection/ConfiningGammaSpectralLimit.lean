import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGammaSymbol
import GaloisForLFunctions.HTGeometry.HardyBoundary.FourierFirstMomentWindow

/-!
# Integrated Gamma comparison with the logarithmic limit

Dominated convergence removes the spectral remainder for each fixed
logarithmic-domain profile. A bounded physical first moment controls its
negative part uniformly, by separating a shrinking Fourier window from
the frequency tails.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- Spectral error between the dilated Gamma form and its logarithmic limit. -/
def confiningGammaErrorForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ ξ, confiningGammaError a ξ * ‖𝓕 f ξ‖ ^ 2

private theorem error_majorant_integrable {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2)) (C : ℝ) :
    Integrable (fun ξ => (C + |Real.log (|ξ|)|) * ‖𝓕 f ξ‖ ^ 2) := by
  apply (((RHTower.integrable_norm_sq_fourier hf1 hf2).const_mul C).add hlog).congr
  exact Eventually.of_forall fun ξ => by
    change C * ‖𝓕 f ξ‖ ^ 2 + |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2 = _
    ring

private theorem measurable_error_density {f : ℝ → ℂ} (hf1 : Integrable f) (a : ℝ) :
    Measurable (fun ξ => confiningGammaError a ξ * ‖𝓕 f ξ‖ ^ 2) := by
  have hF := RHTower.continuous_fourier_of_integrable hf1
  have hσ := continuous_confiningGammaSymbol
  dsimp only [confiningGammaError]
  fun_prop

theorem integrable_confiningGammaError {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2))
    {a : ℝ} (ha : 1 ≤ a) :
    Integrable (fun ξ => confiningGammaError a ξ * ‖𝓕 f ξ‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := exists_confiningGammaError_bound
  apply (error_majorant_integrable hf1 hf2 hlog C).mono'
    (measurable_error_density hf1 a).aestronglyMeasurable
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff]
  filter_upwards [hn] with ξ hξ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖𝓕 f ξ‖)]
  exact mul_le_mul_of_nonneg_right (hC ha hξ) (sq_nonneg _)

/-- Every fixed logarithmic-domain profile has a vanishing Gamma remainder. -/
theorem tendsto_confiningGammaErrorForm {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume)
    (hlog : Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2)) :
    Tendsto (fun a : ℝ => confiningGammaErrorForm a f) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_confiningGammaError_bound
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff]
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := atTop)
    (F := fun (a : ℝ) ξ => confiningGammaError a ξ * ‖𝓕 f ξ‖ ^ 2)
    (f := fun _ : ℝ => (0 : ℝ)) (fun ξ => (C + |Real.log (|ξ|)|) * ‖𝓕 f ξ‖ ^ 2)
    (Eventually.of_forall fun a => (measurable_error_density hf1 a).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
      filter_upwards [hn] with ξ hξ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖𝓕 f ξ‖)]
      exact mul_le_mul_of_nonneg_right (hC ha hξ) (sq_nonneg _))
    (error_majorant_integrable hf1 hf2 hlog C)
    (by
      filter_upwards [hn] with ξ hξ
      simpa only [zero_mul] using (tendsto_confiningGammaError hξ).mul_const (‖𝓕 f ξ‖ ^ 2))
  simpa only [confiningGammaErrorForm, integral_zero] using h

private theorem gamma_error_lower_in_window {a T ξ : ℝ} (ha : 0 < a)
    (hξ : ξ ≠ 0) (hwindow : |ξ| ≤ T / a) :
    -(10 + Real.log 4 + Real.log T) ≤ confiningGammaError a ξ := by
  have hz : 0 < |a * ξ| := abs_pos.mpr (mul_ne_zero ha.ne' hξ)
  have hbound : |a * ξ| ≤ T := by
    rw [abs_mul, abs_of_pos ha]
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hwindow
  have hlog := Real.log_le_log hz hbound
  have hσ := confiningGammaSymbol_lower (a * ξ)
  rw [confiningGammaError_eq ha hξ]
  linarith only [hlog, hσ]

/-- Bounded first moments make the negative spectral remainder uniformly negligible. -/
theorem exists_uniform_confiningGammaErrorForm_lower {M ε : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {a : ℝ}, A ≤ a → ∀ {f : ℝ → ℂ},
      Integrable f → MemLp f 2 volume → (∫ u, ‖f u‖ ^ 2) = 1 →
      Integrable (fun ξ => |Real.log (|ξ|)| * ‖𝓕 f ξ‖ ^ 2) →
      Integrable (fun u => |u| * ‖f u‖ ^ 2) →
      (∫ u, |u| * ‖f u‖ ^ 2) ≤ M → -ε ≤ confiningGammaErrorForm a f := by
  obtain ⟨T, hT, htail⟩ := exists_confiningGammaSymbol_log_tail (half_pos hε)
  let D : ℝ := 10 + Real.log 4 + Real.log T
  have hD : 0 ≤ D := by
    have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have hlogT := Real.log_nonneg hT
    dsimp only [D]
    linarith only [h4, hlogT]
  obtain ⟨η, hη, hsmall⟩ := HTGeometry.exists_fourierWindow_small_of_firstMoment hM
    (div_pos hε (by positivity : 0 < 2 * (D + 1)))
  refine ⟨max 1 (T / η), le_max_left _ _, ?_⟩
  intro a hAa f hf1 hf2 hm hlog hfirst hmf
  have ha1 : 1 ≤ a := (le_max_left _ _).trans hAa
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hwindow : T / a ≤ η := by
    apply (div_le_iff₀ ha).mpr
    have h := (div_le_iff₀ hη).mp ((le_max_right _ _).trans hAa)
    simpa only [mul_comm] using h
  have hζ : 0 ≤ T / a := div_nonneg (zero_le_one.trans hT) ha.le
  have hmass := RHTower.integrable_norm_sq_fourier hf1 hf2
  have herror := integrable_confiningGammaError hf1 hf2 hlog ha1
  have hn : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by simp [ae_iff]
  have hpt : ∀ᵐ ξ : ℝ,
      (-(ε / 2)) * ‖𝓕 f ξ‖ ^ 2 - D * (Icc (-(T / a)) (T / a)).indicator
        (fun ξ => ‖𝓕 f ξ‖ ^ 2) ξ ≤ confiningGammaError a ξ * ‖𝓕 f ξ‖ ^ 2 := by
    filter_upwards [hn] with ξ hξ
    by_cases hw : ξ ∈ Icc (-(T / a)) (T / a)
    · rw [indicator_of_mem hw]
      have he := gamma_error_lower_in_window ha hξ (abs_le.mpr hw)
      change -D ≤ confiningGammaError a ξ at he
      have hscalar : -(ε / 2) - D ≤ confiningGammaError a ξ := by linarith only [he, hε]
      simpa only [sub_mul] using mul_le_mul_of_nonneg_right hscalar (sq_nonneg ‖𝓕 f ξ‖)
    · rw [indicator_of_notMem hw, mul_zero, sub_zero]
      have hξT : T ≤ |a * ξ| := by
        have hξ' : T / a < |ξ| := lt_of_not_ge (fun hh => hw (abs_le.mp hh))
        have h := (div_lt_iff₀ ha).mp hξ'
        rw [abs_mul, abs_of_pos ha]
        simpa only [mul_comm] using h.le
      have he := (abs_le.mp (htail (a * ξ) hξT)).1
      rw [← confiningGammaError_eq ha hξ] at he
      exact mul_le_mul_of_nonneg_right he (sq_nonneg _)
  have hcut : Integrable ((Icc (-(T / a)) (T / a)).indicator (fun ξ => ‖𝓕 f ξ‖ ^ 2)) :=
    hmass.indicator measurableSet_Icc
  have hi := integral_mono_ae ((hmass.const_mul (-(ε / 2))).sub (hcut.const_mul D)) herror hpt
  change (∫ ξ, (-(ε / 2)) * ‖𝓕 f ξ‖ ^ 2 - D *
    (Icc (-(T / a)) (T / a)).indicator (fun ξ => ‖𝓕 f ξ‖ ^ 2) ξ) ≤
      confiningGammaErrorForm a f at hi
  rw [integral_sub (hmass.const_mul (-(ε / 2))) (hcut.const_mul D),
    integral_const_mul (-(ε / 2)) (fun ξ => ‖𝓕 f ξ‖ ^ 2),
    integral_const_mul D ((Icc (-(T / a)) (T / a)).indicator (fun ξ => ‖𝓕 f ξ‖ ^ 2)),
    integral_indicator measurableSet_Icc, RHTower.integral_norm_sq_fourier_eq hf1 hf2, hm,
    mul_one] at hi
  have hsm := hsmall hf1 hf2 hm hfirst hmf hζ hwindow
  have hpay := mul_le_mul_of_nonneg_left hsm.le hD
  have hcap : D * (ε / (2 * (D + 1))) ≤ ε / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (D + 1))).mpr
    nlinarith only [hε]
  linarith only [hi, hpay.trans hcap]

#print axioms tendsto_confiningGammaErrorForm
#print axioms exists_uniform_confiningGammaErrorForm_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
