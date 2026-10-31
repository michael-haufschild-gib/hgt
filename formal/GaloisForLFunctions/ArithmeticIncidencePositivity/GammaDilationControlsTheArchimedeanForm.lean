import GaloisForLFunctions.ArithmeticIncidencePositivity.GammaDilationHasAnExplicitConstant
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier

/-!
# Dilation of the actual archimedean quadratic form

Fourier scaling identifies normalized physical dilation with frequency dilation.
The logarithmic Gamma modulus then bounds the full archimedean energy change
by the source mass, without any derivative norm in the bound.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open _root_.RHTower

/-- Exact Fourier change of variables for normalized physical dilation. -/
theorem mul_archForm_comp_mul {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    r * archForm (fun x => g (r * x)) =
      ∫ ξ : ℝ, 2 * gammaHardyPhaseRate (r * (2 * Real.pi * ξ)) *
        ‖𝓕 (fun u => (g u : ℂ)) ξ‖ ^ 2 := by
  let F : ℝ → ℂ := 𝓕 (fun u => (g u : ℂ))
  let H : ℝ → ℝ := fun ξ =>
    2 * gammaHardyPhaseRate (r * (2 * Real.pi * ξ)) * ‖F ξ‖ ^ 2
  have hscaled (ξ : ℝ) :
      2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖𝓕 (fun u => (g (r * u) : ℂ)) ξ‖ ^ 2 = r⁻¹ ^ 2 * H (r⁻¹ * ξ) := by
    rw [fourier_comp_mul_left hr (fun u => (g u : ℂ)) ξ, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, mul_pow]
    dsimp only [H, F]
    have heq : r * (2 * Real.pi * (r⁻¹ * ξ)) = 2 * Real.pi * ξ := by
      field_simp
    rw [heq, show ξ / r = r⁻¹ * ξ by ring]
    ring
  rw [archForm, WeilLevyPole.integral_paperFT_sq_mul_gammaBracket]
  simp_rw [hscaled]
  rw [integral_const_mul, Measure.integral_comp_mul_left H r⁻¹,
    inv_inv, abs_of_pos hr, smul_eq_mul]
  change r * (r⁻¹ ^ 2 * (r * ∫ ξ, H ξ)) = ∫ ξ, H ξ
  field_simp

/-- Normalized physical dilation changes the full Gamma form by a bounded
logarithmic multiple of the actual squared source norm. -/
theorem archForm_logarithmic_dilation_bound (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {r : ℝ} (hr : 0 < r) :
    |r * archForm (fun x => g (r * x)) - archForm g| ≤
      10 * |Real.log r| * ∫ u : ℝ, g u ^ 2 := by
  let C : ℝ := 5
  have hbound (r : ℝ) (hr : 0 < r) (t : ℝ) :
      |gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t| ≤ C * |Real.log r| :=
    gammaHardyPhaseRate_logarithmic_dilation_bound hr t
  let G : ℝ → ℂ := fun u => (g u : ℂ)
  let F : ℝ → ℂ := 𝓕 G
  have hGcont : Continuous G := Complex.continuous_ofReal.comp hg.continuous
  have hGcs : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  have hG1 : Integrable G := hGcont.integrable_of_hasCompactSupport hGcs
  have hG2 : MemLp G 2 := hGcont.memLp_of_hasCompactSupport hGcs
  have hsq : Integrable (fun ξ : ℝ => ‖F ξ‖ ^ 2) :=
    GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hG1 hG2
  let D : ℝ → ℝ := fun ξ =>
    2 * (gammaHardyPhaseRate (r * (2 * Real.pi * ξ)) -
      gammaHardyPhaseRate (2 * Real.pi * ξ)) * ‖F ξ‖ ^ 2
  have hDnorm (ξ : ℝ) : ‖D ξ‖ ≤ (2 * C * |Real.log r|) * ‖F ξ‖ ^ 2 := by
    dsimp only [D]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖F ξ‖),
      abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have h := mul_le_mul_of_nonneg_left (hbound r hr (2 * Real.pi * ξ)) two_pos.le
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h (sq_nonneg ‖F ξ‖)
  have hDcont : Continuous (fun ξ : ℝ =>
      2 * (gammaHardyPhaseRate (r * (2 * Real.pi * ξ)) -
        gammaHardyPhaseRate (2 * Real.pi * ξ))) :=
    ((continuous_gammaHardyPhaseRate.comp
      (continuous_const.mul (continuous_const.mul continuous_id))).sub
      (continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id))).const_mul 2
  have hmajor := hsq.const_mul (2 * C * |Real.log r|)
  have hDi : Integrable D := hmajor.mono'
    (hDcont.aestronglyMeasurable.mul hsq.aestronglyMeasurable)
    (Filter.Eventually.of_forall hDnorm)
  have hbase : Integrable (fun ξ : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖F ξ‖ ^ 2) := by
    have h := (integrable_gammaHardy_normSq_fourier_ofReal hg hgc).const_mul 2
    simpa only [mul_assoc] using h
  have hsum : Integrable (fun ξ : ℝ =>
      2 * gammaHardyPhaseRate (r * (2 * Real.pi * ξ)) * ‖F ξ‖ ^ 2) := by
    apply (hDi.add hbase).congr
    exact Filter.Eventually.of_forall fun ξ => by
      change D ξ + 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖F ξ‖ ^ 2 = _
      dsimp only [D]
      ring
  have hdiff : r * archForm (fun x => g (r * x)) - archForm g = ∫ ξ, D ξ := by
    rw [mul_archForm_comp_mul hr, archForm,
      WeilLevyPole.integral_paperFT_sq_mul_gammaBracket, ← integral_sub hsum hbase]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by dsimp only [D]; ring
  rw [hdiff]
  have hb := (norm_integral_le_integral_norm D).trans (integral_mono hDi.norm hmajor hDnorm)
  have hmass : (∫ ξ : ℝ, ‖F ξ‖ ^ 2) = ∫ u : ℝ, g u ^ 2 := by
    rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hG1 hG2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp only [G]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [Real.norm_eq_abs, integral_const_mul, hmass, C,
    show (2 : ℝ) * 5 = 10 by norm_num] using hb

theorem exists_archForm_logarithmic_dilation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℝ), ContDiff ℝ 2 g → HasCompactSupport g →
      ∀ r : ℝ, 0 < r →
      |r * archForm (fun x => g (r * x)) - archForm g| ≤
        C * |Real.log r| * ∫ u : ℝ, g u ^ 2 :=
  ⟨10, by norm_num, fun g hg hgc _ hr => archForm_logarithmic_dilation_bound g hg hgc hr⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.mul_archForm_comp_mul
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.archForm_logarithmic_dilation_bound
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.exists_archForm_logarithmic_dilation_bound
