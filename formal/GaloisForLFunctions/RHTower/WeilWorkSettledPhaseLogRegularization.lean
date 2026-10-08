import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseLogKernel
import GaloisForLFunctions.RHTower.WeilHerglotzPerronIntegral

/-!
# Logarithmic regularization error of the actual canonical phase

The source-only estimate is uniform in every width `0 < η ≤ 1`. It uses the
height-scale Poisson moment, retaining the full measure. This estimates
boundary passage; it does not assert phase settlement or cancellation.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral WeilHerglotz

private theorem integrable_scaled_weight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (fun r : ℝ => Y / (Y ^ 2 + r ^ 2)) (boundaryMeasure hW) := by
  have hY0 : 0 < Y := by linarith
  have hc : Continuous (fun r : ℝ => Y / (Y ^ 2 + r ^ 2)) :=
    continuous_const.div (by fun_prop) (fun _ => by dsimp; positivity)
  refine ((integrable_inv_one_add_sq hW).const_mul Y).mono' hc.aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro r
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hY0.le (by positivity) (by nlinarith)

/-- The scale-adapted weight has an exact, source-evaluable Poisson moment. -/
theorem integral_scaled_weight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Y : ℝ} (hY : 0 < Y) :
    (∫ r : ℝ, Y / (Y ^ 2 + r ^ 2) ∂boundaryMeasure hW) =
      (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re := by
  have hc : Continuous (fun r : ℝ => Y / (Y ^ 2 + r ^ 2)) :=
    continuous_const.div (by fun_prop) (fun _ => by dsimp; positivity)
  have hp : ENNReal.ofReal (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re =
      ∫⁻ r : ℝ, ENNReal.ofReal (Y / (Y ^ 2 + r ^ 2)) ∂boundaryMeasure hW := by
    simpa using ofReal_re_weilContinuation_eq hW (1 / 2 + Y) 0 (by linarith)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => by positivity)
    hc.aestronglyMeasurable, ← hp, ENNReal.toReal_ofReal]
  exact re_weilContinuation_nonneg hW (by simp; linarith)

/-- Uniform full-source regularization with a height-scale Poisson moment. -/
theorem integral_regularizedPhase_sub_le_log_moment {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {η Y : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hY : 1 ≤ Y) :
    (∫ y in Ioc Y (2 * Y), ‖regularizedPhase hW η y - canonicalPhase hW y‖) ≤
      (544 * η * Y * Real.log (1 + 6 * Y / η)) *
        (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re := by
  have hb := integral_regularizedPhase_sub_le_of_kernel_bound hW hη hη1 hY
    ((integrable_scaled_weight hW hY).const_mul
      (544 * η * Y * Real.log (1 + 6 * Y / η)))
    (integral_windowError_le_scaled_weight hη hη1 hY)
  rwa [integral_const_mul, integral_scaled_weight hW (by linarith : 0 < Y)] at hb

/-- Logarithmic growth of the actual source's real-axis Poisson moment. -/
theorem exists_re_weilContinuation_real_le_log {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 4 ≤ Y →
      (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re ≤ C * Real.log (Y + 3) := by
  obtain ⟨K, hK, hbound⟩ := exists_re_herglotzFunction_le_log hW
  refine ⟨1 + K, by positivity, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := by linarith
  have hc : (weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2)).re = 0 := by
    rw [Complex.sub_re, re_herglotzFunction_eq hW (by norm_num)]
    ring
  have he : (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re =
      (herglotzFunction hW (Y : ℂ)).re := by
    rw [weilContinuation, Complex.add_re, hc, add_zero]
    congr 2
    push_cast
    ring
  rw [he]
  have hb := hbound (Y : ℂ) (by simpa using hY)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0] at hb
  have hl : Real.log (Y + 1) ≤ Real.log (Y + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl1 : 1 ≤ Real.log (Y + 3) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    linarith [Real.exp_one_lt_d9]
  nlinarith [mul_le_mul_of_nonneg_left hl1 hK]

/-- Full positivity alone yields logarithmic dyadic phase regularization,
uniform in the width and retaining all atomic and diffuse spectral mass. -/
theorem exists_integral_regularizedPhase_sub_le_log {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 4 ≤ Y → ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∫ y in Ioc Y (2 * Y), ‖regularizedPhase hW η y - canonicalPhase hW y‖) ≤
        C * η * Y * Real.log (Y + 3) * Real.log (1 + 6 * Y / η) := by
  obtain ⟨C, hC, hbound⟩ := exists_re_weilContinuation_real_le_log hW
  refine ⟨544 * C, by positivity, ?_⟩
  intro Y hY η hη hη1
  have hlog : 0 ≤ Real.log (1 + 6 * Y / η) := Real.log_nonneg (by
    have : 0 ≤ 6 * Y / η := by positivity
    linarith)
  calc
    _ ≤ (544 * η * Y * Real.log (1 + 6 * Y / η)) *
        (weilContinuation hW ((1 / 2 + Y : ℝ) : ℂ)).re :=
      integral_regularizedPhase_sub_le_log_moment hW hη hη1 (by linarith)
    _ ≤ (544 * η * Y * Real.log (1 + 6 * Y / η)) * (C * Real.log (Y + 3)) :=
      mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _ = _ := by ring

end RHTower.WeilWorkSettledPhase
