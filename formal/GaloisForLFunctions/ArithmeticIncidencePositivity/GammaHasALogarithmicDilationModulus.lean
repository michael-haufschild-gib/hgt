import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation

/-!
# A uniform logarithmic modulus for Gamma dilation

The derivative has bounded radial weight: compactness handles the origin,
and the vertical trigamma estimate handles the ray. In logarithmic frequency
the Gamma symbol is therefore Lipschitz, uniformly over every frequency.
-/

noncomputable section
open Set MeasureTheory
namespace GaloisForLFunctions.ArithmeticIncidencePositivity
open _root_.RHTower

private theorem exists_radial_gamma_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t * |deriv gammaHardyPhaseRate t| ≤ C := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := deriv gammaHardyPhaseRate)
    (continuous_deriv_gammaHardyPhaseRate.continuousOn :
      ContinuousOn (deriv gammaHardyPhaseRate) (Icc (0 : ℝ) 1))
  let C := max (max B 0) (1 + Real.pi / 4) + 1
  have hC : 0 < C := by
    have h := (le_max_right B 0).trans (le_max_left (max B 0) (1 + Real.pi / 4))
    dsimp only [C]
    linarith only [h]
  refine ⟨C, hC, fun t ht => ?_⟩
  by_cases ht1 : t ≤ 1
  · have hb : |deriv gammaHardyPhaseRate t| ≤ max B 0 :=
      (hB t ⟨ht.le, ht1⟩).trans (le_max_left _ _)
    calc
      _ ≤ t * max B 0 := mul_le_mul_of_nonneg_left hb ht.le
      _ ≤ 1 * max B 0 := mul_le_mul_of_nonneg_right ht1 (le_max_right _ _)
      _ ≤ C := by
        dsimp only [C]
        have h := le_max_left (max B 0) (1 + Real.pi / 4)
        linarith only [h]
  · have h1t : 1 ≤ t := (lt_of_not_ge ht1).le
    calc
      _ ≤ t * (1 / t ^ 2 + Real.pi / (4 * t)) :=
        mul_le_mul_of_nonneg_left (abs_deriv_gammaHardyPhaseRate_le ht) ht.le
      _ = 1 / t + Real.pi / 4 := by field_simp [ht.ne']
      _ ≤ 1 + Real.pi / 4 := add_le_add ((div_le_one ht).mpr h1t) le_rfl
      _ ≤ C := by
        dsimp only [C]
        have h := le_max_right (max B 0) (1 + Real.pi / 4)
        linarith only [h]

/-- Positive frequency rescaling changes the Gamma phase rate by at most
a fixed constant times the absolute logarithmic scale change. -/
theorem exists_gammaHardyPhaseRate_logarithmic_dilation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      |gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t| ≤ C * |Real.log r| := by
  obtain ⟨C, hC, hrad⟩ := exists_radial_gamma_deriv_bound
  have hd (u : ℝ) : HasDerivAt (fun u => gammaHardyPhaseRate (Real.exp u))
      (deriv gammaHardyPhaseRate (Real.exp u) * Real.exp u) u :=
    (differentiable_gammaHardyPhaseRate (Real.exp u)).hasDerivAt.comp u (Real.hasDerivAt_exp u)
  have hdb (u : ℝ) : ‖deriv (fun u => gammaHardyPhaseRate (Real.exp u)) u‖ ≤ C := by
    rw [(hd u).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos u), mul_comm]
    exact hrad _ (Real.exp_pos u)
  have hpos (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
      |gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t| ≤ C * |Real.log r| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := (univ : Set ℝ)) (fun u _ => (hd u).differentiableAt)
      (fun u _ => hdb u) convex_univ (mem_univ (Real.log t)) (mem_univ (Real.log (r * t)))
    simpa only [Real.exp_log ht, Real.exp_log (mul_pos hr ht), Real.norm_eq_abs,
      Real.log_mul hr.ne' ht.ne', add_sub_cancel_right, Real.exp_add,
      Real.exp_log hr] using h
  have habs (t : ℝ) : gammaHardyPhaseRate |t| = gammaHardyPhaseRate t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, gammaHardyPhaseRate_neg]
  refine ⟨C, hC, fun r hr t => ?_⟩
  by_cases ht : t = 0
  · simp only [ht, mul_zero, sub_self, abs_zero]
    exact mul_nonneg hC.le (abs_nonneg _)
  · have h := hpos r |t| hr (abs_pos.mpr ht)
    have heq : r * |t| = |r * t| := by rw [abs_mul, abs_of_pos hr]
    rw [heq, habs, habs] at h
    exact h


/-- The Gamma dilation difference is an integrable bounded form on all of `L²`,
with logarithmic scale modulus. -/
theorem exists_gammaHardyPhaseRate_L2_dilation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ f : SoninL2,
      Integrable (fun t : ℝ =>
        (gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t) * ‖f t‖ ^ 2) ∧
      |∫ t : ℝ, (gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t) * ‖f t‖ ^ 2| ≤
        C * |Real.log r| * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_gammaHardyPhaseRate_logarithmic_dilation_bound
  refine ⟨C, hC, fun r hr f => ?_⟩
  have hsq : Integrable (fun t : ℝ => ‖f t‖ ^ (2 : ℕ)) :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hb := hsq.const_mul (C * |Real.log r|)
  have hcont : Continuous (fun t : ℝ =>
      gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t) :=
    (continuous_gammaHardyPhaseRate.comp (continuous_const.mul continuous_id)).sub
      continuous_gammaHardyPhaseRate
  have hnorm (t : ℝ) :
      ‖(gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t) * ‖f t‖ ^ 2‖ ≤
        C * |Real.log r| * ‖f t‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖f t‖)]
    exact mul_le_mul_of_nonneg_right (hbound r hr t) (sq_nonneg ‖f t‖)
  have hi := hb.mono'
    (hcont.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable f).norm.pow 2))
    (Filter.Eventually.of_forall hnorm)
  refine ⟨hi, ?_⟩
  have h := (norm_integral_le_integral_norm
    (fun t : ℝ => (gammaHardyPhaseRate (r * t) - gammaHardyPhaseRate t) * ‖f t‖ ^ 2)).trans
    (integral_mono hi.norm hb hnorm)
  simpa only [Real.norm_eq_abs, integral_const_mul, ← norm_sq_eq_integral] using h

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.exists_gammaHardyPhaseRate_logarithmic_dilation_bound

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.exists_gammaHardyPhaseRate_L2_dilation_bound
