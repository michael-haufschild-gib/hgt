import GaloisForLFunctions.HTGeometry.CompactExponentialSourceDivision
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindow
import GaloisForLFunctions.HTGeometry.CompensatedAnalyticDivision
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Compact division of the co-Poisson window

The logarithmic window has nonzero exponential moment away from the imaginary
axis. Its classical Euler equation therefore has no solution with both endpoint
values zero. Subtracting the explicit moment correction gives a continuous
compact solution. Analytic compensation followed by division retains the entire
original Xi factor and cannot lower its zero order.
-/

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem coPoissonSubWindow_log_forcing {a b t : ℝ} (ht : t ∈ Icc a b) :
    (Real.exp t : ℂ) *
      coPoissonSubWindowSeed (Real.exp a) (Real.exp b) (Real.exp t) = 1 := by
  rw [coPoissonSubWindowSeed_of_mem
    (show Real.exp t ∈ Icc (Real.exp a) (Real.exp b) from
      ⟨Real.exp_le_exp.mpr ht.1, Real.exp_le_exp.mpr ht.2⟩)]
  exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne')

/-- The uncorrected window has no classical Euler inverse with zero endpoints. -/
theorem coPoissonSubWindow_no_euler_division {a b : ℝ} (hab : a < b)
    {z : ℂ} (hz : z.re ≠ 0) :
    ¬ ∃ h : ℝ → ℂ,
      ContinuousOn h (Icc (Real.exp a) (Real.exp b)) ∧
      h (Real.exp a) = 0 ∧ h (Real.exp b) = 0 ∧
      ∀ x ∈ Ioo (Real.exp a) (Real.exp b),
        HasDerivAt h
          ((coPoissonSubWindowSeed (Real.exp a) (Real.exp b) x -
            (1 - z) * h x) / (x : ℂ)) x := by
  rintro ⟨h, hc, ha, hb, hd⟩
  let H : ℝ → ℂ := fun t => (Real.exp t : ℂ) * h (Real.exp t)
  have hC : ContinuousOn H (Icc a b) :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn.mul
      (hc.comp Real.continuous_exp.continuousOn fun t ht =>
        ⟨Real.exp_le_exp.mpr ht.1, Real.exp_le_exp.mpr ht.2⟩)
  apply sourceDivision_no_zero_boundary_window hab hz
  refine ⟨H, hC, ?_, ?_, ?_⟩
  · simp [H, ha]
  · simp [H, hb]
  · intro t ht
    have hx : Real.exp t ∈ Ioo (Real.exp a) (Real.exp b) :=
      ⟨Real.exp_lt_exp.mpr ht.1, Real.exp_lt_exp.mpr ht.2⟩
    have hExp : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ)) (Real.exp t : ℂ) t :=
      (Real.hasDerivAt_exp t).ofReal_comp
    have hcomp := (hd (Real.exp t) hx).scomp t (Real.hasDerivAt_exp t)
    have hprod := hExp.mul hcomp
    apply hprod.congr_deriv
    dsimp only [H, Function.comp_apply]
    rw [coPoissonSubWindowSeed_of_mem ⟨hx.1.le, hx.2.le⟩]
    simp only [Complex.real_smul]
    have hne : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
    field_simp [hne]
    ring

/-- The explicit moment correction gives compact division in logarithmic coordinates. -/
theorem coPoissonSubWindow_corrected_log_division {a b : ℝ} (hab : a < b) (z : ℂ) :
    ∃ H : ℝ → ℂ, Continuous H ∧ HasCompactSupport H ∧
      (∀ t ∉ Icc a b, H t = 0) ∧ H a = 0 ∧ H b = 0 ∧
      ∀ t ∈ Ioo a b,
        HasDerivAt H
          (z * H t + (Real.exp t : ℂ) *
              coPoissonSubWindowSeed (Real.exp a) (Real.exp b) (Real.exp t) -
            sourceDivisionCorrection z a b (fun _ => 1) t) t := by
  obtain ⟨H, hc, hK, hs, ha, hb, hd⟩ :=
    sourceDivision_corrected_source_has_compact_solution hab z (q := fun _ => 1) continuous_const
  refine ⟨H, hc, hK, hs, ha, hb, ?_⟩
  intro t ht
  rw [coPoissonSubWindow_log_forcing ⟨ht.1.le, ht.2.le⟩]
  exact hd t ht

theorem coPoissonSubWindow_division_correction_ne_zero {a b : ℝ} (hab : a < b)
    {z : ℂ} (hz : z.re ≠ 0) (t : ℝ) :
    sourceDivisionCorrection z a b (fun _ => 1) t ≠ 0 := by
  apply mul_ne_zero (Complex.exp_ne_zero _)
  exact div_ne_zero (sourceDivisionMoment_one_ne_zero hab hz)
    (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hab).ne')

/-- The compensated analytic quotient retains the original Xi factor and zero order. -/
theorem xi_compensated_division_retains_order (rho : ℂ) {G U : ℂ → ℂ}
    (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) (hU0 : U rho = 1) :
    AnalyticAt ℂ (compensatedAnalyticDivision rho xi G U) rho ∧
      (∀ s : ℂ, (s - rho) * compensatedAnalyticDivision rho xi G U s =
        xi s * (G s - G rho * U s)) ∧
      analyticOrderAt xi rho ≤ analyticOrderAt (compensatedAnalyticDivision rho xi G U) rho := by
  have hxi := xi_differentiable.analyticAt rho
  exact ⟨compensatedAnalyticDivision_analyticAt hxi hG hU,
    compensatedAnalyticDivision_factor rho xi G U hU0,
    compensatedAnalyticDivision_order_not_lowered hxi hG hU⟩

/-- A nonzero first jet of the compensated seed preserves the Xi order exactly. -/
theorem xi_compensated_division_order_preserved (rho : ℂ) {G U : ℂ → ℂ}
    (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho)
    (hjet : deriv G rho - G rho * deriv U rho ≠ 0) :
    analyticOrderAt (compensatedAnalyticDivision rho xi G U) rho = analyticOrderAt xi rho :=
  compensatedAnalyticDivision_order_preserved (xi_differentiable.analyticAt rho) hG hU hjet

end
end RHTower
