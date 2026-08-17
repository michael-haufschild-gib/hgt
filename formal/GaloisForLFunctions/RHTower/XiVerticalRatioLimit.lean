import GaloisForLFunctions.RHTower.XiVerticalPhaseTwo

/-!
# The vertical contribution is asymptotically `(T log T)/2`

Every term of the vertical splitting except the Gamma phase is either bounded (the two arctangents
and the zeta phase) or linear (the `log π` term), so after division by `T log T` only the Gamma
phase survives, and it contributes `1/2` because its argument is halved.
-/

open Filter Topology Complex

noncomputable section

namespace RHTower

theorem tendsto_bounded_div_TlogT {f : ℝ → ℝ} {C : ℝ} (hf : ∀ T, |f T| ≤ C) :
    Tendsto (fun T => f T / (T * Real.log T)) atTop (𝓝 0) := by
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id Real.tendsto_log_atTop
  have hg : Tendsto (fun T : ℝ => C / (T * Real.log T)) atTop (𝓝 0) := by
    have h := hmul.inv_tendsto_atTop
    have h2 : Tendsto (fun T : ℝ => C * (T * Real.log T)⁻¹) atTop (𝓝 (C * 0)) :=
      h.const_mul C
    simpa [div_eq_mul_inv] using h2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hpos : 0 < T * Real.log T := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
  gcongr
  exact hf T

/-- **The vertical contribution has ratio `1/2`.** -/
theorem tendsto_vertical_ratio :
    Tendsto (fun T : ℝ =>
        (∫ y in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (y : ℂ) * I)).re) / (T * Real.log T))
      atTop (𝓝 (1 / 2)) := by
  have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hmul : Tendsto (fun T : ℝ => T * Real.log T) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id hlogtop
  -- the arctangent head
  have hA : Tendsto (fun T : ℝ =>
      (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))) / (T * Real.log T))
      atTop (𝓝 0) := tendsto_bounded_div_TlogT abs_integral_rational_head_le
  -- the zeta phase
  have hZ : Tendsto (fun T : ℝ =>
      (∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re) / (T * Real.log T))
      atTop (𝓝 0) := tendsto_bounded_div_TlogT abs_integral_re_logDeriv_zeta_two_le
  -- the `log π` term
  have hπ : Tendsto (fun T : ℝ => (T * Real.log Real.pi / 2) / (T * Real.log T)) atTop (𝓝 0) := by
    have hv : Tendsto (fun T : ℝ => 1 / Real.log T) atTop (𝓝 0) := by
      have h := hlogtop.inv_tendsto_atTop
      refine h.congr fun T => ?_
      simp [Pi.inv_apply, one_div]
    have h2 : Tendsto (fun T : ℝ => (Real.log Real.pi / 2) * (1 / Real.log T)) atTop
        (𝓝 ((Real.log Real.pi / 2) * 0)) := hv.const_mul _
    have h2' : Tendsto (fun T : ℝ => (Real.log Real.pi / 2) * (1 / Real.log T)) atTop (𝓝 0) := by
      simpa using h2
    refine h2'.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hlog : 0 < Real.log T := Real.log_pos hT
    have hT0 : 0 < T := by linarith
    field_simp
  -- the Gamma phase
  have hΦ : Tendsto (fun T : ℝ => gammaVerticalPhase 1 (T / 2) / (T * Real.log T))
      atTop (𝓝 (1 / 2)) := by
    have hhalf : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => by linarith⟩
    have hratio := (tendsto_gammaVerticalPhase_ratio (σ := 1) (by norm_num)).comp hhalf
    have hlogratio : Tendsto (fun T : ℝ => Real.log (T / 2) / Real.log T) atTop (𝓝 1) := by
      have hsub : Tendsto (fun T : ℝ => 1 - Real.log 2 / Real.log T) atTop (𝓝 (1 - 0)) := by
        have hv : Tendsto (fun T : ℝ => 1 / Real.log T) atTop (𝓝 0) := by
          have h := hlogtop.inv_tendsto_atTop
          refine h.congr fun T => ?_
          simp [Pi.inv_apply, one_div]
        have h2 : Tendsto (fun T : ℝ => Real.log 2 * (1 / Real.log T)) atTop
            (𝓝 (Real.log 2 * 0)) := hv.const_mul _
        have h2' : Tendsto (fun T : ℝ => Real.log 2 * (1 / Real.log T)) atTop (𝓝 0) := by
          simpa using h2
        have h3 : Tendsto (fun T : ℝ => Real.log 2 / Real.log T) atTop (𝓝 0) := by
          refine h2'.congr fun T => ?_
          ring
        exact tendsto_const_nhds.sub h3
      have hsub' : Tendsto (fun T : ℝ => 1 - Real.log 2 / Real.log T) atTop (𝓝 1) := by
        simpa using hsub
      refine hsub'.congr' ?_
      filter_upwards [eventually_gt_atTop (2 : ℝ)] with T hT
      have hlog : 0 < Real.log T := Real.log_pos (by linarith)
      have hT0 : 0 < T := by linarith
      rw [Real.log_div hT0.ne' (by norm_num)]
      field_simp
    have hprod : Tendsto (fun T : ℝ =>
        (gammaVerticalPhase 1 (T / 2) / ((T / 2) * Real.log (T / 2)))
          * ((Real.log (T / 2) / Real.log T) / 2)) atTop (𝓝 (1 * (1 / 2))) :=
      hratio.mul ((hlogratio.div_const 2))
    have hprod' : Tendsto (fun T : ℝ =>
        (gammaVerticalPhase 1 (T / 2) / ((T / 2) * Real.log (T / 2)))
          * ((Real.log (T / 2) / Real.log T) / 2)) atTop (𝓝 (1 / 2)) := by
      simpa using hprod
    refine hprod'.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have hlog2 : Real.log (T / 2) ≠ 0 := by
      have h1 : (1 : ℝ) < T / 2 := by linarith
      exact (Real.log_pos h1).ne'
    field_simp
  have hsum : Tendsto (fun T : ℝ =>
      (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))) / (T * Real.log T)
        - (T * Real.log Real.pi / 2) / (T * Real.log T)
        + gammaVerticalPhase 1 (T / 2) / (T * Real.log T)
        + (∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)
            / (T * Real.log T)) atTop (𝓝 (0 - 0 + 1 / 2 + 0)) :=
    ((hA.sub hπ).add hΦ).add hZ
  have hsum' : Tendsto (fun T : ℝ =>
      (∫ y in (0 : ℝ)..T, (2 / (4 + y ^ 2) + 1 / (1 + y ^ 2))) / (T * Real.log T)
        - (T * Real.log Real.pi / 2) / (T * Real.log T)
        + gammaVerticalPhase 1 (T / 2) / (T * Real.log T)
        + (∫ y in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + (y : ℂ) * I)).re)
            / (T * Real.log T)) atTop (𝓝 (1 / 2)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [integral_re_logDeriv_xi_two T]
  ring

end RHTower
