import GaloisForLFunctions.HTGeometry.DigammaPositiveRealAsymptotic
import GaloisForLFunctions.RHTower.CompletedPrimeGammaAllOrderFarRight
import GaloisForLFunctions.RHTower.XiShiftedMomentSourceJet

/-!
# Order-zero completed-Xi far-right asymptotic

Positive derivative orders are polynomially normalized.  Order zero is logarithmic and therefore
requires a separate argument.  The continuous positive-real digamma asymptotic supplies the sole
leading term; rational and Euler legs vanish after division by `log x`.
-/

open Complex Filter Topology LSeries

namespace RHTower

noncomputable section

private theorem tendsto_log_half_div_log :
    Tendsto (fun x : ℝ => Real.log (x / 2) / Real.log x) atTop (nhds 1) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hconst : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog
  have hmain : Tendsto (fun x : ℝ => 1 - Real.log 2 / Real.log x)
      atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub hconst
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  rw [Real.log_div (ne_of_gt (lt_trans zero_lt_one hx)) (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [hlogne]

/-- Half-argument digamma carries exactly one logarithmic unit. -/
theorem tendsto_re_digamma_half_div_log :
    Tendsto
      (fun x : ℝ => (Complex.digamma ((x : ℂ) / 2)).re / Real.log x)
      atTop (nhds 1) := by
  have hhalfTop : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have herror :=
    GaloisForLFunctions.HTGeometry.tendsto_re_digamma_ofReal_sub_log.comp hhalfTop
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have herrorDiv : Tendsto
      (fun x : ℝ =>
        ((Complex.digamma (((x / 2 : ℝ) : ℂ))).re - Real.log (x / 2)) /
          Real.log x)
      atTop (nhds 0) := herror.div_atTop hlog
  have hsum := herrorDiv.add tendsto_log_half_div_log
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  push_cast
  field_simp [hlogne]
  ring

private theorem tendsto_completedRationalLeg_zero_div_log :
    Tendsto
      (fun x : ℝ =>
        (iteratedDeriv 0
          (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2)
          (x : ℂ)).re / Real.log x)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hshift : Tendsto (fun x : ℝ => (x - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  have hnum : Tendsto
      (fun x : ℝ => x⁻¹ + (x - 1)⁻¹ - Real.log Real.pi / 2)
      atTop (nhds (-(Real.log Real.pi / 2))) := by
    simpa using (hinv.add hshift).sub_const (Real.log Real.pi / 2)
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hdiv := hnum.div_atTop hlog
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hx1 : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hzero : (1 / (x : ℂ)) = ((x⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp [hx0]
  have hone : (1 / ((x : ℂ) - 1)) = (((x - 1)⁻¹ : ℝ) : ℂ) := by
    rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring]
    push_cast
    field_simp [hx1]
  have hzeroRe : (1 / (x : ℂ)).re = x⁻¹ := by rw [hzero, Complex.ofReal_re]
  have honeRe : (1 / ((x : ℂ) - 1)).re = (x - 1)⁻¹ := by
    rw [hone, Complex.ofReal_re]
  simp only [iteratedDeriv_zero, Complex.sub_re, Complex.add_re]
  rw [hzeroRe, honeRe]
  norm_num

private theorem tendsto_completedEulerLeg_zero_re_div_log :
    Tendsto
      (fun x : ℝ =>
        (((-1 : ℂ) * LSeries (vonMangoldtLogCoeff 0) (x : ℂ)).re) / Real.log x)
      atTop (nhds 0) := by
  have heuler := tendsto_scaled_completedEulerLeg 0
  have hre : Tendsto
      (fun x : ℝ => (((-1 : ℂ) * LSeries (vonMangoldtLogCoeff 0) (x : ℂ)).re))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp heuler
  exact hre.div_atTop Real.tendsto_log_atTop

/-- Exact logarithmic slope of the completed Xi logarithmic derivative on the positive ray. -/
theorem tendsto_xiRayLogDeriv_div_log :
    Tendsto (fun x : ℝ => xiRayLogDeriv x / Real.log x) atTop (nhds (1 / 2 : ℝ)) := by
  have hrat := tendsto_completedRationalLeg_zero_div_log
  have hgamma := tendsto_re_digamma_half_div_log.const_mul (1 / 2 : ℝ)
  have heuler := tendsto_completedEulerLeg_zero_re_div_log
  have hsum := (hrat.add hgamma).add heuler
  have hlim : (0 : ℝ) + (1 / 2) * 1 + 0 = 1 / 2 := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hsplit := iteratedDeriv_xiLogDeriv_split 0 (s := (x : ℂ)) (by simpa using hx)
  simp only [iteratedDeriv_zero] at hsplit
  change _ = (xiLogDeriv (x : ℂ)).re / Real.log x
  rw [hsplit, Complex.add_re]
  simp only [iteratedDeriv_zero, vonMangoldtLogCoeff, Function.iterate_zero_apply,
    Complex.add_re, Complex.mul_re]
  norm_num
  ring

end

end RHTower
