import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralComplexLogConstant

/-!
# The sectorial logarithmic law

Exactly at the cut the transported finite part at complex time is logarithmic in the principal
branch:

`η₀(e^{-z·} h) = −c h(0)(Log z + γ) + o(1)`,  `z = R w`, `Re w > 0`.

The rescaled cut integral splits into the two rotated halves and `−log R`; the halves evaluate the
principal logarithm of the direction, and the Hadamard remainder is `O(1/R)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology Complex

noncomputable section

/-! ## The rescaled cut integral at the cut -/

theorem intervalIntegrable_cgammaDefect_zero_one (w : ℂ) :
    IntervalIntegrable (cgammaDefect 0 w) volume 0 1 := by
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 ?_
  have h := integrableOn_cgammaDefect_Ioo_one (a := 0) (by norm_num) w
  exact h.congr_set_ae (Ioo_ae_eq_Ioc).symm

theorem intervalIntegrable_cgammaDefect_one_top {R : ℝ} (hR : 1 ≤ R) (w : ℂ) :
    IntervalIntegrable (cgammaDefect 0 w) volume 1 R := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hR]
  exact continuousOn_cgammaDefect w fun t ht => lt_of_lt_of_le zero_lt_one ht.1

theorem intervalIntegrable_cgammaOrd_one_top {R : ℝ} (hR : 1 ≤ R) (w : ℂ) :
    IntervalIntegrable (cgammaOrd 0 w) volume 1 R := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hR]
  refine ContinuousOn.mul ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
    exact continuousOn_id.rpow_const fun x hx =>
      Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

theorem intervalIntegrable_rpow_one_top {R : ℝ} (hR : 1 ≤ R) :
    IntervalIntegrable (fun t : ℝ => ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ)) volume 1 R := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hR]
  refine Complex.continuous_ofReal.continuousOn.comp ?_ (mapsTo_univ _ _)
  exact continuousOn_id.rpow_const fun x hx =>
    Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

theorem integral_rpow_neg_one_interval {R : ℝ} (hR : 1 ≤ R) :
    (∫ t in (1 : ℝ)..R, ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ)) = ((Real.log R : ℝ) : ℂ) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hreal : (∫ t in (1 : ℝ)..R, (t ^ (0 - 1 : ℝ) : ℝ)) = Real.log R := by
    have hcongr : (∫ t in (1 : ℝ)..R, (t ^ (0 - 1 : ℝ) : ℝ)) = ∫ t in (1 : ℝ)..R, t⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hR] at ht
      show (t ^ (0 - 1 : ℝ) : ℝ) = t⁻¹
      rw [zero_sub, Real.rpow_neg_one]
    rw [hcongr, integral_inv_of_pos zero_lt_one hR0]
    simp
  rw [intervalIntegral.integral_ofReal, hreal]

/-- **The rescaled cut integral splits off the logarithm.** -/
theorem ccutIntegral_zero_split {R : ℝ} (hR : 1 ≤ R) (w : ℂ) :
    ccutIntegral 0 ((R : ℂ) * w) =
      clogHead w + (∫ t in (1 : ℝ)..R, cgammaOrd 0 w t) - ((Real.log R : ℝ) : ℂ) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hscale := rpow_mul_ccutIntegral hR0 w 0
  rw [Real.rpow_zero, Complex.ofReal_one, one_mul] at hscale
  have hadj : (∫ t in (0 : ℝ)..1, cgammaDefect 0 w t) + (∫ t in (1 : ℝ)..R, cgammaDefect 0 w t) =
      ∫ t in (0 : ℝ)..R, cgammaDefect 0 w t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cgammaDefect_zero_one w) (intervalIntegrable_cgammaDefect_one_top hR w)
  have hhead : (∫ t in (0 : ℝ)..1, cgammaDefect 0 w t) = clogHead w := by
    rw [clogHead, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have htail : (∫ t in (1 : ℝ)..R, cgammaDefect 0 w t) =
      (∫ t in (1 : ℝ)..R, cgammaOrd 0 w t) - ((Real.log R : ℝ) : ℂ) := by
    have hcongr : (∫ t in (1 : ℝ)..R, cgammaDefect 0 w t) =
        ∫ t in (1 : ℝ)..R, (cgammaOrd 0 w t - ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ)) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      show cgammaDefect 0 w t = cgammaOrd 0 w t - ((t ^ (0 - 1 : ℝ) : ℝ) : ℂ)
      rw [cgammaDefect, cgammaOrd]
      ring
    rw [hcongr, intervalIntegral.integral_sub (intervalIntegrable_cgammaOrd_one_top hR w)
      (intervalIntegrable_rpow_one_top hR), integral_rpow_neg_one_interval hR]
  rw [hscale, ← hadj, hhead, htail]
  ring

/-- **The rotated logarithmic law for the cut integral.** -/
theorem tendsto_ccutIntegral_zero_add_log {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun R : ℝ => ccutIntegral 0 ((R : ℂ) * w) + Complex.log ((R : ℂ) * w)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hwne : w ≠ 0 := by
    intro hcon
    rw [hcon] at hw
    simp at hw
  have htail : Tendsto (fun R : ℝ => ∫ t in (1 : ℝ)..R, cgammaOrd 0 w t) atTop
      (𝓝 (clogTail w)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_cgammaOrd_Ioi_one (by norm_num) hw)
      tendsto_id
  have hlim : Tendsto (fun R : ℝ => clogHead w + ∫ t in (1 : ℝ)..R, cgammaOrd 0 w t) atTop
      (𝓝 (clogHead w + clogTail w)) := tendsto_const_nhds.add htail
  rw [clogHead_add_clogTail hw] at hlim
  have hshift : Tendsto (fun R : ℝ => clogHead w + (∫ t in (1 : ℝ)..R, cgammaOrd 0 w t) +
      Complex.log w) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) - Complex.log w + Complex.log w)) :=
    hlim.add_const _
  rw [sub_add_cancel] at hshift
  refine hshift.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  rw [ccutIntegral_zero_split hR w, Complex.log_ofReal_mul hR0 hwne]
  ring

/-! ## The remainder at the cut -/

theorem tendsto_cremainderIntegral_zero {w : ℂ} (hw : 0 < w.re) {r : ℝ → ℝ}
    (hrc : Continuous r) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B) :
    Tendsto (fun R : ℝ => cremainderIntegral 0 ((R : ℂ) * w) r) atTop (𝓝 0) := by
  set C : ℝ := B * (w.re ⁻¹ * Real.Gamma (0 + 1)) with hCdef
  have hlim : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hzre : ((R : ℂ) * w).re = R * w.re := by simp
  have hz : 0 < ((R : ℂ) * w).re := by rw [hzre]; positivity
  have hbound := norm_cremainderIntegral_le (a := 0) (by norm_num) hz hrc hB0 hB
  rw [hzre] at hbound
  have hpow : (R * w.re) ^ (-(0 + 1) : ℝ) = R⁻¹ * w.re ⁻¹ := by
    rw [show (-(0 + 1) : ℝ) = -1 by ring, Real.mul_rpow hR.le hw.le, Real.rpow_neg_one,
      Real.rpow_neg_one]
  rw [hpow] at hbound
  calc ‖cremainderIntegral 0 ((R : ℂ) * w) r‖ ≤ B * (R⁻¹ * w.re ⁻¹ * Real.Gamma (0 + 1)) := hbound
    _ = C / R := by rw [hCdef]; field_simp

/-! ## The sectorial logarithmic law -/

/-- **The sectorial logarithmic contact law.**  At the cut the transported finite part at complex
time is `− c h(0)(Log z + γ) + o(1)` along every ray of the right half-plane. -/
theorem tendsto_ctransportedFinitePart_log (c : ℝ) {w : ℂ} (hw : 0 < w.re) {h : ℝ → ℝ}
    (hh : IsSmoothReal h) :
    Tendsto (fun R : ℝ => ctransportedFinitePart c 0 ((R : ℂ) * w) h +
        (c : ℂ) * (h 0 : ℂ) *
          (Complex.log ((R : ℂ) * w) + (Real.eulerMascheroniConstant : ℂ))) atTop (𝓝 0) := by
  set r : ℝ → ℝ := hadamardAvg 0 (deriv h) with hrdef
  have hrS : IsSmoothReal r := isSmoothReal_hadamardAvg 0 hh.derivSmooth
  have hrc : Continuous r := hrS.continuous
  have hr : ∀ s, h s = h 0 + s * r s := hadamard_eq hh
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hrc.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ Ioo (0 : ℝ) 1, |r s| ≤ B := fun s hs =>
    le_trans (hB₀ s ⟨hs.1.le, hs.2.le⟩) (le_max_left _ _)
  have hcut : Tendsto (fun R : ℝ => ccutIntegral 0 ((R : ℂ) * w) + Complex.log ((R : ℂ) * w) +
      (Real.eulerMascheroniConstant : ℂ)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) + (Real.eulerMascheroniConstant : ℂ))) :=
    (tendsto_ccutIntegral_zero_add_log hw).add_const _
  rw [neg_add_cancel] at hcut
  have hrem := tendsto_cremainderIntegral_zero hw hrc hB0 hB
  have hmain : Tendsto (fun R : ℝ => (c : ℂ) * ((h 0 : ℂ) *
      (ccutIntegral 0 ((R : ℂ) * w) + Complex.log ((R : ℂ) * w) +
        (Real.eulerMascheroniConstant : ℂ)) + cremainderIntegral 0 ((R : ℂ) * w) r)) atTop
      (𝓝 ((c : ℂ) * ((h 0 : ℂ) * 0 + 0))) :=
    Tendsto.const_mul _ ((hcut.const_mul (h 0 : ℂ)).add hrem)
  rw [show (c : ℂ) * ((h 0 : ℂ) * 0 + 0) = 0 by ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hz : 0 < ((R : ℂ) * w).re := by
    have hzre : ((R : ℂ) * w).re = R * w.re := by simp
    rw [hzre]
    positivity
  rw [ctransportedFinitePart_split c (a := 0) (by norm_num) hz hr hrc hB]
  rw [Complex.ofReal_zero, div_zero]
  ring

end

end GaloisForLFunctions.HTGeometry.Interfinity
