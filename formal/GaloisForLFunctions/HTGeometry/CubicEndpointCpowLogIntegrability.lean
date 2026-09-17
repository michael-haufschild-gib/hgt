import GaloisForLFunctions.HTGeometry.CubicEndpointCpowIntegrability

/-! Logarithmic cubic endpoint subtraction in the physical Mellin strip. -/

namespace GaloisForLFunctions.HTGeometry
open Set MeasureTheory
noncomputable section
set_option autoImplicit false

private theorem abs_log_le_rpow_neg (ε z : ℝ) (hε : 0 < ε)
    (hz : z ∈ Ioc (0 : ℝ) 1) :
    |Real.log z| ≤ (1 / ε) * z ^ (-ε) := by
  have hz0 : 0 < z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have hlog : Real.log z ≤ 0 := Real.log_nonpos hz0.le hz1
  rw [abs_of_nonpos hlog]
  have hp : 0 < z ^ (-ε) := Real.rpow_pos_of_pos hz0 _
  have h := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hz0] at h
  calc
    -Real.log z = ((-ε) * Real.log z) / ε := by field_simp
    _ ≤ (z ^ (-ε) - 1) / ε := div_le_div_of_nonneg_right h hε.le
    _ ≤ z ^ (-ε) / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      linarith
    _ = (1 / ε) * z ^ (-ε) := by ring

/-- A measurable cubic endpoint remainder retains its source-action logarithm
throughout the sharp strip `-4 < Re w`. -/
theorem integrableOn_cpow_log_mul_of_cubic_bound {F : ℝ → ℂ} {C : ℝ} {w : ℂ}
    (hC : 0 ≤ C) (hw : -4 < w.re)
    (hmeas : AEStronglyMeasurable (fun z : ℝ =>
      (z : ℂ) ^ w * (Real.log z : ℂ) * F z) (volume.restrict (Ioc (0 : ℝ) 1)))
    (hbound : ∀ z ∈ Ioc (0 : ℝ) 1, ‖F z‖ ≤ C * z ^ 3) :
    IntegrableOn (fun z : ℝ => (z : ℂ) ^ w * (Real.log z : ℂ) * F z) (Ioc 0 1) := by
  let ε : ℝ := (w.re + 4) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hbase : IntegrableOn (fun z : ℝ => (z : ℂ) ^ ((ε : ℂ) - 1))
      (Ioc (0 : ℝ) 1) := by
    have h := integrableOn_cpow_Ioc (s := (ε : ℂ)) (by simpa using hε)
    convert h using 1
  change Integrable (fun z : ℝ => (z : ℂ) ^ w * (Real.log z : ℂ) * F z)
    (volume.restrict (Ioc 0 1))
  have hmajor : Integrable (fun z : ℝ => (C / ε) * ‖(z : ℂ) ^ ((ε : ℂ) - 1)‖)
      (volume.restrict (Ioc 0 1)) :=
    hbase.norm.const_mul (C / ε)
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hz0 : 0 < z := hz.1
  have hzn : 0 ≤ z := hz0.le
  have hF := hbound z hz
  have hlog := abs_log_le_rpow_neg ε z hε hz
  have hpow : 0 ≤ z ^ w.re := Real.rpow_nonneg hzn _
  have hlognonneg : 0 ≤ |Real.log z| := abs_nonneg _
  have hzthree : 0 ≤ z ^ 3 := pow_nonneg hzn _
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    z ^ w.re * |Real.log z| * ‖F z‖ ≤
        z ^ w.re * |Real.log z| * (C * z ^ 3) :=
      mul_le_mul_of_nonneg_left hF (mul_nonneg hpow hlognonneg)
    _ ≤ z ^ w.re * ((1 / ε) * z ^ (-ε)) * (C * z ^ 3) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hpow) (mul_nonneg hC hzthree)
    _ = (C / ε) * (z ^ w.re * z ^ (-ε) * z ^ (3 : ℝ)) := by
      have hthree : z ^ (3 : ℝ) = z ^ 3 := Real.rpow_natCast z 3
      rw [hthree]
      ring
    _ = (C / ε) * z ^ (w.re + (-ε) + 3) := by
      rw [← Real.rpow_add hz0, ← Real.rpow_add hz0]
    _ = (C / ε) * z ^ (w.re + 3 - ε) := by
      congr 2
      ring
    _ = (C / ε) * ‖(z : ℂ) ^ ((ε : ℂ) - 1)‖ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hz0]
      have he : w.re + 3 - ε = ε - 1 := by
        dsimp [ε]
        ring
      rw [he]
      congr 1

end
end GaloisForLFunctions.HTGeometry
