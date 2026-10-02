import GaloisForLFunctions.RHTower.SoninDilationTimeBandTrace
import GaloisForLFunctions.RHTower.SoninSineTraceCurrent

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower


private theorem finite_fourier_row (a w : ℝ) (ha : 0 < a) :
    (∫ y in Icc (-a) a, Complex.exp (((w * y : ℝ) : ℂ) * Complex.I)) =
      ((2 * a * Real.sinc (w * a) : ℝ) : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  by_cases hw : w = 0
  · simp [hw]
    ring
  · have hrow : (∫ y in (-a)..a, Complex.exp (((w * y : ℝ) : ℂ) * Complex.I)) =
        compactFourier (fun _ => (1 : ℂ)) (-a) a (w : ℂ) := by
      unfold compactFourier
      apply intervalIntegral.integral_congr
      intro y _
      simp only [one_mul]
      congr 1
      push_cast
      ring
    rw [hrow, compactFourier_one_eq a hw,
      Real.sinc_of_ne_zero (mul_ne_zero hw ha.ne')]
    congr 1
    field_simp

private theorem sinc_symmetric_interval (L : ℝ) :
    (∫ x in (-L)..L, Real.sinc x) = 2 * ∫ x in (0 : ℝ)..L, Real.sinc x := by
  have hneg := intervalIntegral.integral_comp_neg (fun x : ℝ => Real.sinc x)
    (a := (0 : ℝ)) (b := L)
  simp only [Real.sinc_neg, neg_zero] at hneg
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (Real.continuous_sinc.intervalIntegrable (-L) 0)
    (Real.continuous_sinc.intervalIntegrable 0 L)
  rw [← hneg] at hsplit
  linarith

/-- Exact scalar form of the actual finite-window trace kernel. -/
theorem sonin_timeBand_window_eq_sine_current
    (a c : ℝ) (ha : 0 < a) (hc : c ≠ 0) :
    (∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
      Complex.exp (((2 * Real.pi * c * x * y : ℝ) : ℂ) * Complex.I)) =
    (((2 / (Real.pi * c)) *
      ∫ t in (0 : ℝ)..(2 * Real.pi * c * a ^ (2 : ℕ)), Real.sinc t : ℝ) : ℂ) := by
  have hrow (x : ℝ) := finite_fourier_row a (2 * Real.pi * c * x) ha
  simp_rw [hrow]
  rw [integral_complex_ofReal, MeasureTheory.integral_const_mul]
  congr 1
  let k := 2 * Real.pi * c * a
  have hk : k ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hc) ha.ne'
  have harg (x : ℝ) : (2 * Real.pi * c * x) * a = k * x := by dsimp [k]; ring
  simp_rw [harg]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    intervalIntegral.integral_comp_mul_left _ hk]
  rw [show k * -a = -(k * a) by ring, sinc_symmetric_interval]
  change 2 * a * (k⁻¹ * (2 * ∫ t in (0 : ℝ)..k * a, Real.sinc t)) = _
  have hbound : k * a = 2 * Real.pi * c * a ^ (2 : ℕ) := by dsimp [k]; ring
  rw [hbound]
  dsimp [k]
  field_simp

/-- The apparent oscillatory window current is strictly positive at every
positive frequency and positive aperture. -/
theorem sonin_timeBand_window_re_pos (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    0 < (∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
      Complex.exp (((2 * Real.pi * c * x * y : ℝ) : ℂ) * Complex.I)).re := by
  rw [sonin_timeBand_window_eq_sine_current a c ha hc.ne']
  simp only [Complex.ofReal_re]
  exact mul_pos (div_pos (by norm_num) (mul_pos Real.pi_pos hc))
    (integral_sinc_pos _ (by positivity))

/-- Exact large-frequency coefficient of the finite-window trace current. -/
theorem tendsto_sonin_timeBand_window_scaled (a : ℝ) (ha : 0 < a) :
    Tendsto (fun c : ℝ => c * (∫ x in Icc (-a) a, ∫ y in Icc (-a) a,
      Complex.exp (((2 * Real.pi * c * x * y : ℝ) : ℂ) * Complex.I)).re)
      atTop (𝓝 1) := by
  have hscale : Tendsto (fun c : ℝ => 2 * Real.pi * c * a ^ (2 : ℕ)) atTop atTop := by
    have h := (tendsto_id : Tendsto (fun c : ℝ => c) atTop atTop).const_mul_atTop
      (by positivity : 0 < 2 * Real.pi * a ^ (2 : ℕ))
    convert h using 1
    funext c
    simp only [id_eq]
    ring
  have h := tendsto_const_nhds.mul (tendsto_integral_sinc_atTop.comp hscale)
    (a := (2 / Real.pi : ℝ))
  have hnorm : (2 / Real.pi) * (Real.pi / 2) = (1 : ℝ) := by field_simp
  rw [hnorm] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  rw [sonin_timeBand_window_eq_sine_current a c ha hc.ne']
  simp only [Complex.ofReal_re, Function.comp_apply]
  field_simp

end RHTower

