import GaloisForLFunctions.HTGeometry.GoldenRuleSincIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
open MeasureTheory Set intervalIntegral Filter
open scoped Topology
namespace RHTower


private theorem mul_sinc_sq (x : ℝ) :
    x * Real.sinc x ^ (2 : ℕ) = Real.sin x ^ (2 : ℕ) / x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

/-- The oscillatory sine current is an exact positive square current plus
its endpoint term. No tail estimate or convergence premise is used. -/
theorem integral_sinc_eq_square_current (R : ℝ) (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..(2 * R), Real.sinc t) =
      (∫ u in (0 : ℝ)..R, Real.sinc u ^ (2 : ℕ)) + R * Real.sinc R ^ (2 : ℕ) := by
  have hderiv (x : ℝ) (hx : x ∈ Ioo 0 R) :
      HasDerivAt (fun u : ℝ => u * Real.sinc u ^ (2 : ℕ))
        (2 * Real.sinc (2 * x) - Real.sinc x ^ (2 : ℕ)) x := by
    simp_rw [mul_sinc_sq]
    convert! ((Real.hasDerivAt_sin x).pow 2).div (hasDerivAt_id x) hx.1.ne' using 1
    simp only [id_eq, Pi.pow_apply]
    rw [Real.sinc_of_ne_zero hx.1.ne',
      Real.sinc_of_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx.1.ne'),
      Real.sin_two_mul]
    field_simp [hx.1.ne']
    ring
  have hc1 : Continuous (fun x : ℝ => 2 * Real.sinc (2 * x)) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => Real.sinc x ^ (2 : ℕ)) := by fun_prop
  have h := integral_eq_sub_of_hasDerivAt_of_le hR
    (f := fun u : ℝ => u * Real.sinc u ^ (2 : ℕ))
    (by fun_prop) hderiv ((hc1.sub hc2).intervalIntegrable 0 R)
  rw [integral_sub (hc1.intervalIntegrable 0 R) (hc2.intervalIntegrable 0 R),
    intervalIntegral.integral_const_mul] at h
  have hscale := smul_integral_comp_mul_left (fun x : ℝ => Real.sinc x) (a := 0) (b := R) (2 : ℝ)
  simp only [smul_eq_mul, mul_zero] at hscale
  rw [hscale] at h
  simp only [zero_mul, sub_zero] at h
  linarith

/-- Every positive finite sine current is strictly positive, although its
original integrand changes sign. -/
theorem integral_sinc_pos (T : ℝ) (hT : 0 < T) :
    0 < ∫ t in (0 : ℝ)..T, Real.sinc t := by
  have hR : 0 < T / 2 := half_pos hT
  have hsq : 0 < ∫ u in (0 : ℝ)..(T / 2), Real.sinc u ^ (2 : ℕ) := by
    have h := integral_lt_integral_of_continuousOn_of_le_of_exists_lt hR
      (f := fun _ : ℝ => (0 : ℝ)) (g := fun u : ℝ => Real.sinc u ^ (2 : ℕ))
      continuous_const.continuousOn (by fun_prop)
      (fun u _ => sq_nonneg _) ⟨0, ⟨le_rfl, hR.le⟩, by simp⟩
    simpa only [intervalIntegral.integral_zero] using h
  have h := integral_sinc_eq_square_current (T / 2) hR.le
  rw [show 2 * (T / 2) = T by ring] at h
  rw [h]
  exact add_pos_of_pos_of_nonneg hsq (mul_nonneg hR.le (sq_nonneg _))

private theorem sinc_square_integrable :
    Integrable (fun x : ℝ => Real.sinc x ^ (2 : ℕ)) := by
  apply Integrable.of_integral_ne_zero
  rw [GaloisForLFunctions.HTGeometry.integral_sinc_sq]
  exact Real.pi_ne_zero

private theorem sinc_square_half_mass :
    (∫ x in Ioi (0 : ℝ), Real.sinc x ^ (2 : ℕ)) = Real.pi / 2 := by
  have h := integral_Iic_add_Ioi (b := (0 : ℝ))
    sinc_square_integrable.integrableOn sinc_square_integrable.integrableOn
  have hneg := integral_comp_neg_Iic (0 : ℝ) (fun x : ℝ => Real.sinc x ^ (2 : ℕ))
  simp only [Real.sinc_neg, neg_zero] at hneg
  rw [hneg, GaloisForLFunctions.HTGeometry.integral_sinc_sq] at h
  linarith

private theorem tendsto_sinc_square_endpoint :
    Tendsto (fun R : ℝ => R * Real.sinc R ^ (2 : ℕ)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun R : ℝ => R⁻¹)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact mul_nonneg hR (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [mul_sinc_sq, ← one_div]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one R) hR.le
  · exact tendsto_inv_atTop_zero

/-- The exact finite sine current tends to π/2. This follows from the
corpus Plancherel normalization of sinc² and the positive square identity. -/
theorem tendsto_integral_sinc_atTop :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.sinc t) atTop (𝓝 (Real.pi / 2)) := by
  have hhalf : Tendsto (fun R : ℝ => ∫ u in (0 : ℝ)..R, Real.sinc u ^ (2 : ℕ))
      atTop (𝓝 (Real.pi / 2)) := by
    simpa only [sinc_square_half_mass, id_eq] using
      intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
        sinc_square_integrable.integrableOn (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hdouble : Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..(2 * R), Real.sinc t)
      atTop (𝓝 (Real.pi / 2)) := by
    have h := hhalf.add tendsto_sinc_square_endpoint
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (integral_sinc_eq_square_current R hR).symm
  have hscale : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    Tendsto.atTop_div_const (by positivity : (0 : ℝ) < 2) tendsto_id
  simpa only [Function.comp_def, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    hdouble.comp hscale

end RHTower

