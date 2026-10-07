import GaloisForLFunctions.RHTower.WeilWorkDeficitFourierTransport

/-!
# Fourier transport of individual Xi-copy Poisson kernels

The widths at abscissa two lie between one and two. Their endpoint errors are bounded by
three halves of the fixed-width leakage, uniformly in frequency. The actual copy series
admits complex character-weighted integration on every bounded positive height interval.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

private def zeroCharacter (k t : ℝ) : ℂ := Complex.exp (((k * t : ℝ) : ℂ) * I)
private def zeroPoisson (b r t : ℝ) : ℝ := b / (b ^ 2 + (t - r) ^ 2)

private theorem norm_zeroCharacter (k t : ℝ) : ‖zeroCharacter k t‖ = 1 := by
  simp [zeroCharacter, Complex.norm_exp]

private theorem continuous_zeroCharacter (k : ℝ) : Continuous (zeroCharacter k) := by
  unfold zeroCharacter
  fun_prop

private theorem continuous_zeroPoisson {b : ℝ} (hb : 0 < b) (r : ℝ) :
    Continuous (zeroPoisson b r) :=
  continuous_const.div (by fun_prop) (fun _ => by positivity)

private theorem zeroPoisson_nonneg {b : ℝ} (hb : 0 < b) (r t : ℝ) :
    0 ≤ zeroPoisson b r t := by unfold zeroPoisson; positivity

private theorem integrable_zeroPoisson {b : ℝ} (hb : 0 < b) (r : ℝ) :
    Integrable (zeroPoisson b r) := by
  change Integrable (fun t : ℝ => b / (b ^ 2 + (t - r) ^ 2))
  simpa only [div_eq_mul_inv] using
    ((GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq hb).comp_sub_right r).const_mul b

private theorem integral_zeroPoisson {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ∫ t, zeroPoisson b r t = Real.pi := by
  simp only [zeroPoisson, div_eq_mul_inv, integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : ℝ => (b ^ 2 + x ^ 2)⁻¹) r,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq hb]
  field_simp [hb.ne']

private theorem integral_zeroPoisson_window {T : ℝ} (hT : 0 ≤ T) (r : ℝ) :
    ∫ t in Ioc 0 T, zeroPoisson (3 / 2) r t = countKernel T r := by
  rw [← intervalIntegral.integral_of_le hT]
  convert integral_poissonKernel_eq T r using 1
  congr 1
  funext t
  unfold zeroPoisson
  congr 2
  ring

private theorem norm_zeroProduct {b : ℝ} (hb : 0 < b) (k r t : ℝ) :
    ‖zeroCharacter k t * (zeroPoisson b r t : ℂ)‖ = zeroPoisson b r t := by
  rw [norm_mul, norm_zeroCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zeroPoisson_nonneg hb r t)]

private theorem integrable_zeroProduct {b : ℝ} (hb : 0 < b) (k r : ℝ) :
    Integrable (fun t => zeroCharacter k t * (zeroPoisson b r t : ℂ)) := by
  refine (integrable_zeroPoisson hb r).mono'
    (((continuous_zeroCharacter k).mul
      (Complex.continuous_ofReal.comp (continuous_zeroPoisson hb r))).aestronglyMeasurable)
    (Eventually.of_forall fun t => (norm_zeroProduct hb k r t).le)

private theorem integral_zeroProduct {b : ℝ} (hb : 0 < b) (k r : ℝ) :
    (∫ t, zeroCharacter k t * (zeroPoisson b r t : ℂ)) =
      ((Real.pi * Real.exp (-(b * |k|)) : ℝ) : ℂ) * zeroCharacter k r := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun t => zeroCharacter k t * (zeroPoisson b r t : ℂ)) r]
  have hpt (x : ℝ) : zeroCharacter k (x + r) * (zeroPoisson b r (x + r) : ℂ) =
      (b : ℂ) * zeroCharacter k r *
        (Complex.exp (((x * k : ℝ) : ℂ) * I) * ((b ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹) := by
    have he : zeroCharacter k (x + r) =
        zeroCharacter k r * Complex.exp (((x * k : ℝ) : ℂ) * I) := by
      unfold zeroCharacter
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hp : (zeroPoisson b r (x + r) : ℂ) =
        (b : ℂ) * ((b ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ := by
      simp [zeroPoisson, div_eq_mul_inv]
    rw [he, hp]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_cexp_mul_inv_sq_add_sq hb]
  push_cast
  field_simp [hb.ne']

private theorem zeroPoisson_le_fixed {b : ℝ} (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (r t : ℝ) :
    zeroPoisson b r t ≤ (3 / 2) * zeroPoisson (3 / 2) r t := by
  have hb : 0 < b := by linarith
  unfold zeroPoisson
  calc
    b / (b ^ 2 + (t - r) ^ 2) ≤ (9 / 4) / ((3 / 2) ^ 2 + (t - r) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 := mul_nonneg hb.le (show 0 ≤ b - 1 by linarith)
      have h2 := mul_nonneg (show 0 ≤ 9 / 4 - b by linarith) (sq_nonneg (t - r))
      nlinarith
    _ = _ := by ring

private theorem norm_zeroProduct_window_error {T b : ℝ} (hT : 0 ≤ T)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 2) (k r : ℝ) :
    ‖(∫ t in Ioc 0 T, zeroCharacter k t * (zeroPoisson b r t : ℂ)) -
        (Ioc 0 T).indicator
          (fun r => ((Real.pi * Real.exp (-(b * |k|)) : ℝ) : ℂ) * zeroCharacter k r) r‖ ≤
      (3 / 2) * deficitPoissonLeakage T r := by
  have hb : 0 < b := by linarith
  have hfixed : 0 < (3 / 2 : ℝ) := by norm_num
  have hnorm (S : Set ℝ) :
      ‖∫ t in S, zeroCharacter k t * (zeroPoisson b r t : ℂ)‖ ≤
        (3 / 2) * ∫ t in S, zeroPoisson (3 / 2) r t := by
    calc
      _ ≤ ∫ t in S, ‖zeroCharacter k t * (zeroPoisson b r t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ t in S, zeroPoisson b r t := by simp_rw [norm_zeroProduct hb]
      _ ≤ ∫ t in S, (3 / 2) * zeroPoisson (3 / 2) r t :=
        integral_mono (integrable_zeroPoisson hb r).restrict
          ((integrable_zeroPoisson hfixed r).const_mul (3 / 2)).restrict
          (zeroPoisson_le_fixed hb1 hb2 r)
      _ = _ := integral_const_mul _ _
  by_cases hr : r ∈ Ioc 0 T
  · rw [indicator_of_mem hr, ← integral_zeroProduct hb k r,
      ← integral_add_compl measurableSet_Ioc (integrable_zeroProduct hb k r),
      sub_add_cancel_left, norm_neg]
    apply (hnorm (Ioc 0 T)ᶜ).trans
    rw [setIntegral_compl measurableSet_Ioc (integrable_zeroPoisson hfixed r),
      integral_zeroPoisson hfixed, integral_zeroPoisson_window hT]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [deficitPoissonLeakage, indicator_of_mem hr]
    linarith [neg_le_abs (countKernel T r - Real.pi)]
  · rw [indicator_of_notMem hr, sub_zero]
    apply (hnorm (Ioc 0 T)).trans
    rw [integral_zeroPoisson_window hT]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [deficitPoissonLeakage, indicator_of_notMem hr, sub_zero]
    exact le_abs_self _

/-- The actual copy kernel has the fixed-width endpoint error bound, uniformly in frequency. -/
theorem norm_deficitCopyFourierIntegral_sub_le {T : ℝ} (hT : 0 ≤ T) (k : ℝ) (q : XiZeroCopy) :
    ‖(∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) * (copyPoisson 2 t q : ℂ)) -
        (Ioc 0 T).indicator
          (fun r => ((Real.pi * Real.exp (-((2 - (q.1 : ℂ).re) * |k|)) : ℝ) : ℂ) *
            Complex.exp (((k * r : ℝ) : ℂ) * I)) (q.1 : ℂ).im‖ ≤
      (3 / 2) * deficitPoissonLeakage T (q.1 : ℂ).im := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  exact norm_zeroProduct_window_error hT (by linarith) (by linarith) k (q.1 : ℂ).im

/-- Complex character-weighted integration of the actual full Xi-copy Poisson series. -/
theorem hasSum_deficitCopyFourierIntegral {T : ℝ} (hT : 0 ≤ T) (k : ℝ) :
    HasSum (fun q : XiZeroCopy => ∫ t in Ioc 0 T,
      Complex.exp (((k * t : ℝ) : ℂ) * I) * (copyPoisson 2 t q : ℂ))
      (∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) *
        ((logDeriv xi ((2 : ℂ) + t * I)).re : ℂ)) := by
  set C : ℝ := (1 + (2 * T + 2) ^ 2) / (2 - 1) + 8 * 2
  simp only [← intervalIntegral.integral_of_le hT]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := T)
    (F := fun q : XiZeroCopy => fun t : ℝ => zeroCharacter k t * (copyPoisson 2 t q : ℂ))
    (f := fun t => zeroCharacter k t * ((logDeriv xi ((2 : ℂ) + t * I)).re : ℂ))
    (fun q _ => C * (1 / (1 + (q.1 : ℂ).im ^ 2)))
    (fun q => ((continuous_zeroCharacter k).mul
      (Complex.continuous_ofReal.comp (continuous_copyPoisson (by norm_num) q))).aestronglyMeasurable)
    (fun q => ?_) ?_ ?_ ?_
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hT] at ht
    rw [norm_mul, norm_zeroCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (copyPoisson_pos (by norm_num) t q).le]
    exact copyPoisson_le_local (by norm_num) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) q
  · exact Eventually.of_forall fun _ _ => summable_inv_one_add_sq_im.mul_left C
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t _ => ?_
    have hsum := (summable_copyPoisson (σ := 2) (by norm_num) t).hasSum
    have heq := re_logDeriv_xi_eq_tsum_copyPoisson (σ := 2) (by norm_num) t
    push_cast at heq
    rw [heq]
    exact ((RCLike.hasSum_ofReal ℂ).mpr hsum).mul_left (zeroCharacter k t)

end RHTower.WeilSpectral
end
