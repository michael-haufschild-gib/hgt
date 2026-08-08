import GaloisForLFunctions.HTGeometry.ProlateKernelSymmetry
import GaloisForLFunctions.HTGeometry.SturmSelfAdjoint

/-!
# Differentiating the finite Fourier transform under the integral

The finite Fourier transform of an integrable band-limited function may be differentiated under the
integral sign.  The kernel is unimodular, its parameter derivative is bounded by the bandwidth on
the band, and the integrand is therefore dominated by a fixed multiple of the function.

This is the analytic step that turns the kernel identity `L_t K = L_x K` into a commutation of the
prolate differential operator with the finite Fourier transform.
-/

open MeasureTheory intervalIntegral Set

namespace HTGeometry

theorem continuous_prolateKernel_snd (c y : ℝ) : Continuous fun t : ℝ => prolateKernel c y t :=
  Complex.continuous_exp.comp (by fun_prop)

set_option maxHeartbeats 1000000 in
/-- **Differentiation under the integral sign for the finite Fourier transform.** -/
theorem hasDerivAt_prolateTransform {c : ℝ} {f : ℝ → ℂ}
    (hint : IntervalIntegrable f volume (-1) 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in (-1 : ℝ)..1, prolateKernel c y t * f t)
      (∫ t in (-1 : ℝ)..1, Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t * f t) x := by
  have huIoc : Set.uIoc (-1 : ℝ) 1 = Set.Ioc (-1 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [huIoc]
    exact hint.1.1
  have hFmeas : ∀ᶠ y in nhds x,
      AEStronglyMeasurable (fun t : ℝ => prolateKernel c y t * f t)
        (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    filter_upwards with y
    exact ((continuous_prolateKernel_snd c y).aestronglyMeasurable).mul hfm
  have hFint : IntervalIntegrable (fun t : ℝ => prolateKernel c x t * f t) volume (-1) 1 :=
    hint.continuousOn_mul (continuous_prolateKernel_snd c x).continuousOn
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t * f t)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine AEStronglyMeasurable.mul ?_ hfm
    exact (((Complex.continuous_ofReal.const_mul (Complex.I * (c : ℂ))).mul
      (continuous_prolateKernel_snd c x))).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ y ∈ Metric.ball x 1,
      ‖Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t‖ ≤ |c| * ‖f t‖ := by
    refine Filter.Eventually.of_forall ?_
    intro t ht y _
    have habs : |t| ≤ 1 := by
      rw [huIoc] at ht
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_prolateKernel_deriv_le habs y) (norm_nonneg _)
  have hboundint : IntervalIntegrable (fun t : ℝ => |c| * ‖f t‖) volume (-1) 1 :=
    hint.norm.const_mul _
  have hdiff : ∀ᵐ t : ℝ, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ y ∈ Metric.ball x 1,
      HasDerivAt (fun z : ℝ => prolateKernel c z t * f t)
        (Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t) y :=
    Filter.Eventually.of_forall fun t _ y _ => (hasDerivAt_prolateKernel_fst c y t).mul_const (f t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun y t => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t)
    (bound := fun t => |c| * ‖f t‖) (Metric.ball_mem_nhds x one_pos) hFmeas hFint hF'meas hbound hboundint hdiff).2

/-- Multiplying by the bounded factor `i c t` preserves interval integrability on the band. -/
theorem intervalIntegrable_mul_kernelFactor {c : ℝ} {f : ℝ → ℂ}
    (hint : IntervalIntegrable f volume (-1) 1) :
    IntervalIntegrable (fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * f t) volume (-1) 1 := by
  refine hint.continuousOn_mul ?_
  exact (Continuous.continuousOn (by fun_prop))

/-- The transform written with the factor absorbed into the function. -/
theorem prolateTransform_factor {c : ℝ} (f : ℝ → ℂ) (y : ℝ) :
    ∫ t in (-1 : ℝ)..1, prolateKernel c y t * (Complex.I * (c : ℂ) * (t : ℂ) * f t)
      = ∫ t in (-1 : ℝ)..1, Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

set_option maxHeartbeats 1000000 in
/-- **The second derivative of the finite Fourier transform.**  Differentiating twice under the
integral multiplies the kernel by the square of its parameter factor. -/
theorem hasDerivAt_prolateTransform_deriv {c : ℝ} {f : ℝ → ℂ}
    (hint : IntervalIntegrable f volume (-1) 1) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∫ t in (-1 : ℝ)..1, Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t)
      (∫ t in (-1 : ℝ)..1,
        Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t *
          (Complex.I * (c : ℂ) * (t : ℂ) * f t)) x := by
  have hg := intervalIntegrable_mul_kernelFactor (c := c) hint
  have h := hasDerivAt_prolateTransform (c := c)
    (f := fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * f t) hg x
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact (prolateTransform_factor f y).symm

theorem intervalIntegrable_kernel_mul {c y : ℝ} {f : ℝ → ℂ}
    (hint : IntervalIntegrable f volume (-1) 1) :
    IntervalIntegrable (fun t : ℝ => prolateKernel c y t * f t) volume (-1) 1 :=
  hint.continuousOn_mul (continuous_prolateKernel_snd c y).continuousOn

set_option maxHeartbeats 1000000 in
/-- **The prolate flux of the transform.**  Differentiating `(1 - x^2)` times the transform's
derivative pushes the whole prolate operator inside the integral, where it becomes the symbol. -/
theorem hasDerivAt_prolateTransformFlux {c : ℝ} {f : ℝ → ℂ}
    (hint : IntervalIntegrable f volume (-1) 1) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ((1 - y ^ 2 : ℝ) : ℂ) *
        ∫ t in (-1 : ℝ)..1, Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t * f t)
      (∫ t in (-1 : ℝ)..1,
        (prolateSymbol c x t + (c : ℂ) ^ 2 * (x : ℂ) ^ 2) * prolateKernel c x t * f t) x := by
  have hw : HasDerivAt (fun y : ℝ => ((1 - y ^ 2 : ℝ) : ℂ)) (((-2 * x : ℝ) : ℂ)) x := by
    have h : HasDerivAt (fun y : ℝ => (1 - y ^ 2 : ℝ)) (-2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    exact h.ofReal_comp
  have hG := hasDerivAt_prolateTransform_deriv (c := c) hint x
  have hprod := hw.mul hG
  refine hprod.congr_deriv ?_
  have hint1 : IntervalIntegrable
      (fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t * f t) volume (-1) 1 := by
    have h := intervalIntegrable_kernel_mul (c := c) (y := x)
      (intervalIntegrable_mul_kernelFactor (c := c) hint)
    have hfun : (fun t : ℝ => prolateKernel c x t * (Complex.I * (c : ℂ) * (t : ℂ) * f t))
        = fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t * f t := by
      funext t
      ring
    rwa [hfun] at h
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t *
        (Complex.I * (c : ℂ) * (t : ℂ) * f t)) volume (-1) 1 := by
    have h := intervalIntegrable_kernel_mul (c := c) (y := x)
      (intervalIntegrable_mul_kernelFactor (c := c)
        (intervalIntegrable_mul_kernelFactor (c := c) hint))
    have hfun : (fun t : ℝ => prolateKernel c x t *
          (Complex.I * (c : ℂ) * (t : ℂ) * (Complex.I * (c : ℂ) * (t : ℂ) * f t)))
        = fun t : ℝ => Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c x t *
          (Complex.I * (c : ℂ) * (t : ℂ) * f t) := by
      funext t
      ring
    rwa [hfun] at h
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [prolateSymbol]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  push_cast
  ring_nf
  rw [hI]
  ring

set_option maxHeartbeats 1000000 in
/-- **The prolate operator commutes with the finite Fourier transform.**  Moving the operator inside
the integral turns it into the symbol; the symbol is symmetric, so it may be read as acting in the
integration variable; and Sturm symmetry with the vanishing weight `1 - t^2` transfers it onto the
function. -/
theorem prolateSymbol_integral_eq {c : ℝ} {f f' wf' : ℝ → ℂ} (x : ℝ)
    (hf : ∀ t ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt f (f' t) t)
    (hwf : ∀ t ∈ Set.uIcc (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) * f' s) (wf' t) t)
    (hf'int : IntervalIntegrable f' volume (-1) 1)
    (hwf'int : IntervalIntegrable wf' volume (-1) 1)
    (hKint : IntervalIntegrable (fun t : ℝ => Complex.I * (c : ℂ) * (x : ℂ) * prolateKernel c x t)
      volume (-1) 1)
    (hKfluxint : IntervalIntegrable
      (fun t : ℝ => (prolateSymbol c x t + (c : ℂ) ^ 2 * (t : ℂ) ^ 2) * prolateKernel c x t)
      volume (-1) 1) :
    ∫ t in (-1 : ℝ)..1,
        f t * ((prolateSymbol c x t + (c : ℂ) ^ 2 * (t : ℂ) ^ 2) * prolateKernel c x t)
      = ∫ t in (-1 : ℝ)..1, wf' t * prolateKernel c x t := by
  have hwvanish : ((1 - (1 : ℝ) ^ 2 : ℝ) : ℂ) = 0 := by norm_num
  have hwvanish' : ((1 - (-1 : ℝ) ^ 2 : ℝ) : ℂ) = 0 := by norm_num
  refine integral_mul_sturm_symm (w := fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ))
    (u := f) (v := fun t : ℝ => prolateKernel c x t)
    (u' := f') (v' := fun t : ℝ => Complex.I * (c : ℂ) * (x : ℂ) * prolateKernel c x t)
    (wu' := wf')
    (wv' := fun t : ℝ => (prolateSymbol c x t + (c : ℂ) ^ 2 * (t : ℂ) ^ 2) * prolateKernel c x t)
    ?_ ?_ ?_ ?_ hf ?_ hwf ?_ hf'int hKint hwf'int hKfluxint
  · rw [hwvanish']; ring
  · rw [hwvanish]; ring
  · rw [hwvanish']; ring
  · rw [hwvanish]; ring
  · intro t _
    exact hasDerivAt_prolateKernel c x t
  · intro t _
    exact hasDerivAt_prolateFlux c x t

end HTGeometry
