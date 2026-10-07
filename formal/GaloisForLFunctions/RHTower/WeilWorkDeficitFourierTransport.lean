import GaloisForLFunctions.RHTower.WeilWorkDeficitLeakageIntegral
import GaloisForLFunctions.HTGeometry.CauchyKernelFourier

/-!
# Fourier transport across a finite spectral window

The canonical Poisson representation transports a truncated Fourier integral to the sharp
spectral window. Its error is bounded by the total endpoint leakage, uniformly in frequency.
All product integrability is proved for the actual canonical measure.
-/

open Complex Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace RHTower.WeilSpectral

private def transportCharacter (k t : ℝ) : ℂ := Complex.exp (((k * t : ℝ) : ℂ) * I)

private def transportPoisson (r t : ℝ) : ℝ :=
  (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (t - r) ^ 2)

private theorem norm_transportCharacter (k t : ℝ) : ‖transportCharacter k t‖ = 1 := by
  simp [transportCharacter, Complex.norm_exp]

private theorem continuous_transportCharacter (k : ℝ) : Continuous (transportCharacter k) := by
  unfold transportCharacter
  fun_prop

private theorem transportPoisson_nonneg (r t : ℝ) : 0 ≤ transportPoisson r t := by
  unfold transportPoisson
  positivity

private theorem continuous_transportPoisson (r : ℝ) : Continuous (transportPoisson r) := by
  exact continuous_const.div (by fun_prop) (fun t => by positivity)

private theorem integrable_transportPoisson (r : ℝ) : Integrable (transportPoisson r) := by
  change Integrable (fun t : ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (t - r) ^ 2))
  simpa only [div_eq_mul_inv] using
    ((GaloisForLFunctions.HTGeometry.integrable_inv_sq_add_sq
      (show 0 < (3 / 2 : ℝ) by norm_num)).comp_sub_right r).const_mul (3 / 2 : ℝ)

private theorem integral_transportPoisson (r : ℝ) :
    ∫ t, transportPoisson r t = Real.pi := by
  have heq : transportPoisson r =
      fun t : ℝ => (3 / 2 : ℝ) * ((3 / 2) ^ 2 + (t - r) ^ 2)⁻¹ := by
    funext t
    exact div_eq_mul_inv _ _
  rw [heq, integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => ((3 / 2 : ℝ) ^ 2 + x ^ 2)⁻¹) r,
    GaloisForLFunctions.HTGeometry.integral_inv_sq_add_sq (by norm_num)]
  ring

private theorem integral_transportPoisson_window {T : ℝ} (hT : 0 ≤ T) (r : ℝ) :
    ∫ t in Ioc 0 T, transportPoisson r t = countKernel T r := by
  rw [← intervalIntegral.integral_of_le hT]
  convert integral_poissonKernel_eq T r using 1
  congr 1
  funext t
  unfold transportPoisson
  congr 2
  ring

private theorem norm_transportProduct (k r t : ℝ) :
    ‖transportCharacter k t * (transportPoisson r t : ℂ)‖ = transportPoisson r t := by
  rw [norm_mul, norm_transportCharacter, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (transportPoisson_nonneg r t)]

private theorem integrable_transportProduct (k r : ℝ) :
    Integrable (fun t => transportCharacter k t * (transportPoisson r t : ℂ)) := by
  refine (integrable_transportPoisson r).mono'
    (((continuous_transportCharacter k).mul
      (Complex.continuous_ofReal.comp (continuous_transportPoisson r))).aestronglyMeasurable)
    (Eventually.of_forall fun t => (norm_transportProduct k r t).le)

private theorem integral_transportProduct (k r : ℝ) :
    (∫ t, transportCharacter k t * (transportPoisson r t : ℂ)) =
      ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ) * transportCharacter k r := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun t => transportCharacter k t * (transportPoisson r t : ℂ)) r]
  have hpt (x : ℝ) :
      transportCharacter k (x + r) * (transportPoisson r (x + r) : ℂ) =
      ((3 / 2 : ℝ) : ℂ) * transportCharacter k r *
        (Complex.exp (((x * k : ℝ) : ℂ) * I) * (((3 / 2 : ℝ) ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹) := by
    have he : transportCharacter k (x + r) =
        transportCharacter k r * Complex.exp (((x * k : ℝ) : ℂ) * I) := by
      unfold transportCharacter
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hp : (transportPoisson r (x + r) : ℂ) =
        ((3 / 2 : ℝ) : ℂ) * (((3 / 2 : ℝ) ^ 2 + x ^ 2 : ℝ) : ℂ)⁻¹ := by
      simp [transportPoisson, div_eq_mul_inv]
    rw [he, hp]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_cexp_mul_inv_sq_add_sq (by norm_num)]
  push_cast
  ring

private theorem integrable_boundary_window_const {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (T c : ℝ) :
    Integrable ((Ioc 0 T).indicator (fun _ => c)) (boundaryMeasure hW) := by
  exact (integrableOn_const (measure_ne_top_of_subset Ioc_subset_Icc_self
    (boundaryMeasure_Icc_ne_top hW 0 T))).integrable_indicator measurableSet_Ioc

/-- Integrability of the counting kernel follows from leakage and the finite sharp window. -/
theorem integrable_deficit_countKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) : Integrable (countKernel T) (boundaryMeasure hW) := by
  refine ((integrable_deficitPoissonLeakage hW hT).add
    (integrable_boundary_window_const hW T Real.pi)).mono'
    (continuous_countKernel T).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (countKernel_nonneg (by linarith) r)]
  change countKernel T r ≤ deficitPoissonLeakage T r + (Ioc 0 T).indicator (fun _ => Real.pi) r
  unfold deficitPoissonLeakage
  linarith [le_abs_self (countKernel T r - (Ioc 0 T).indicator (fun _ => Real.pi) r)]

private theorem norm_transportProduct_window_error {T : ℝ} (hT : 0 ≤ T) (k r : ℝ) :
    ‖(∫ t in Ioc 0 T, transportCharacter k t * (transportPoisson r t : ℂ)) -
        (Ioc 0 T).indicator
          (fun r => ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ) * transportCharacter k r) r‖ ≤
      deficitPoissonLeakage T r := by
  by_cases hr : r ∈ Ioc 0 T
  · rw [indicator_of_mem hr, ← integral_transportProduct k r,
      ← integral_add_compl measurableSet_Ioc (integrable_transportProduct k r),
      sub_add_cancel_left, norm_neg]
    calc
      ‖∫ t in (Ioc 0 T)ᶜ, transportCharacter k t * (transportPoisson r t : ℂ)‖ ≤
          ∫ t in (Ioc 0 T)ᶜ, ‖transportCharacter k t * (transportPoisson r t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = Real.pi - countKernel T r := by
        simp_rw [norm_transportProduct]
        rw [setIntegral_compl measurableSet_Ioc (integrable_transportPoisson r),
          integral_transportPoisson, integral_transportPoisson_window hT]
      _ ≤ deficitPoissonLeakage T r := by
        rw [deficitPoissonLeakage, indicator_of_mem hr]
        linarith [neg_le_abs (countKernel T r - Real.pi)]
  · rw [indicator_of_notMem hr, sub_zero]
    calc
      ‖∫ t in Ioc 0 T, transportCharacter k t * (transportPoisson r t : ℂ)‖ ≤
          ∫ t in Ioc 0 T, ‖transportCharacter k t * (transportPoisson r t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = countKernel T r := by
        simp_rw [norm_transportProduct]
        exact integral_transportPoisson_window hT r
      _ ≤ deficitPoissonLeakage T r := by
        rw [deficitPoissonLeakage, indicator_of_notMem hr, sub_zero]
        exact le_abs_self _

private theorem integral_transportPoisson_boundary {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (t : ℝ) :
    (∫ r, transportPoisson r t ∂boundaryMeasure hW) =
      (weilContinuation hW ((2 : ℂ) + t * I)).re := by
  have h := mul_re_weilContinuation_eq hW (a := t) (b := 3 / 2) (by norm_num)
  have hkernel : (fun r : ℝ => (3 / 2 : ℝ) ^ 2 / ((3 / 2) ^ 2 + (r - t) ^ 2)) =
      fun r => (3 / 2 : ℝ) * transportPoisson r t := by
    funext r
    unfold transportPoisson
    rw [show (r - t) ^ 2 = (t - r) ^ 2 by ring]
    ring
  rw [hkernel, integral_const_mul] at h
  norm_num at h
  linarith

private theorem integrable_boundary_window_character {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k T : ℝ) :
    Integrable ((Ioc 0 T).indicator (transportCharacter k)) (boundaryMeasure hW) := by
  have hc : IntegrableOn (fun _r : ℝ => (1 : ℝ)) (Ioc 0 T) (boundaryMeasure hW) :=
    integrableOn_const (measure_ne_top_of_subset Ioc_subset_Icc_self
      (boundaryMeasure_Icc_ne_top hW 0 T))
  have hi : IntegrableOn (transportCharacter k) (Ioc 0 T) (boundaryMeasure hW) :=
    hc.mono' (continuous_transportCharacter k).aestronglyMeasurable
      (Eventually.of_forall fun r => (norm_transportCharacter k r).le)
  exact hi.integrable_indicator measurableSet_Ioc

private theorem integrable_transportProduct_prod {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (k : ℝ) :
    Integrable (fun p : ℝ × ℝ => transportCharacter k p.2 * (transportPoisson p.1 p.2 : ℂ))
      ((boundaryMeasure hW).prod (volume.restrict (Ioc 0 T))) := by
  have hp : Continuous (fun p : ℝ × ℝ => transportPoisson p.1 p.2) :=
    continuous_const.div (by fun_prop) (fun p => by positivity)
  have hc : Continuous (fun p : ℝ × ℝ =>
      transportCharacter k p.2 * (transportPoisson p.1 p.2 : ℂ)) :=
    ((continuous_transportCharacter k).comp continuous_snd).mul
      (Complex.continuous_ofReal.comp hp)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun r => (integrable_transportProduct k r).integrableOn, ?_⟩
  refine (integrable_deficit_countKernel hW hT).congr (Eventually.of_forall fun r => ?_)
  simp_rw [norm_transportProduct]
  exact (integral_transportPoisson_window (by linarith) r).symm

/-- Forward Poisson Fourier transport error for the actual canonical boundary measure. -/
def deficitFourierError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (k T : ℝ) : ℂ :=
  (∫ t in Ioc 0 T, Complex.exp (((k * t : ℝ) : ℂ) * I) *
      ((weilContinuation hW ((2 : ℂ) + t * I)).re : ℂ)) -
    ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ) *
      ∫ r in Ioc 0 T, Complex.exp (((k * r : ℝ) : ℂ) * I) ∂boundaryMeasure hW

/-- The transport error is bounded by the full canonical endpoint leakage, uniformly in frequency. -/
theorem norm_deficitFourierError_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (k : ℝ) :
    ‖deficitFourierError hW k T‖ ≤ ∫ r, deficitPoissonLeakage T r ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  let c : ℂ := ((Real.pi * Real.exp (-((3 / 2) * |k|)) : ℝ) : ℂ)
  have hp := integrable_transportProduct_prod hW hT k
  have hiA : Integrable (fun r =>
      ∫ t in Ioc 0 T, transportCharacter k t * (transportPoisson r t : ℂ))
      (boundaryMeasure hW) := hp.integral_prod_left
  have hiB : Integrable ((Ioc 0 T).indicator (fun r => c * transportCharacter k r))
      (boundaryMeasure hW) := by
    refine ((integrable_boundary_window_character hW k T).const_mul c).congr
      (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc 0 T <;> simp [hr]
  have heqA : (∫ r, (∫ t in Ioc 0 T, transportCharacter k t * (transportPoisson r t : ℂ))
      ∂boundaryMeasure hW) =
      ∫ t in Ioc 0 T, transportCharacter k t *
        ((weilContinuation hW ((2 : ℂ) + t * I)).re : ℂ) := by
    rw [integral_integral_swap hp]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [integral_const_mul, integral_complex_ofReal, integral_transportPoisson_boundary]
  have heqB : (∫ r, (Ioc 0 T).indicator (fun r => c * transportCharacter k r) r
      ∂boundaryMeasure hW) = c * ∫ r in Ioc 0 T, transportCharacter k r ∂boundaryMeasure hW := by
    rw [integral_indicator measurableSet_Ioc, integral_const_mul]
  have hnorm := norm_integral_le_integral_norm (μ := boundaryMeasure hW)
    (fun r => (∫ t in Ioc 0 T, transportCharacter k t * (transportPoisson r t : ℂ)) -
      (Ioc 0 T).indicator (fun r => c * transportCharacter k r) r)
  have hbound := integral_mono (hiA.sub hiB).norm (integrable_deficitPoissonLeakage hW hT)
    (norm_transportProduct_window_error (by linarith : 0 ≤ T) k)
  rw [integral_sub hiA hiB, heqA, heqB] at hnorm
  exact hnorm.trans hbound

/-- Frequency may vary with height: the forward transport error remains `o(T)`. -/
theorem tendsto_norm_deficitFourierError_div {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℝ → ℝ) :
    Tendsto (fun T : ℝ => ‖deficitFourierError hW (k T) T‖ / T) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_integral_deficitPoissonLeakage_div hW)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg (norm_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_le_div_of_nonneg_right (norm_deficitFourierError_le hW hT (k T)) (by linarith)

theorem tendsto_deficitFourierError_div {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℝ → ℝ) :
    Tendsto (fun T : ℝ => deficitFourierError hW (k T) T / (T : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_norm_deficitFourierError_div hW k).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < T)]

end RHTower.WeilSpectral

end
