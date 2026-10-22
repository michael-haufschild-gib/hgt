import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPeriodization
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Fourier–Laplace transform of the source is entire

A member of the exponentially decreasing source beats `e^{-A|t|}` for *every* `A`, so the kernel
`e^{-izt}`, whose modulus is `e^{(Im z)t}`, is absorbed at every complex frequency.  Differentiating
under the integral costs one factor of `t`, which the same margin absorbs.

Hence `ĥ(z) = ∫ h(t) e^{-izt} dt` is defined and complex-differentiable at every `z`: the source
transform is entire.  This is the input the identity theorem needs when the zeros of `ĥ` accumulate.

* `deningerExpAbs_integrable` : `e^{-c|t|}` is integrable for `c > 0`.
* `deningerFourierLaplace` : the transform `ĥ`.
* `deningerFourierLaplace_differentiable` : **`ĥ` is entire.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- The two-sided exponential is integrable. -/
theorem deningerExpAbs_integrable {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Real.exp (-(c * |t|)) := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).measurableEmbedding
  have hpos : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    rw [abs_of_pos ht0]
    congr 1
    ring
  have hrefl : IntegrableOn (fun t : ℝ => Real.exp (-(c * |(-t)|))) (Set.Iio 0) := by
    have hiff := hmp.integrableOn_comp_preimage hme
      (f := fun t : ℝ => Real.exp (-(c * |t|))) (s := Set.Ioi (0 : ℝ))
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
      ext x
      simp [Set.mem_Iio]
    rw [hpre] at hiff
    exact hiff.mpr hpos
  have hneg : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|))) (Set.Iio 0) := by
    refine hrefl.congr_fun (fun t _ => ?_) measurableSet_Iio
    show Real.exp (-(c * |(-t)|)) = Real.exp (-(c * |t|))
    rw [abs_neg]
  have hunion : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|)))
      (Set.Iio (0 : ℝ) ∪ Set.Ioi 0) := integrableOn_union.mpr ⟨hneg, hpos⟩
  rw [Set.Iio_union_Ioi] at hunion
  have hae : (Set.univ : Set ℝ) =ᵐ[volume] ({(0 : ℝ)}ᶜ : Set ℝ) :=
    (ae_eq_univ.mpr (by simp)).symm
  have huniv : IntegrableOn (fun t : ℝ => Real.exp (-(c * |t|))) Set.univ :=
    hunion.congr_set_ae hae
  rwa [integrableOn_univ] at huniv

/-- The Fourier–Laplace kernel `e^{-izt}`. -/
def deningerLaplaceKernel (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(Complex.I * z * (t : ℂ)))

theorem deningerLaplaceKernel_norm (z : ℂ) (t : ℝ) :
    ‖deningerLaplaceKernel z t‖ = Real.exp (z.im * t) := by
  rw [deningerLaplaceKernel, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem deningerLaplaceKernel_norm_le (z : ℂ) (t : ℝ) :
    ‖deningerLaplaceKernel z t‖ ≤ Real.exp (|z.im| * |t|) := by
  rw [deningerLaplaceKernel_norm]
  refine Real.exp_le_exp.mpr ?_
  calc z.im * t ≤ |z.im * t| := le_abs_self _
    _ = |z.im| * |t| := abs_mul _ _

theorem deningerLaplaceKernel_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => deningerLaplaceKernel w t)
      (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z t) z := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.I * w * (t : ℂ)) (Complex.I * (t : ℂ)) z := by
    simpa using ((hasDerivAt_id z).const_mul Complex.I).mul_const (t : ℂ)
  have hlin : HasDerivAt (fun w : ℂ => -(Complex.I * w * (t : ℂ)))
      (-(Complex.I * (t : ℂ))) z := h1.neg
  have hcomp := (Complex.hasDerivAt_exp (-(Complex.I * z * (t : ℂ)))).comp z hlin
  rw [mul_comm] at hcomp
  exact hcomp

/-- **The Fourier–Laplace transform of the source.** -/
def deningerFourierLaplace (h : 𝓢(ℝ, ℂ)) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (h : ℝ → ℂ) t * deningerLaplaceKernel z t

/-- The integrand is integrable at every complex frequency, with a margin. -/
theorem deningerFourierLaplace_integrable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (z : ℂ) (k : ℕ) :
    Integrable fun t : ℝ => ((t : ℂ)) ^ k * ((h : ℝ → ℂ) t * deningerLaplaceKernel z t) := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_norm_le hh (|z.im| + (k : ℝ) + 2)
  have hker : Continuous (deningerLaplaceKernel z) := by
    refine Complex.continuous_exp.comp ?_
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((t : ℂ)) ^ k * ((h : ℝ → ℂ) t * deningerLaplaceKernel z t)) volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact ((Complex.continuous_ofReal.pow k).mul (h.continuous.mul hker))
  refine Integrable.mono' ((deningerExpAbs_integrable (c := 1)
    (by norm_num)).const_mul (C * (Nat.factorial k : ℝ))) hmeas ?_
  filter_upwards with t
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hk : ‖((t : ℂ)) ^ k‖ = |t| ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hpow : |t| ^ k ≤ (Nat.factorial k : ℝ) * Real.exp |t| := by
    have hb := deningerPow_le_factorial_mul_exp k t
    rwa [Real.norm_eq_abs] at hb
  rw [norm_mul, norm_mul, hk]
  have hbound : ‖(h : ℝ → ℂ) t‖ * ‖deningerLaplaceKernel z t‖
      ≤ C * Real.exp (-(((k : ℝ) + 2) * |t|)) := by
    refine le_trans (mul_le_mul (hC t) (deningerLaplaceKernel_norm_le z t)
      (norm_nonneg _) (by positivity)) (le_of_eq ?_)
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hfinal : |t| ^ k * (‖(h : ℝ → ℂ) t‖ * ‖deningerLaplaceKernel z t‖)
      ≤ ((Nat.factorial k : ℝ) * Real.exp |t|) * (C * Real.exp (-(((k : ℝ) + 2) * |t|))) :=
    mul_le_mul hpow hbound (by positivity) (by positivity)
  refine le_trans hfinal ?_
  rw [show ((Nat.factorial k : ℝ) * Real.exp |t|) * (C * Real.exp (-(((k : ℝ) + 2) * |t|)))
      = (C * (Nat.factorial k : ℝ)) * (Real.exp |t| * Real.exp (-(((k : ℝ) + 2) * |t|))) by ring,
    ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- A bound for the differentiated integrand, uniform on a unit ball of frequencies. -/
theorem deningerFourierLaplace_deriv_bound {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (z₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ t : ℝ,
      ‖(h : ℝ → ℂ) t * (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z t)‖
        ≤ C * Real.exp (-(1 * |t|)) := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_norm_le hh (|z₀.im| + 3)
  refine ⟨C, hCnn, fun z hz t => ?_⟩
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have him : |z.im| ≤ |z₀.im| + 1 := by
    have hlt : ‖z - z₀‖ < 1 := by
      rw [← Complex.dist_eq]
      exact Metric.mem_ball.mp hz
    have hle : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa using Complex.abs_im_le_norm (z - z₀)
    have := abs_sub_abs_le_abs_sub z.im z₀.im
    linarith
  have hker : ‖deningerLaplaceKernel z t‖ ≤ Real.exp ((|z₀.im| + 1) * |t|) := by
    refine le_trans (deningerLaplaceKernel_norm_le z t) (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_right him habs
  have hnorm : ‖(h : ℝ → ℂ) t * (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z t)‖
      = ‖(h : ℝ → ℂ) t‖ * (|t| * ‖deningerLaplaceKernel z t‖) := by
    rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hnorm]
  have ht : |t| ≤ Real.exp |t| := by
    have hb := deningerPow_le_factorial_mul_exp 1 t
    rw [Real.norm_eq_abs, pow_one] at hb
    simpa using hb
  have hstep : ‖(h : ℝ → ℂ) t‖ * (|t| * ‖deningerLaplaceKernel z t‖)
      ≤ (C * Real.exp (-((|z₀.im| + 3) * |t|))) *
        (Real.exp |t| * Real.exp ((|z₀.im| + 1) * |t|)) := by
    refine mul_le_mul (hC t) (mul_le_mul ht hker (norm_nonneg _) (by positivity))
      (by positivity) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  have hexp : Real.exp (-((|z₀.im| + 3) * |t|)) *
      (Real.exp |t| * Real.exp ((|z₀.im| + 1) * |t|)) = Real.exp (-(1 * |t|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [mul_assoc, hexp]

/-- **Differentiation under the Fourier–Laplace integral.** -/
theorem deningerFourierLaplace_hasDerivAt {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (z₀ : ℂ) :
    HasDerivAt (deningerFourierLaplace h)
      (∫ t : ℝ, (h : ℝ → ℂ) t * (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z₀ t)) z₀ := by
  obtain ⟨C, hCnn, hbound⟩ := deningerFourierLaplace_deriv_bound hh z₀
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ => (h : ℝ → ℂ) t * deningerLaplaceKernel z t := by
    intro z
    refine h.continuous.mul (Complex.continuous_exp.comp ?_)
    fun_prop
  have hcont' : ∀ z : ℂ, Continuous
      fun t : ℝ => (h : ℝ → ℂ) t * (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z t) := by
    intro z
    refine h.continuous.mul (Continuous.mul (by fun_prop) ?_)
    exact Complex.continuous_exp.comp (by fun_prop)
  have hint : Integrable fun t : ℝ => (h : ℝ → ℂ) t * deningerLaplaceKernel z₀ t := by
    have hb := deningerFourierLaplace_integrable hh z₀ 0
    refine hb.congr (Filter.Eventually.of_forall fun t => ?_)
    simp
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => (h : ℝ → ℂ) t * deningerLaplaceKernel z t)
    (F' := fun z t => (h : ℝ → ℂ) t * (-(Complex.I * (t : ℂ)) * deningerLaplaceKernel z t))
    (bound := fun t : ℝ => C * Real.exp (-(1 * |t|)))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    hint (hcont' z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => fun z hz => hbound z hz t)
    ((deningerExpAbs_integrable (c := 1) one_pos).const_mul C)
    (Filter.Eventually.of_forall fun t => fun z _ =>
      (deningerLaplaceKernel_hasDerivAt t z).const_mul ((h : ℝ → ℂ) t))
  exact hres.2

/-- **The Fourier–Laplace transform of a source element is entire.** -/
theorem deningerFourierLaplace_differentiable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    Differentiable ℂ (deningerFourierLaplace h) := fun z =>
  (deningerFourierLaplace_hasDerivAt hh z).differentiableAt

end

end RHTower
