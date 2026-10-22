import GaloisForLFunctions.RHTower.DilationAutocorrelationPeriodization
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanFourierMellinScattering
import Mathlib.Analysis.MellinInversion
import GaloisForLFunctions.HTGeometry.MellinTestFunctionPerron


/-!
# The cosine–dilation kernel as an inverse Mellin transform

Let `f` be smooth and supported in `[α, β]`, `0 < α ≤ β`, and let `Cf(w) = 2∫_0^∞ f(z) cos(2πzw) dz`
and `Ψ_f = Cf ⋆ f`, `Ψ_f(x) = ∫_0^∞ f(y) Cf(x/y) dy/y` (`cosDilationKernel`).

* **Fourier form** (`fourier_halfLineEvenExt`): `Cf` is the Fourier transform of the even extension
  `t ↦ f(t) + f(−t)`, a Schwartz function (`halfLineEvenExtSchwartz`).
* **Local functional equation** (`Gammaℝ_mul_mellin_halfLineCosTransform`): on the critical line,
  `Γ_ℝ(½+iτ) 𝓜[Cf](½−iτ) = Γ_ℝ(½−iτ) 𝓜f(½+iτ)`, the archimedean functional equation
  `soninMellinEvaluation_fourier` applied to the even extension.
* **Mellin factorization** (`mellin_cosDilationKernel`): `𝓜Ψ_f(s) = 𝓜f(s) 𝓜[Cf](s)` for
  `Re s = ½`, by Fubini; the Mellin integrand is absolutely integrable on `(0, ∞)²`
  (`integrable_cosDilationMellinIntegrand`), with the dilation `x = yw` in the inner integral.
* **Inversion** (`mellinInv_gammaRatio_mellin_eq_cosDilationKernel`): for every `x > 0`,
  `Ψ_f(x) = 𝓜⁻¹_{1/2}[(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)](x)`, by Mellin inversion
  (`mellinInv_mellin_eq`); vertical integrability uses the quadratic decay of `𝓜f` on the line.

On the critical line the multiplier is `e^{2iθ(t)} |𝓜f(½+it)|²`, so `Ψ_f` is the kernel of the
chirped moments `∫ |𝓜f(½+it)|² e^{2iθ(t)} x^{−½−it} dt`.
-/

open MeasureTheory Set Real
open scoped FourierTransform SchwartzMap ContDiff

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-- The critical-line point `½ + iτ`. -/
def cosKernelLinePt (τ : ℝ) : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I

theorem cosKernelLinePt_re (τ : ℝ) : (cosKernelLinePt τ).re = 1 / 2 := by simp [cosKernelLinePt]

/-- The even extension `t ↦ f(t) + f(−t)`; for `f` supported in `(0, ∞)` it equals `f(|t|)`. -/
def halfLineEvenExt (f : ℝ → ℝ) (t : ℝ) : ℂ := ((f t + f (-t) : ℝ) : ℂ)

theorem halfLineEvenExt_neg (f : ℝ → ℝ) (t : ℝ) : halfLineEvenExt f (-t) = halfLineEvenExt f t := by
  simp [halfLineEvenExt, add_comm]

theorem hasCompactSupport_of_support_Icc {α β : ℝ} (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun y hy => by
    by_contra h; exact hy (hsupp y h)

theorem hasCompactSupport_halfLineEvenExt {α β : ℝ} (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    HasCompactSupport (halfLineEvenExt f) := by
  have h1 := hasCompactSupport_of_support_Icc hsupp
  have h2 : HasCompactSupport (fun t => f (-t)) := h1.comp_homeomorph (Homeomorph.neg ℝ)
  have h3 : HasCompactSupport (fun t => f t + f (-t)) := h1.add h2
  exact h3.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero

theorem contDiff_halfLineEvenExt (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (halfLineEvenExt f) := by
  unfold halfLineEvenExt
  exact Complex.ofRealCLM.contDiff.comp (hf.add (hf.comp contDiff_neg))

/-- On the positive half-line the even extension is `f`. -/
theorem halfLineEvenExt_of_pos {α β : ℝ} (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    {t : ℝ} (ht : 0 < t) : halfLineEvenExt f t = (f t : ℂ) := by
  have : f (-t) = 0 := by
    by_contra h
    have := (hsupp (-t) h).1
    linarith
  simp [halfLineEvenExt, this]

/-- **The Fourier transform of the even extension is the cosine transform.** -/
theorem fourier_halfLineEvenExt (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (w : ℝ) :
    𝓕 (halfLineEvenExt f) w = (halfLineCosTransform f w : ℂ) := by
  have hc : Continuous f := hf.continuous
  have hcs := hasCompactSupport_of_support_Icc hsupp
  have hint1 : Integrable fun v : ℝ => (f v * Real.cos (2 * π * (v * w)) : ℝ) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  rw [fourier_real_eq_integral_exp_smul]
  have e : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) • halfLineEvenExt f v =
      Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f v : ℂ) +
        Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f (-v) : ℂ) := by
    intro v; simp only [halfLineEvenExt, smul_eq_mul]; push_cast; ring
  simp_rw [e]
  have hA : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f v : ℂ) :=
    ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) *
      (f v : ℂ))).integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_left
  have hB : Integrable fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f (-v) : ℂ) := by
    have h2 : HasCompactSupport (fun t => f (-t)) := hcs.comp_homeomorph (Homeomorph.neg ℝ)
    exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) *
      (f (-v) : ℂ))).integrable_of_hasCompactSupport
      (h2.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_left
  rw [integral_add hA hB]
  have hrefl : ∫ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f (-v) : ℂ) =
      ∫ v : ℝ, Complex.exp (↑(2 * π * v * w) * Complex.I) * (f v : ℂ) := by
    rw [← integral_neg_eq_self]
    congr 1; funext v; simp only [neg_neg]; push_cast; ring_nf
  rw [hrefl, ← integral_add hA (by
    exact ((by fun_prop : Continuous fun v : ℝ => Complex.exp (↑(2 * π * v * w) * Complex.I) *
      (f v : ℂ))).integrable_of_hasCompactSupport
      (hcs.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_left)]
  have e2 : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) * (f v : ℂ) +
      Complex.exp (↑(2 * π * v * w) * Complex.I) * (f v : ℂ) =
      ((2 * (f v * Real.cos (2 * π * (v * w))) : ℝ) : ℂ) := by
    intro v
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * v * w = -(2 * π * (v * w)) by ring,
      show 2 * π * v * w = 2 * π * (v * w) by ring, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [e2]
  rw [integral_complex_ofReal, integral_const_mul]
  unfold halfLineCosTransform
  congr 2
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
  have : f v = 0 := by
    by_contra h
    exact hv (lt_of_lt_of_le hα (hsupp v h).1)
  simp [this]

/-- The even extension as a Schwartz function. -/
def halfLineEvenExtSchwartz (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_halfLineEvenExt hsupp).toSchwartzMap (contDiff_halfLineEvenExt hf)

@[simp] theorem halfLineEvenExtSchwartz_apply (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (t : ℝ) :
    halfLineEvenExtSchwartz hf hsupp t = halfLineEvenExt f t := rfl

/-- **The archimedean reflection for the cosine transform**, completed form on the critical line. -/
theorem soninMellinEvaluation_halfLineCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (τ : ℝ) :
    soninMellinEvaluation (cosKernelLinePt τ) (fun t => (halfLineCosTransform f t : ℂ)) =
      soninMellinEvaluation (cosKernelLinePt (-τ)) (halfLineEvenExt f) := by
  let F : 𝓢(ℝ, ℂ) := halfLineEvenExtSchwartz hf hsupp
  have hFe : (F : ℝ → ℂ) = halfLineEvenExt f := rfl
  have hfi : Integrable (F : ℝ → ℂ) := F.integrable
  have hFf : Integrable (𝓕 (F : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 F : SchwartzMap ℝ ℂ).integrable
  have heven : ∀ t : ℝ, F (-t) = F t := fun t => halfLineEvenExt_neg f t
  have hint : IntegrableOn (fun t : ℝ => ‖F t‖ * t ^ (-(cosKernelLinePt (-τ)).re)) (Ioi 0) := by
    simpa only [cosKernelLinePt_re] using
      (schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ)) (by norm_num) (by norm_num) F)
  have hFint : IntegrableOn
      (fun t : ℝ => ‖(𝓕 (F : ℝ → ℂ)) t‖ * t ^ (-(1 - cosKernelLinePt (-τ)).re)) (Ioi 0) := by
    rw [show (𝓕 (F : ℝ → ℂ)) = ((𝓕 F : SchwartzMap ℝ ℂ) : ℝ → ℂ) from
      (SchwartzMap.fourier_coe F).symm]
    have hbase := schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (𝓕 F : SchwartzMap ℝ ℂ)
    convert hbase using 1
    norm_num [Complex.sub_re, cosKernelLinePt_re]
  have h := soninMellinEvaluation_fourier (w := cosKernelLinePt (-τ)) (f := (F : ℝ → ℂ))
    (by rw [cosKernelLinePt_re]; norm_num) (by rw [cosKernelLinePt_re]; norm_num) hfi hFf heven hint hFint
  have hline : 1 - cosKernelLinePt (-τ) = cosKernelLinePt τ := by
    unfold cosKernelLinePt; push_cast; ring
  have hfour : 𝓕 (F : ℝ → ℂ) = fun t => (halfLineCosTransform f t : ℂ) := by
    funext w; rw [hFe]; exact fourier_halfLineEvenExt hf hα hsupp w
  rw [hline, hfour, hFe] at h
  exact h.symm

theorem mellinCompletionFactor_eq_Gammaℝ (w : ℂ) : mellinCompletionFactor w = Complex.Gammaℝ w := by
  rw [mellinCompletionFactor, Complex.Gammaℝ_def]

theorem integral_mul_cpow_neg_eq_mellin (g : ℝ → ℂ) (w : ℂ) :
    ∫ t in Ioi (0 : ℝ), g t * (t : ℂ) ^ (-w) = mellin g (1 - w) := by
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm, show 1 - w - 1 = -w by ring]

/-- **The local functional equation of the cosine transform on the critical line**:
`Γ_ℝ(½+iτ) 𝓜[Cf](½−iτ) = Γ_ℝ(½−iτ) 𝓜f(½+iτ)`. -/
theorem Gammaℝ_mul_mellin_halfLineCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (τ : ℝ) :
    Complex.Gammaℝ (cosKernelLinePt τ) * mellin (fun t => (halfLineCosTransform f t : ℂ)) (cosKernelLinePt (-τ)) =
      Complex.Gammaℝ (cosKernelLinePt (-τ)) * mellin (fun t => (f t : ℂ)) (cosKernelLinePt τ) := by
  have h := soninMellinEvaluation_halfLineCosTransform hf hα hsupp τ
  unfold soninMellinEvaluation soninMellinKernel at h
  rw [mellinCompletionFactor_eq_Gammaℝ, mellinCompletionFactor_eq_Gammaℝ,
    integral_mul_cpow_neg_eq_mellin, integral_mul_cpow_neg_eq_mellin] at h
  have h1 : 1 - cosKernelLinePt τ = cosKernelLinePt (-τ) := by unfold cosKernelLinePt; push_cast; ring
  have h2 : 1 - cosKernelLinePt (-τ) = cosKernelLinePt τ := by unfold cosKernelLinePt; push_cast; ring
  rw [h1, h2] at h
  have hm : mellin (halfLineEvenExt f) (cosKernelLinePt τ) = mellin (fun t => (f t : ℂ)) (cosKernelLinePt τ) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [halfLineEvenExt_of_pos hα hsupp ht]
  rw [hm] at h
  exact h

/-! ### Mellin calculus for the cosine–dilation kernel -/

/-- Dilation in the Mellin integrand: `∫_0^∞ x^{s−1} g(x/y) dx = y^s ∫_0^∞ w^{s−1} g(w) dw`. -/
theorem integral_Ioi_cpow_mul_comp_div (g : ℝ → ℂ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * g (x / y) =
      (y : ℂ) ^ s * ∫ w in Ioi (0 : ℝ), (w : ℂ) ^ (s - 1) * g w := by
  have h := integral_comp_mul_left_Ioi (fun x => (x : ℂ) ^ (s - 1) * g (x / y)) 0 hy
  simp only [mul_zero] at h
  have hc : ∫ w in Ioi (0 : ℝ), ((y * w : ℝ) : ℂ) ^ (s - 1) * g (y * w / y) =
      (y : ℂ) ^ (s - 1) * ∫ w in Ioi (0 : ℝ), (w : ℂ) ^ (s - 1) * g w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have hw0 : (0 : ℝ) < w := hw
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le hw0.le,
      mul_div_cancel_left₀ _ hy.ne']
    ring
  rw [hc] at h
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpow : (y : ℂ) ^ s = (y : ℂ) * (y : ℂ) ^ (s - 1) := by
    have e : (y : ℂ) ^ s = (y : ℂ) ^ ((s - 1) + 1) := by ring_nf
    rw [e, Complex.cpow_add _ _ hy0, Complex.cpow_one, mul_comm]
  rw [Complex.real_smul, Complex.ofReal_inv] at h
  rw [hpow, mul_assoc, h, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]

/-- The real version for norms. -/
theorem integral_Ioi_rpow_mul_comp_div (g : ℝ → ℝ) (a : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), x ^ a * g (x / y) = y ^ (a + 1) * ∫ w in Ioi (0 : ℝ), w ^ a * g w := by
  have h := integral_comp_mul_left_Ioi (fun x => x ^ a * g (x / y)) 0 hy
  simp only [mul_zero, smul_eq_mul] at h
  have hc : ∫ w in Ioi (0 : ℝ), (y * w) ^ a * g (y * w / y) =
      y ^ a * ∫ w in Ioi (0 : ℝ), w ^ a * g w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have hw0 : (0 : ℝ) < w := hw
    rw [Real.mul_rpow hy.le hw0.le, mul_div_cancel_left₀ _ hy.ne']
    ring
  rw [hc] at h
  rw [Real.rpow_add hy, Real.rpow_one, mul_comm (y ^ a) y, mul_assoc, h, ← mul_assoc,
    mul_inv_cancel₀ hy.ne', one_mul]

/-- The cosine transform is the Fourier transform of the even Schwartz extension. -/
theorem halfLineCosTransform_eq_fourier (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    (fun w => (halfLineCosTransform f w : ℂ)) =
      ⇑((𝓕 (halfLineEvenExtSchwartz hf hsupp) : 𝓢(ℝ, ℂ))) := by
  funext w
  rw [SchwartzMap.fourier_coe]
  exact (fourier_halfLineEvenExt hf hα hsupp w).symm

theorem continuous_halfLineCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Continuous fun w => (halfLineCosTransform f w : ℂ) := by
  rw [halfLineCosTransform_eq_fourier hf hα hsupp]
  exact (𝓕 (halfLineEvenExtSchwartz hf hsupp) : 𝓢(ℝ, ℂ)).continuous

theorem integrableOn_norm_halfLineCosTransform (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    IntegrableOn (fun w : ℝ => ‖(halfLineCosTransform f w : ℂ)‖ * w ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
  have h := schwartz_integrableOn_norm_mul_rpow_Ioi (sigma := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (𝓕 (halfLineEvenExtSchwartz hf hsupp) : 𝓢(ℝ, ℂ))
  rw [← halfLineCosTransform_eq_fourier hf hα hsupp] at h
  exact h

/-- Integrability of the dilated Mellin integrand `x ↦ x^{s−1} Cf(x/y)` on the half-line. -/
theorem integrableOn_cpow_mul_halfLineCosTransform_div (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : s.re = 1 / 2)
    {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * (halfLineCosTransform f (x / y) : ℂ))
      (Ioi 0) := by
  set H : ℝ → ℂ := fun w => ((y * w : ℝ) : ℂ) ^ (s - 1) * (halfLineCosTransform f w : ℂ)
  have hcos := continuous_halfLineCosTransform hf hα hsupp
  have hH : IntegrableOn H (Ioi 0) := by
    have hbase := (integrableOn_norm_halfLineCosTransform hf hα hsupp).const_mul (y ^ (-(1 / 2 : ℝ)))
    refine Integrable.mono' hbase ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun w hw => ?_) measurableSet_Ioi
      have hw0 : (0 : ℝ) < w := hw
      refine ContinuousAt.continuousWithinAt ?_
      have h1 : ContinuousAt (fun w : ℝ => ((y * w : ℝ) : ℂ) ^ (s - 1)) w :=
        (Complex.continuousAt_ofReal_cpow_const (y * w) (s - 1) (Or.inr (mul_pos hy hw0).ne')).comp
          (continuous_const.mul continuous_id).continuousAt
      exact h1.mul hcos.continuousAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw0 : (0 : ℝ) < w := hw
      simp only [H, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hy hw0), Complex.sub_re, Complex.one_re, hs,
        Real.mul_rpow hy.le hw0.le]
      norm_num
      apply le_of_eq; ring
  have heq : (fun x : ℝ => H (y⁻¹ * x)) =
      fun x : ℝ => (x : ℂ) ^ (s - 1) * (halfLineCosTransform f (x / y) : ℂ) := by
    funext x
    simp only [H]
    rw [show y * (y⁻¹ * x) = x by field_simp, show y⁻¹ * x = x / y by ring]
  rw [← heq, integrableOn_Ioi_comp_mul_left_iff H 0 (inv_pos.mpr hy), mul_zero]
  exact hH

/-- The integral of the norm of the dilated integrand. -/
theorem integral_norm_cpow_mul_halfLineCosTransform_div {s : ℂ} (hs : s.re = 1 / 2) {y : ℝ}
    (hy : 0 < y) :
    ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * (halfLineCosTransform f (x / y) : ℂ)‖ =
      y ^ (1 / 2 : ℝ) *
        ∫ w in Ioi (0 : ℝ), w ^ (-(1 / 2 : ℝ)) * ‖(halfLineCosTransform f w : ℂ)‖ := by
  have h := integral_Ioi_rpow_mul_comp_div (fun w => ‖(halfLineCosTransform f w : ℂ)‖)
    (-(1 / 2 : ℝ)) hy
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  simp only [norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re, hs]
  norm_num

/-- The two-variable Mellin integrand `x^{s−1} f(y) Cf(x/y)/y` of `Cf ⋆ f`. -/
def cosDilationMellinIntegrand (f : ℝ → ℝ) (s : ℂ) (x y : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * ((f y : ℂ) * (halfLineCosTransform f (x / y) : ℂ) / (y : ℂ))

theorem integral_cosDilationMellinIntegrand_left (f : ℝ → ℝ) (s : ℂ) (x : ℝ) :
    ∫ y in Ioi (0 : ℝ), cosDilationMellinIntegrand f s x y =
      (x : ℂ) ^ (s - 1) * (cosDilationKernel f x : ℂ) := by
  unfold cosDilationKernel cosDilationMellinIntegrand
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  push_cast
  ring

/-- **Absolute integrability of the Mellin integrand of `Cf ⋆ f` on the critical line.** -/
theorem integrable_cosDilationMellinIntegrand (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : s.re = 1 / 2) :
    Integrable (Function.uncurry (cosDilationMellinIntegrand f s))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  set cosT : ℝ → ℂ := fun w => (halfLineCosTransform f w : ℂ) with hcosT
  have hcos : Continuous cosT := continuous_halfLineCosTransform hf hα hsupp
  have hfc : Continuous f := hf.continuous
  set K₀ : ℝ := ∫ w in Ioi (0 : ℝ), w ^ (-(1 / 2 : ℝ)) * ‖cosT w‖
  have hmeas : AEStronglyMeasurable (Function.uncurry (cosDilationMellinIntegrand f s))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine ContinuousOn.aestronglyMeasurable (fun p hp => ?_)
      (measurableSet_Ioi.prod measurableSet_Ioi)
    obtain ⟨hp1, hp2⟩ := hp
    have hx0 : (0 : ℝ) < p.1 := hp1
    have hy0 : (0 : ℝ) < p.2 := hp2
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ) ^ (s - 1)) p :=
      (Complex.continuousAt_ofReal_cpow_const p.1 (s - 1) (Or.inr hx0.ne')).comp
        continuousAt_fst
    have h2 : ContinuousAt (fun q : ℝ × ℝ => cosT (q.1 / q.2)) p :=
      hcos.continuousAt.comp (continuousAt_fst.div continuousAt_snd hy0.ne')
    have h3 : ContinuousAt (fun q : ℝ × ℝ => (f q.2 : ℂ)) p :=
      (Complex.continuous_ofReal.comp (hfc.comp continuous_snd)).continuousAt
    have h4 : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
      (Complex.continuous_ofReal.comp continuous_snd).continuousAt
    exact h1.mul ((h3.mul h2).div h4 (by exact_mod_cast hy0.ne'))
  rw [integrable_prod_iff' hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := hy
    have hbase := (integrableOn_cpow_mul_halfLineCosTransform_div hf hα hsupp hs hy0).const_mul
      ((f y : ℂ) / (y : ℂ))
    refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair, cosDilationMellinIntegrand]
    ring
  · have hnorm : ∀ y : ℝ, 0 < y →
        ∫ x in Ioi (0 : ℝ), ‖Function.uncurry (cosDilationMellinIntegrand f s) (x, y)‖ =
          ‖f y‖ * y ^ (-(1 / 2 : ℝ)) * K₀ := by
      intro y hy0
      have e : ∀ x : ℝ, ‖Function.uncurry (cosDilationMellinIntegrand f s) (x, y)‖ =
          (‖f y‖ / y) * ‖(x : ℂ) ^ (s - 1) * (halfLineCosTransform f (x / y) : ℂ)‖ := by
        intro x
        simp only [Function.uncurry_apply_pair, cosDilationMellinIntegrand, norm_mul, norm_div,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
        ring
      simp_rw [e]
      rw [integral_const_mul, integral_norm_cpow_mul_halfLineCosTransform_div hs hy0]
      have hy12 : y ^ (1 / 2 : ℝ) = y * y ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_one_add' hy0.le (by norm_num)]; norm_num
      rw [hy12]
      field_simp
      rfl
    have hK : IntegrableOn (fun y : ℝ => ‖f y‖ * y ^ (-(1 / 2 : ℝ)) * K₀) (Ioi 0) := by
      have hcont : ContinuousOn (fun y : ℝ => ‖f y‖ * y ^ (-(1 / 2 : ℝ)) * K₀) (Icc α β) := by
        refine ((hfc.norm.continuousOn).mul ?_).mul continuousOn_const
        exact continuousOn_id.rpow_const fun y hy => Or.inl (lt_of_lt_of_le hα hy.1).ne'
      refine (hcont.integrableOn_compact' isCompact_Icc measurableSet_Icc).of_forall_sdiff_eq_zero
        measurableSet_Ioi fun y hy => ?_
      have : f y = 0 := by
        by_contra h0; exact hy.2 (hsupp y h0)
      simp [this]
    exact hK.congr_fun (fun y hy => (hnorm y hy).symm) measurableSet_Ioi

/-- **Mellin convergence of `Cf ⋆ f` on the critical line.** -/
theorem mellinConvergent_cosDilationKernel (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : s.re = 1 / 2) :
    MellinConvergent (fun x => (cosDilationKernel f x : ℂ)) s := by
  have h := (integrable_cosDilationMellinIntegrand hf hα hsupp hs).integral_prod_left
  unfold MellinConvergent
  refine (h.congr (Filter.Eventually.of_forall fun x => ?_))
  simp only [smul_eq_mul]
  exact integral_cosDilationMellinIntegrand_left f s x

/-- **Mellin factorization of the cosine–dilation kernel on the critical line**:
`𝓜[Cf ⋆ f](s) = 𝓜f(s) 𝓜[Cf](s)` for `Re s = ½`. -/
theorem mellin_cosDilationKernel (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : s.re = 1 / 2) :
    mellin (fun x => (cosDilationKernel f x : ℂ)) s =
      mellin (fun y => (f y : ℂ)) s * mellin (fun w => (halfLineCosTransform f w : ℂ)) s := by
  set cosT : ℝ → ℂ := fun w => (halfLineCosTransform f w : ℂ) with hcosT
  have hD : mellin (fun x => (cosDilationKernel f x : ℂ)) s =
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), cosDilationMellinIntegrand f s x y := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [integral_cosDilationMellinIntegrand_left, smul_eq_mul]
  rw [hD, integral_integral_swap (integrable_cosDilationMellinIntegrand hf hα hsupp hs)]
  have hinner : ∀ y : ℝ, 0 < y → ∫ x in Ioi (0 : ℝ), cosDilationMellinIntegrand f s x y =
      (y : ℂ) ^ (s - 1) * (f y : ℂ) * mellin cosT s := by
    intro y hy0
    have hy : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have e : ∀ x : ℝ, cosDilationMellinIntegrand f s x y =
        ((f y : ℂ) / (y : ℂ)) * ((x : ℂ) ^ (s - 1) * cosT (x / y)) := by
      intro x; simp only [cosDilationMellinIntegrand, hcosT]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_Ioi_cpow_mul_comp_div cosT s hy0]
    have hpow : (y : ℂ) ^ s = (y : ℂ) * (y : ℂ) ^ (s - 1) := by
      have e2 : (y : ℂ) ^ s = (y : ℂ) ^ ((s - 1) + 1) := by ring_nf
      rw [e2, Complex.cpow_add _ _ hy, Complex.cpow_one, mul_comm]
    unfold mellin
    simp only [smul_eq_mul]
    rw [hpow]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => hinner y hy]
  rw [integral_mul_const]
  unfold mellin
  simp only [smul_eq_mul]

/-- Mellin transforms of continuous functions are continuous along a line of convergence. -/
theorem continuous_mellin_verticalLine_of_continuous {g : ℝ → ℂ} (hgc : Continuous g) {σ : ℝ}
    (hg : MellinConvergent g σ) :
    Continuous fun y : ℝ => mellin g (σ + y * Complex.I) := by
  unfold mellin
  refine continuous_of_dominated (bound := fun t => ‖(t : ℂ) ^ ((σ : ℂ) - 1) • g t‖) ?_ ?_
    hg.norm ?_
  · intro y
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    exact (Complex.continuousAt_ofReal_cpow_const t _ (Or.inr ht0.ne')).smul hgc.continuousAt
  · intro y
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    refine (Continuous.const_cpow (by fun_prop) (Or.inl ?_)).smul continuous_const
    exact_mod_cast ht0.ne'

/-- The cosine–dilation kernel is continuous. -/
theorem continuous_cosDilationKernel (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Continuous fun x => (cosDilationKernel f x : ℂ) := by
  have hfc : Continuous f := hf.continuous
  have hA : Continuous fun r => dilationAutocorr f |r| :=
    (continuous_dilationAutocorr hfc hα hsupp).comp continuous_abs
  have hAs := hasCompactSupport_dilationAutocorr_abs hα hαβ hsupp (f := f)
  have hreal : Continuous fun x => cosDilationKernel f x := by
    have e : (fun x => cosDilationKernel f x) =
        fun x => ∫ r, dilationAutocorr f |r| * Real.cos (2 * π * (x * r)) := by
      funext x; exact cosDilationKernel_eq_integral_abs hfc hα hαβ hsupp x
    rw [e]
    refine continuous_of_dominated (bound := fun r => abs (dilationAutocorr f |r|)) ?_ ?_ ?_ ?_
    · intro x
      exact (hA.mul (by fun_prop)).aestronglyMeasurable
    · intro x
      refine Filter.Eventually.of_forall fun r => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · exact (hA.abs.integrable_of_hasCompactSupport hAs.abs)
    · exact Filter.Eventually.of_forall fun r => by fun_prop
  exact Complex.continuous_ofReal.comp hreal

/-- The smooth test function `f` in the corpus test-function class. -/
theorem isTest_ofReal_of_support (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    GaloisForLFunctions.HTGeometry.TestFunctionPerron.IsTest (fun y => (f y : ℂ)) α β where
  pos := hα
  le := hαβ
  smooth := Complex.ofRealCLM.contDiff.comp hf
  supp := fun y hy => by
    have : f y ≠ 0 := by simpa using hy
    exact hsupp y this

/-- **Vertical integrability of the Mellin transform of `Cf ⋆ f` on the critical line.** -/
theorem verticalIntegrable_mellin_cosDilationKernel (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    Complex.VerticalIntegrable (mellin fun x => (cosDilationKernel f x : ℂ)) (1 / 2) := by
  have htest := isTest_ofReal_of_support hf hα hαβ hsupp
  obtain ⟨C, hC0, hC⟩ := htest.exists_norm_mellin_le_decay 1
  set cosT : ℝ → ℂ := fun w => (halfLineCosTransform f w : ℂ) with hcosT
  set Kc : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ‖cosT t‖ with hKc
  have hline : ∀ y : ℝ, (((1 / 2 : ℝ) : ℂ) + y * Complex.I).re = 1 / 2 := by
    intro y; simp
  have hconv : MellinConvergent (fun x => (cosDilationKernel f x : ℂ)) ((1 / 2 : ℝ) : ℂ) :=
    mellinConvergent_cosDilationKernel hf hα hsupp (by simp)
  have hcont := continuous_mellin_verticalLine_of_continuous (continuous_cosDilationKernel hf hα hαβ hsupp) hconv
  unfold Complex.VerticalIntegrable
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (C * Kc))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * Complex.I
  rw [mellin_cosDilationKernel hf hα hsupp (hline y), norm_mul]
  have h1 : ‖mellin (fun y => (f y : ℂ)) s‖ ≤ C / (1 + y ^ 2) := by
    have := hC s (by rw [hline y]; norm_num [abs_of_neg])
    simpa [s] using this
  have h2 : ‖mellin cosT s‖ ≤ Kc := by
    unfold mellin
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    simp only [norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp [s]
    norm_num
  have hKc0 : 0 ≤ Kc := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _)
  calc ‖mellin (fun y => (f y : ℂ)) s‖ * ‖mellin cosT s‖ ≤ (C / (1 + y ^ 2)) * Kc :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C * Kc * (1 + y ^ 2)⁻¹ := by field_simp

/-- On the critical line the Mellin transform of `Cf ⋆ f` is
`(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)`. -/
theorem mellin_cosDilationKernel_eq_gammaRatio (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (y : ℝ) :
    mellin (fun x => (cosDilationKernel f x : ℂ)) (((1 / 2 : ℝ) : ℂ) + y * Complex.I) =
      Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + y * Complex.I) /
          Complex.Gammaℝ (1 - (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) *
        mellin (fun y => (f y : ℂ)) (((1 / 2 : ℝ) : ℂ) + y * Complex.I) *
        mellin (fun y => (f y : ℂ)) (1 - (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + y * Complex.I with hs_def
  have hs : s.re = 1 / 2 := by simp [s]
  rw [mellin_cosDilationKernel hf hα hsupp hs]
  have hFE := Gammaℝ_mul_mellin_halfLineCosTransform hf hα hsupp (-y)
  have e1 : cosKernelLinePt (-(-y)) = s := by simp [cosKernelLinePt, s]
  have e2 : cosKernelLinePt (-y) = 1 - s := by
    simp only [cosKernelLinePt, s]; push_cast; ring
  rw [e1, e2] at hFE
  have hne : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s]; norm_num)
  have hcos : mellin (fun t => (halfLineCosTransform f t : ℂ)) s =
      Complex.Gammaℝ s * mellin (fun y => (f y : ℂ)) (1 - s) / Complex.Gammaℝ (1 - s) := by
    rw [eq_div_iff hne, ← hFE]; ring
  rw [hcos]
  field_simp

/-- **`Cf ⋆ f` is the inverse Mellin transform of `(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜f(s) 𝓜f(1−s)`** on the
critical line. -/
theorem mellinInv_gammaRatio_mellin_eq_cosDilationKernel (hf : ContDiff ℝ ∞ f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {x : ℝ} (hx : 0 < x) :
    mellinInv (1 / 2) (fun s => Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) *
        mellin (fun y => (f y : ℂ)) s * mellin (fun y => (f y : ℂ)) (1 - s)) x =
      (cosDilationKernel f x : ℂ) := by
  have hconv : MellinConvergent (fun x => (cosDilationKernel f x : ℂ)) ((1 / 2 : ℝ) : ℂ) :=
    mellinConvergent_cosDilationKernel hf hα hsupp (by simp)
  rw [← mellinInv_mellin_eq (1 / 2) (fun x => (cosDilationKernel f x : ℂ)) hx hconv
    (verticalIntegrable_mellin_cosDilationKernel hf hα hαβ hsupp)
    (continuous_cosDilationKernel hf hα hαβ hsupp).continuousAt]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [mellin_cosDilationKernel_eq_gammaRatio hf hα hsupp y]

end

end RHTower
