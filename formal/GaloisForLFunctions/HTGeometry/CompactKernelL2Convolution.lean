import GaloisForLFunctions.HTGeometry.YoungConvolutionL2
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Convolution of a compactly supported kernel against a square-integrable profile

The mollified objects of a weak-domain argument are line convolutions `g ⋆ V` with `g` smooth and
compactly supported and `V` only square-integrable.  This module records their basic regularity:
pointwise well-definedness, continuity, the derivative falling on the kernel, the sup and Lipschitz
bounds by `‖g‖₂‖V‖₂`-type constants, square-integrability, the `L²` translate modulus controlled by
the `L¹` translate modulus of the kernel, and the support shift.

Everything is quantitative and hypothesis-light: `V` carries only measurability and
square-integrability, `g` carries continuity or one derivative and compact support.
-/

open MeasureTheory Set Convolution
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- The line convolution is the bundled `mathlib` convolution for scalar multiplication. -/
theorem lineConvolution_eq_convolution (g V : ℝ → ℝ) :
    lineConvolution g V = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] V := by
  funext x
  simp [lineConvolution, MeasureTheory.convolution_def]

/-- A square-integrable measurable profile is locally integrable. -/
theorem locallyIntegrable_of_sq_integrable {V : ℝ → ℝ}
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2)) :
    LocallyIntegrable V volume :=
  ((memLp_two_iff_integrable_sq hVm).mpr hV2).locallyIntegrable (by norm_num)

/-- The reflected translate of a square-integrable profile is square-integrable, with the same
integral. -/
theorem integral_sq_comp_sub (V : ℝ → ℝ) (x : ℝ) :
    (∫ t, V (x - t) ^ 2) = ∫ t, V t ^ 2 :=
  integral_sub_left_eq_self (fun t => V t ^ 2) volume x

theorem integrable_sq_comp_sub {V : ℝ → ℝ}
    (hV2 : Integrable (fun t => V t ^ 2)) (x : ℝ) :
    Integrable (fun t => V (x - t) ^ 2) := by
  have hmp := (volume : Measure ℝ).measurePreserving_sub_left x
  have hcomp := (hmp.integrable_comp (hV2.aestronglyMeasurable)).mpr hV2
  simpa [Function.comp_def] using hcomp

/-- The square of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_sq {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport fun u => f u ^ 2 := by
  have := hf.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  simpa [Function.comp_def] using this

theorem aestronglyMeasurable_comp_sub {V : ℝ → ℝ}
    (hVm : AEStronglyMeasurable V volume) (x : ℝ) :
    AEStronglyMeasurable (fun t => V (x - t)) volume :=
  hVm.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left x)

/-- The convolution integrand of an `L²` kernel against an `L²` profile is integrable. -/
theorem integrable_kernel_mul_sq {g V : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g volume) (hg2 : Integrable (fun u => g u ^ 2))
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2)) (x : ℝ) :
    Integrable (fun t => g t * V (x - t)) :=
  integrable_mul_of_sq_integrable hgm (aestronglyMeasurable_comp_sub hVm x) hg2
    (integrable_sq_comp_sub hV2 x)

/-- **The pointwise Cauchy–Schwarz bound.** -/
theorem sq_lineConvolution_le_mul {g V : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g volume) (hg2 : Integrable (fun u => g u ^ 2))
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2)) (x : ℝ) :
    lineConvolution g V x ^ 2 ≤ (∫ u, g u ^ 2) * ∫ t, V t ^ 2 := by
  have h := sq_integral_mul_le (μ := volume) hgm (aestronglyMeasurable_comp_sub hVm x) hg2
    (integrable_sq_comp_sub hV2 x)
  rw [integral_sq_comp_sub] at h
  exact h

/-- **The sup bound.** -/
theorem abs_lineConvolution_le {g V : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g volume) (hg2 : Integrable (fun u => g u ^ 2))
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2)) (x : ℝ) :
    |lineConvolution g V x| ≤ Real.sqrt ((∫ u, g u ^ 2) * ∫ t, V t ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_lineConvolution_le_mul hgm hg2 hVm hV2 x)

/-- **Continuity.** -/
theorem continuous_lineConvolution {g V : ℝ → ℝ}
    (hgc : Continuous g) (hgsupp : HasCompactSupport g)
    (hVloc : LocallyIntegrable V volume) :
    Continuous (lineConvolution g V) := by
  rw [lineConvolution_eq_convolution]
  exact hgsupp.continuous_convolution_left _ hgc hVloc

/-- **The derivative falls on the kernel.** -/
theorem hasDerivAt_lineConvolution {g V : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgsupp : HasCompactSupport g)
    (hVloc : LocallyIntegrable V volume) (x : ℝ) :
    HasDerivAt (lineConvolution g V) (lineConvolution (deriv g) V x) x := by
  rw [lineConvolution_eq_convolution, lineConvolution_eq_convolution]
  exact hgsupp.hasDerivAt_convolution_left _ hg hVloc x

/-- **The Lipschitz bound**, with constant `‖g′‖₂‖V‖₂`. -/
theorem abs_lineConvolution_sub_le {g V : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgsupp : HasCompactSupport g)
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2))
    (x y : ℝ) :
    |lineConvolution g V x - lineConvolution g V y|
      ≤ Real.sqrt ((∫ u, deriv g u ^ 2) * ∫ t, V t ^ 2) * |x - y| := by
  set C : ℝ := Real.sqrt ((∫ u, deriv g u ^ 2) * ∫ t, V t ^ 2) with hC
  have hVloc : LocallyIntegrable V volume := locallyIntegrable_of_sq_integrable hVm hV2
  have hg'c : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hg'supp : HasCompactSupport (deriv g) := hgsupp.deriv
  have hg'2 : Integrable (fun u => deriv g u ^ 2) :=
    (hg'c.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hg'supp)
  have hbound : ∀ z ∈ (univ : Set ℝ), ‖lineConvolution (deriv g) V z‖ ≤ C := by
    intro z _
    rw [Real.norm_eq_abs]
    exact abs_lineConvolution_le hg'c.aestronglyMeasurable hg'2 hVm hV2 z
  have hderiv : ∀ z ∈ (univ : Set ℝ),
      HasDerivWithinAt (lineConvolution g V) (lineConvolution (deriv g) V z) univ z :=
    fun z _ => (hasDerivAt_lineConvolution hg hgsupp hVloc z).hasDerivWithinAt
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound convex_univ
    (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- **Square-integrability of the convolution.** -/
theorem integrable_sq_lineConvolution {g V : ℝ → ℝ}
    (hgc : Continuous g) (hgsupp : HasCompactSupport g)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ 2)) :
    Integrable (fun x => lineConvolution g V x ^ 2) := by
  have hgi : Integrable (fun t => |g t|) :=
    (hgc.integrable_of_hasCompactSupport hgsupp).abs
  have hcont : Continuous (lineConvolution g V) :=
    continuous_lineConvolution hgc hgsupp
      (locallyIntegrable_of_sq_integrable hVmm.aestronglyMeasurable hV2)
  have hbound : ∀ x, ‖lineConvolution g V x‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ * ‖V (x - y)‖ₑ := by
    intro x
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    exact lintegral_congr fun t => enorm_mul _ _
  have hmain := lintegral_enorm_sq_le_of_convolution_bound
    hgc.measurable.enorm hVmm.enorm hbound
  have hBfin : (∫⁻ t, ‖g t‖ₑ) ≠ ⊤ := by
    have h := hgi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa using h.ne
  have hDfin : (∫⁻ x, ‖V x‖ₑ ^ 2) ≠ ⊤ := by
    have h := hV2.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa [enorm_pow] using h.ne
  refine ⟨(hcont.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (∫⁻ x, ‖lineConvolution g V x ^ 2‖ₑ) = ∫⁻ x, ‖lineConvolution g V x‖ₑ ^ 2 :=
    lintegral_congr fun x => enorm_pow _ _
  rw [heq]
  exact lt_of_le_of_lt hmain
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top hBfin.lt_top) hDfin.lt_top)

/-- Shifting the base point shifts the kernel. -/
theorem lineConvolution_comp_add (g V : ℝ → ℝ) (h x : ℝ) :
    lineConvolution g V (x + h) = lineConvolution (fun u => g (u + h)) V x := by
  rw [lineConvolution, lineConvolution]
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t => g t * V (x + h - t)) h
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show g (u + h) * V (x + h - (u + h)) = g (u + h) * V (x - u)
  have harg : x + h - (u + h) = x - u := by ring
  rw [harg]

/-- The convolution is additive in the kernel wherever both integrands are integrable. -/
theorem lineConvolution_kernel_sub {g₁ g₂ V : ℝ → ℝ} {x : ℝ}
    (h1 : Integrable (fun t => g₁ t * V (x - t)))
    (h2 : Integrable (fun t => g₂ t * V (x - t))) :
    lineConvolution (fun u => g₁ u - g₂ u) V x
      = lineConvolution g₁ V x - lineConvolution g₂ V x := by
  rw [lineConvolution, lineConvolution, lineConvolution, ← integral_sub h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (g₁ t - g₂ t) * V (x - t) = g₁ t * V (x - t) - g₂ t * V (x - t)
  ring

/-- **The `L²` translate modulus** of the convolution is the `L¹` translate modulus of the
kernel times the energy. -/
theorem integral_sq_lineConvolution_translate_le {g V : ℝ → ℝ}
    (hgc : Continuous g) (hgsupp : HasCompactSupport g)
    (hVmm : Measurable V) (hV2 : Integrable (fun t => V t ^ 2)) (h : ℝ) :
    (∫ x, (lineConvolution g V (x + h) - lineConvolution g V x) ^ 2)
      ≤ (∫ u, |g (u + h) - g u|) ^ 2 * ∫ t, V t ^ 2 := by
  have hc1 : Continuous fun u : ℝ => g (u + h) := hgc.comp (continuous_add_const h)
  have hdc : Continuous fun u : ℝ => g (u + h) - g u := hc1.sub hgc
  have hdsupp : HasCompactSupport fun u : ℝ => g (u + h) - g u := by
    have h1 : HasCompactSupport fun u : ℝ => g (u + h) := by
      have := hgsupp.comp_homeomorph (Homeomorph.addRight h)
      simpa [Function.comp_def] using this
    exact h1.sub hgsupp
  have hVm : AEStronglyMeasurable V volume := hVmm.aestronglyMeasurable
  have hg2 : Integrable (fun u => g u ^ 2) :=
    (hgc.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hgsupp)
  have hg2' : Integrable (fun u => g (u + h) ^ 2) := by
    simpa using hg2.comp_add_right h
  have hpt : ∀ x, lineConvolution g V (x + h) - lineConvolution g V x
      = lineConvolution (fun u => g (u + h) - g u) V x := by
    intro x
    rw [lineConvolution_comp_add g V h x]
    exact (lineConvolution_kernel_sub
      (integrable_kernel_mul_sq hc1.aestronglyMeasurable hg2' hVm hV2 x)
      (integrable_kernel_mul_sq hgc.aestronglyMeasurable hg2 hVm hV2 x)).symm
  have hrw : (fun x => (lineConvolution g V (x + h) - lineConvolution g V x) ^ 2)
      = fun x => lineConvolution (fun u => g (u + h) - g u) V x ^ 2 := by
    funext x
    rw [hpt x]
  rw [hrw]
  exact integral_sq_lineConvolution_le hdc.measurable hVmm
    ((hdc.integrable_of_hasCompactSupport hdsupp).abs)
    hV2 (integrable_sq_lineConvolution hdc hdsupp hVmm hV2)

/-- **The kernel's `L¹` translate modulus** is linear in the shift, for a Lipschitz compactly
supported kernel. -/
theorem integral_abs_kernel_translate_le {g : ℝ → ℝ} {K R : ℝ}
    (hK : ∀ u v : ℝ, |g u - g v| ≤ K * |u - v|)
    (hsupp : ∀ u : ℝ, R < |u| → g u = 0) (hR : 0 ≤ R) {h : ℝ} (hh : 0 ≤ h) :
    (∫ u, |g (u + h) - g u|) ≤ K * h * (2 * R + h) := by
  have hKnn : 0 ≤ K := by
    have h1 := hK 1 0
    have h2 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h2, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  have hlip : LipschitzWith ⟨K, hKnn⟩ g := lipschitzWith_iff_dist_le_mul.mpr fun u v => by
    rw [Real.dist_eq, Real.dist_eq]
    exact_mod_cast hK u v
  have hgc : Continuous g := hlip.continuous
  set d : ℝ → ℝ := fun u => |g (u + h) - g u| with hd
  have hdc : Continuous d := ((hgc.comp (continuous_id.add continuous_const)).sub hgc).abs
  have hzero : ∀ u : ℝ, u ∉ Icc (-R - h) R → d u = 0 := by
    intro u hu
    rw [mem_Icc, not_and_or] at hu
    have h1 : g (u + h) = 0 ∧ g u = 0 := by
      rcases hu with hu | hu
      · rw [not_le] at hu
        constructor
        · refine hsupp _ ?_
          rw [abs_of_neg (by linarith : u + h < 0)]
          linarith
        · refine hsupp _ ?_
          rw [abs_of_neg (by nlinarith : u < 0)]
          nlinarith
      · rw [not_le] at hu
        constructor
        · refine hsupp _ ?_
          rw [abs_of_pos (by linarith : (0:ℝ) < u + h)]
          linarith
        · refine hsupp _ ?_
          rw [abs_of_pos (by linarith : (0:ℝ) < u)]
          linarith
    rw [hd]
    simp [h1.1, h1.2]
  have hrestrict : (∫ u, d u) = ∫ u in Icc (-R - h) R, d u :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hdint : IntegrableOn d (Icc (-R - h) R) :=
    hdc.continuousOn.integrableOn_compact isCompact_Icc
  have hptw : ∀ u ∈ Icc (-R - h) R, d u ≤ K * h := by
    intro u _
    rw [hd]
    have := hK (u + h) u
    simpa [abs_of_nonneg hh] using this
  have hconst : IntegrableOn (fun _ : ℝ => K * h) (Icc (-R - h) R) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmono : (∫ u in Icc (-R - h) R, d u) ≤ ∫ u in Icc (-R - h) R, (K * h : ℝ) :=
    setIntegral_mono_on hdint hconst measurableSet_Icc hptw
  have hvol : (∫ u in Icc (-R - h) R, (K * h : ℝ)) = K * h * (2 * R + h) := by
    have hmeasval : (volume : Measure ℝ).real (Icc (-R - h) R) = 2 * R + h := by
      rw [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R - (-R - h))]
      ring
    rw [setIntegral_const, hmeasval, smul_eq_mul]
    ring
  rw [hrestrict]
  calc (∫ u in Icc (-R - h) R, d u) ≤ ∫ u in Icc (-R - h) R, (K * h : ℝ) := hmono
    _ = K * h * (2 * R + h) := hvol

/-- The flip form of the convolution integrand is integrable. -/
theorem integrable_mul_kernel_comp_sub {g V : ℝ → ℝ}
    (hgm : AEStronglyMeasurable g volume) (hg2 : Integrable (fun u => g u ^ 2))
    (hVm : AEStronglyMeasurable V volume) (hV2 : Integrable (fun t => V t ^ 2)) (x : ℝ) :
    Integrable (fun t => V t * g (x - t)) :=
  integrable_mul_of_sq_integrable hVm (aestronglyMeasurable_comp_sub hgm x)
    hV2 (integrable_sq_comp_sub hg2 x)

/-- **The squared `L²` translate modulus** of a Lipschitz compactly supported kernel is quadratic
in the shift. -/
theorem integral_sq_translate_sub_le_of_lipschitz {g : ℝ → ℝ} {K R : ℝ}
    (hK : ∀ u v : ℝ, |g u - g v| ≤ K * |u - v|)
    (hsupp : ∀ u : ℝ, R < |u| → g u = 0) (hR : 0 ≤ R) {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ u, (g (u + h) - g u) ^ 2) ≤ K ^ 2 * (2 * R + 1) * h ^ 2 := by
  have hKnn : 0 ≤ K := by
    have h1 := hK 1 0
    have h2 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h2, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  have hlip : LipschitzWith ⟨K, hKnn⟩ g := lipschitzWith_iff_dist_le_mul.mpr fun u v => by
    rw [Real.dist_eq, Real.dist_eq]
    exact_mod_cast hK u v
  have hgc : Continuous g := hlip.continuous
  set d : ℝ → ℝ := fun u => (g (u + h) - g u) ^ 2 with hd
  have hdc : Continuous d := ((hgc.comp (continuous_add_const h)).sub hgc).pow 2
  have hzero : ∀ u : ℝ, u ∉ Icc (-R - h) R → d u = 0 := by
    intro u hu
    rw [mem_Icc, not_and_or] at hu
    have h1 : g (u + h) = 0 ∧ g u = 0 := by
      rcases hu with hu | hu
      · rw [not_le] at hu
        constructor
        · refine hsupp _ ?_
          rw [abs_of_neg (by linarith : u + h < 0)]
          linarith
        · refine hsupp _ ?_
          rw [abs_of_neg (by nlinarith : u < 0)]
          nlinarith
      · rw [not_le] at hu
        constructor
        · refine hsupp _ ?_
          rw [abs_of_pos (by linarith : (0:ℝ) < u + h)]
          linarith
        · refine hsupp _ ?_
          rw [abs_of_pos (by linarith : (0:ℝ) < u)]
          linarith
    rw [hd]
    simp [h1.1, h1.2]
  have hrestrict : (∫ u, d u) = ∫ u in Icc (-R - h) R, d u :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hdint : IntegrableOn d (Icc (-R - h) R) :=
    hdc.continuousOn.integrableOn_compact isCompact_Icc
  have hptw : ∀ u ∈ Icc (-R - h) R, d u ≤ K ^ 2 * h ^ 2 := by
    intro u _
    rw [hd]
    have hstep := hK (u + h) u
    rw [show u + h - u = h from by ring, abs_of_nonneg hh0] at hstep
    have hnn : (0 : ℝ) ≤ |g (u + h) - g u| := abs_nonneg _
    calc (g (u + h) - g u) ^ 2 = |g (u + h) - g u| ^ 2 := (sq_abs _).symm
      _ ≤ (K * h) ^ 2 := pow_le_pow_left₀ hnn hstep 2
      _ = K ^ 2 * h ^ 2 := by ring
  have hconst : IntegrableOn (fun _ : ℝ => K ^ 2 * h ^ 2) (Icc (-R - h) R) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hmono : (∫ u in Icc (-R - h) R, d u)
      ≤ ∫ u in Icc (-R - h) R, (K ^ 2 * h ^ 2 : ℝ) :=
    setIntegral_mono_on hdint hconst measurableSet_Icc hptw
  have hvol : (∫ u in Icc (-R - h) R, (K ^ 2 * h ^ 2 : ℝ))
      = K ^ 2 * h ^ 2 * (2 * R + h) := by
    have hmeasval : (volume : Measure ℝ).real (Icc (-R - h) R) = 2 * R + h := by
      rw [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ R - (-R - h))]
      ring
    rw [setIntegral_const, hmeasval, smul_eq_mul]
    ring
  rw [hrestrict]
  calc (∫ u in Icc (-R - h) R, d u)
      ≤ ∫ u in Icc (-R - h) R, (K ^ 2 * h ^ 2 : ℝ) := hmono
    _ = K ^ 2 * h ^ 2 * (2 * R + h) := hvol
    _ ≤ K ^ 2 * (2 * R + 1) * h ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hh1 (mul_nonneg (sq_nonneg K) (sq_nonneg h))]

/-- **The support shift.**  A kernel supported in `[−r, r]` convolved against a profile vanishing
below `a` vanishes below `a − r`. -/
theorem lineConvolution_eq_zero_of_lt {g V : ℝ → ℝ} {r a : ℝ}
    (hsupp : ∀ u : ℝ, r < |u| → g u = 0)
    (hVsupp : ∀ t : ℝ, t < a → V t = 0) {x : ℝ} (hx : x < a - r) :
    lineConvolution g V x = 0 := by
  rw [lineConvolution]
  have hzero : ∀ t : ℝ, g t * V (x - t) = 0 := by
    intro t
    rcases le_or_gt t r with ht | ht
    · rcases le_or_gt (-r) t with ht' | ht'
      · have : x - t < a := by linarith
        rw [hVsupp _ this, mul_zero]
      · rw [hsupp t (lt_of_lt_of_le (by linarith) (neg_le_abs t)), zero_mul]
    · rw [hsupp t (lt_of_lt_of_le ht (le_abs_self t)), zero_mul]
  simp only [hzero]
  exact integral_zero _ _

end GaloisForLFunctions.HTGeometry
