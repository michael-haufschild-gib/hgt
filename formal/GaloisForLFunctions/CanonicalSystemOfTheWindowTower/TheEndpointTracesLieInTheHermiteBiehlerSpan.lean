import GaloisForLFunctions.HTGeometry.FourierZeroFlipRealZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ReflectionExchangesTheWeilEndpointTraces

/-!
# Endpoint traces in the Hermite–Biehler span

The physical zero-moving correction is differentiable and vanishes at both
aperture endpoints. It therefore has zero normalized logarithmic trace.
Applying this invariance to the projected evaluation vectors expresses each
actual endpoint trace in terms of the two anchored Hermite–Biehler functions.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open GaloisForLFunctions.HTGeometry.FourierZeroFlip
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact


private theorem tendsto_endpoint_scale : Tendsto (fun t : ℝ => t * Real.sqrt (Real.log (1/t)))
    (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by norm_num)).neg.sqrt
  simp only [Real.rpow_two, neg_zero, Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  rw [one_div, Real.log_inv, show -(Real.log t*t^2) = t^2*(-Real.log t) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht']

private theorem tendsto_endpoint_quotient {f : ℝ → ℂ} {d : ℂ} (hf : HasDerivAt f d 0) (h0 : f 0 = 0) :
    Tendsto (fun t : ℝ => f t / (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  have h := hf.tendsto_slope_zero_right
  simpa only [zero_add, h0, sub_zero, Complex.real_smul, Complex.ofReal_inv,
    div_eq_mul_inv, mul_comm] using h

-- A differentiable function vanishing at the endpoint is negligible on the logarithmic trace scale.
private theorem differentiable_normalized_trace_zero {f : ℝ → ℂ} (hf : DifferentiableAt ℝ f 0) (h0 : f 0 = 0) :
    Tendsto (fun t : ℝ => f t * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hq := tendsto_endpoint_quotient hf.hasDerivAt h0
  have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_endpoint_scale
  have hp : Tendsto (fun t : ℝ => f t/(t : ℂ) *
      ((t*Real.sqrt (Real.log (1/t)) : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Complex.ofReal_zero, mul_zero, Function.comp_def] using hq.mul hs
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (show 0 < t from ht))
  push_cast
  field_simp

private theorem differentiable_flipAux (L : ℝ) {f : ℝ → ℂ} (hc : Continuous f) (κ : ℂ) :
    Differentiable ℝ (flipAux L f κ) := by
  have hp : Differentiable ℝ (prim L f κ) := fun x =>
    (hasDerivAt_prim L hc κ x).differentiableAt
  unfold flipAux
  fun_prop

private theorem flipAux_left_trace_zero {L : ℝ} {f : ℝ → ℂ} (hc : Continuous f) (hs : SupportedIn L f)
    (κ : ℂ) :
    Tendsto (fun t : ℝ => flipAux L f κ (t-L) * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply differentiable_normalized_trace_zero
  · exact ((differentiable_flipAux L hc κ).comp (differentiable_id.sub_const L)).differentiableAt
  · simp only [zero_sub, flipAux, prim_eq_zero_of_le hc hs κ le_rfl, mul_zero]

private theorem flipAux_right_trace_zero {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℂ} (hc : Continuous f)
    (hs : SupportedIn L f) {κ : ℂ} (hz : paperFT f κ = 0) :
    Tendsto (fun t : ℝ => flipAux L f κ (L-t) * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply differentiable_normalized_trace_zero
  · have hlin : Differentiable ℝ (fun t : ℝ => L-t) := by fun_prop
    exact ((differentiable_flipAux L hc κ).comp hlin).differentiableAt
  · simp only [sub_zero, flipAux, prim_eq_paperFT_of_ge hL hc hs κ le_rfl, hz, mul_zero]

private theorem paperFT_sub_compact {L : ℝ} (hL : 0 ≤ L) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfs : SupportedIn L f)
    (hgs : SupportedIn L g) (w : ℂ) :
    paperFT (f-g) w = paperFT f w - paperFT g w := by
  have hs : SupportedIn L (f-g) := by
    intro x hx
    simp only [Pi.sub_apply, hfs x hx, hgs x hx, sub_self]
  rw [paperFT_eq_intervalIntegral hL hs, paperFT_eq_intervalIntegral hL hfs,
    paperFT_eq_intervalIntegral hL hgs]
  have hfi : IntervalIntegrable (fun x : ℝ => f x * cexp (I*w*x)) volume (-L) L :=
    (by fun_prop : Continuous (fun x : ℝ => f x * cexp (I*w*x))).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun x : ℝ => g x * cexp (I*w*x)) volume (-L) L :=
    (by fun_prop : Continuous (fun x : ℝ => g x * cexp (I*w*x))).intervalIntegrable _ _
  simp only [Pi.sub_apply, sub_mul]
  exact intervalIntegral.integral_sub hfi hgi

open _root_.RHTower

/-- The canonical continuous physical Riesz source has the exact Weil kernel as its Fourier transform. -/
theorem paperFT_evalVectorContinuousRepresentative (a : PrecontactAperture) (z w : ℂ) :
    paperFT (evalVectorContinuousRepresentative a z) w = kernel a z w := by
  change _ = fourier a (evalVector a z) w
  rw [fourier_eq_whole]
  unfold suzukiCompactL2Fourier
  have hcut : suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)) : SoninL2) =
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)) : SoninL2) :=
    indicatorCutoff_suzukiApertureHilbert a.1 _
  change paperFT (evalVectorContinuousRepresentative a z) w =
    ∫ x : ℝ, (suzukiCutoff a.1.1
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)) : SoninL2)) x *
        Complex.exp (I*w*(x : ℂ))
  rw [hcut, ccmArchimedeanFormToAperture_coe]
  apply integral_congr_ae
  filter_upwards [evalVectorContinuousRepresentative_ae a z] with x hx
  rw [hx]

private def projectedRieszSource (a : PrecontactAperture) (κ z : ℂ) : ℝ → ℂ :=
  (‖evalVector a κ‖ : ℂ)^2 • evalVectorContinuousRepresentative a z -
    kernel a z κ • evalVectorContinuousRepresentative a κ

private theorem supportedIn_evalVectorContinuousRepresentative (a : PrecontactAperture) (z : ℂ) :
    SupportedIn a.1.1 (evalVectorContinuousRepresentative a z) := by
  intro x hx
  apply evalVectorContinuousRepresentative_eq_zero
  by_cases hl : x ≤ -a.1.1
  · exact Or.inl hl
  · exact Or.inr (le_of_not_ge fun hr => hx ⟨(lt_of_not_ge hl).le,hr⟩)

private theorem continuous_projectedRieszSource (a : PrecontactAperture) (κ z : ℂ) :
    Continuous (projectedRieszSource a κ z) := by
  exact (continuous_const.smul (continuous_evalVectorContinuousRepresentative a z)).sub
    (continuous_const.smul (continuous_evalVectorContinuousRepresentative a κ))

private theorem supportedIn_projectedRieszSource (a : PrecontactAperture) (κ z : ℂ) :
    SupportedIn a.1.1 (projectedRieszSource a κ z) := by
  intro x hx
  simp only [projectedRieszSource, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    supportedIn_evalVectorContinuousRepresentative a z x hx, supportedIn_evalVectorContinuousRepresentative a κ x hx, mul_zero, sub_self]

private theorem paperFT_projectedRieszSource (a : PrecontactAperture) (κ z w : ℂ) :
    paperFT (projectedRieszSource a κ z) w = fourier a (kernelNumerator a κ z) w := by
  have hsc (c : ℂ) (v : ℂ) : Continuous (c • evalVectorContinuousRepresentative a v) :=
    continuous_const.smul (continuous_evalVectorContinuousRepresentative a v)
  have hss (c : ℂ) (v : ℂ) : SupportedIn a.1.1 (c • evalVectorContinuousRepresentative a v) := by
    intro x hx
    simp only [Pi.smul_apply, supportedIn_evalVectorContinuousRepresentative a v x hx, smul_zero]
  rw [projectedRieszSource, paperFT_sub_compact a.1.2.le (hsc _ _) (hsc _ _) (hss _ _) (hss _ _),
    _root_.RHTower.paperFT_smul, _root_.RHTower.paperFT_smul, paperFT_evalVectorContinuousRepresentative, paperFT_evalVectorContinuousRepresentative]
  change _ = eval a w (_ - _)
  rw [map_sub, map_smul, map_smul]
  rfl

private def scaledProjectedRieszSource (a : PrecontactAperture) (κ z : ℂ) : ℝ → ℂ :=
  (starRingEnd ℂ) (z-star κ) • projectedRieszSource a κ z

private theorem continuous_scaledProjectedRieszSource (a : PrecontactAperture) (κ z : ℂ) :
    Continuous (scaledProjectedRieszSource a κ z) := continuous_const.smul (continuous_projectedRieszSource a κ z)

private theorem supportedIn_scaledProjectedRieszSource (a : PrecontactAperture) (κ z : ℂ) :
    SupportedIn a.1.1 (scaledProjectedRieszSource a κ z) := by
  intro x hx
  simp only [scaledProjectedRieszSource, Pi.smul_apply, supportedIn_projectedRieszSource a κ z x hx, smul_zero]

private theorem paperFT_scaledProjectedRieszSource (a : PrecontactAperture) (κ z w : ℂ) :
    paperFT (scaledProjectedRieszSource a κ z) w =
      (starRingEnd ℂ) (z-star κ) * fourier a (kernelNumerator a κ z) w := by
  rw [scaledProjectedRieszSource, _root_.RHTower.paperFT_smul, paperFT_projectedRieszSource]

private theorem paperFT_scaledProjectedRieszSource_zero (a : PrecontactAperture) (κ z : ℂ) :
    paperFT (scaledProjectedRieszSource a κ z) κ = 0 := by
  rw [paperFT_scaledProjectedRieszSource]
  have hz : fourier a (kernelNumerator a κ z) κ = 0 := (kernelNumerator a κ z).property
  rw [hz, mul_zero]

private theorem zeroMove_scaledProjectedRieszSource_fourier (a : PrecontactAperture) (κ z w : ℂ) :
    (w-κ)*paperFT (scaledProjectedRieszSource a (star κ) z) w =
      (w-star κ)*paperFT (scaledProjectedRieszSource a κ z) w := by
  have he := congrArg (fun x : evaluationKernel a κ =>
    fourier a (zeroMove a κ x) w) (zeroMove_kernelNumerator a κ z)
  simp only [map_smul, LinearIsometryEquiv.apply_symm_apply] at he
  change eval a w ((starRingEnd ℂ) (z-κ) • (kernelNumerator a (star κ) z : WeilHilbertBeforeContact a)) =
    eval a w ((starRingEnd ℂ) (z-star κ) • (zeroMove a κ (kernelNumerator a κ z) : WeilHilbertBeforeContact a)) at he
  rw [map_smul, map_smul] at he
  rw [paperFT_scaledProjectedRieszSource, paperFT_scaledProjectedRieszSource, star_star]
  have hu := zeroMove_fourier a κ w (kernelNumerator a κ z)
  simp only [fourier, smul_eq_mul] at he hu ⊢
  linear_combination (w-κ)*he +
    (starRingEnd ℂ) (z-star κ)*hu

-- Compact Fourier uniqueness identifies the abstract unitary with its explicit physical zero flip.
private theorem zeroFlip_scaledProjectedRieszSource (a : PrecontactAperture) (κ z : ℂ) :
    scaledProjectedRieszSource a (star κ) z = zeroFlip a.1.1 (scaledProjectedRieszSource a κ z) κ := by
  have hc := continuous_zeroFlip a.1.1 (continuous_scaledProjectedRieszSource a κ z) κ
  have hs := supportedIn_zeroFlip a.1.2.le (continuous_scaledProjectedRieszSource a κ z)
    (supportedIn_scaledProjectedRieszSource a κ z) (paperFT_scaledProjectedRieszSource_zero a κ z)
  apply sub_eq_zero.mp
  refine GaloisForLFunctions.HTGeometry.FourierZeroFlip.eq_zero_of_paperFT_eq_zero
    (L := a.1.1) ((continuous_scaledProjectedRieszSource a (star κ) z).sub hc) ?_ κ.re ?_
  · intro x hx
    simp only [Pi.sub_apply, supportedIn_scaledProjectedRieszSource a (star κ) z x hx, hs x hx, sub_self]
  · intro t ht
    have hw : (t : ℂ) ≠ κ := fun he => ht (by simpa only [Complex.ofReal_re] using congrArg Complex.re he)
    rw [paperFT_sub_compact a.1.2.le (continuous_scaledProjectedRieszSource a (star κ) z) hc
      (supportedIn_scaledProjectedRieszSource a (star κ) z) hs,
      paperFT_zeroFlip a.1.2.le (continuous_scaledProjectedRieszSource a κ z) (supportedIn_scaledProjectedRieszSource a κ z)
        (paperFT_scaledProjectedRieszSource_zero a κ z) hw]
    apply sub_eq_zero.mpr
    apply (eq_div_iff (sub_ne_zero.mpr hw)).mpr
    linear_combination zeroMove_scaledProjectedRieszSource_fourier a κ z t

private theorem scaledProjectedRieszSource_normalized_limit (a : PrecontactAperture) (κ z : ℂ) {p : ℝ → ℝ} {τ : ℂ → ℂ}
    (ht : ∀ v, Tendsto (fun t : ℝ => evalVectorContinuousRepresentative a v (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (τ v))) :
    Tendsto (fun t : ℝ => scaledProjectedRieszSource a κ z (p t) * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((starRingEnd ℂ) (z-star κ) *
        ((‖evalVector a κ‖ : ℂ)^2 * τ z-kernel a z κ * τ κ))) := by
  have h := (((ht z).const_mul ((‖evalVector a κ‖ : ℂ)^2)).sub
    ((ht κ).const_mul (kernel a z κ))).const_mul ((starRingEnd ℂ) (z-star κ))
  apply h.congr
  intro t
  simp only [scaledProjectedRieszSource, projectedRieszSource, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem trace_projection_relation (a : PrecontactAperture) (κ z : ℂ) {p : ℝ → ℝ} {τ : ℂ → ℂ}
    (ht : ∀ v, Tendsto (fun t : ℝ => evalVectorContinuousRepresentative a v (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (τ v)))
    (hf : Tendsto (fun t : ℝ => flipAux a.1.1 (scaledProjectedRieszSource a κ z) κ (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (starRingEnd ℂ) (z-κ) *
      ((‖evalVector a κ‖ : ℂ)^2 * τ z-kernel a z (star κ) * τ (star κ)) =
    (starRingEnd ℂ) (z-star κ) *
      ((‖evalVector a κ‖ : ℂ)^2 * τ z-kernel a z κ * τ κ) := by
  have h₁ := scaledProjectedRieszSource_normalized_limit a (star κ) z ht
  have hn : ‖evalVector a (star κ)‖ = ‖evalVector a κ‖ := norm_evalVector_conj a κ
  rw [star_star, hn] at h₁
  have h₂ := (scaledProjectedRieszSource_normalized_limit a κ z ht).add (hf.const_mul (κ-(starRingEnd ℂ) κ))
  simp only [mul_zero, add_zero] at h₂
  have he : (fun t : ℝ => scaledProjectedRieszSource a (star κ) z (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) =
    (fun t : ℝ => scaledProjectedRieszSource a κ z (p t) * (Real.sqrt (Real.log (1/t)) : ℂ)+
      (κ-(starRingEnd ℂ) κ)*(flipAux a.1.1 (scaledProjectedRieszSource a κ z) κ (p t)*
        (Real.sqrt (Real.log (1/t)) : ℂ))) := by
    funext t
    rw [zeroFlip_scaledProjectedRieszSource]
    unfold zeroFlip
    ring
  rw [he] at h₁
  exact tendsto_nhds_unique h₁ h₂

private theorem trace_hermiteBiehler_span (a : PrecontactAperture) (z : ℂ) {p : ℝ → ℝ} {τ : ℂ → ℂ}
    (ht : ∀ v, Tendsto (fun t : ℝ => evalVectorContinuousRepresentative a v (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (τ v)))
    (hf : Tendsto (fun t : ℝ => flipAux a.1.1 (scaledProjectedRieszSource a I z) I (p t) *
      (Real.sqrt (Real.log (1/t)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    2*I*(‖evalVector a I‖ : ℂ)^2 * τ z =
      hermiteBiehler a ((starRingEnd ℂ) z)*τ (-I)-
        (starRingEnd ℂ) (hermiteBiehler a z)*τ I := by
  have h := trace_projection_relation a I z ht hf
  simp only [show star (I : ℂ) = -I from Complex.conj_I, map_sub, map_neg, Complex.conj_I] at h
  have hk : kernel a I ((starRingEnd ℂ) z) = kernel a z (-I) := by
    calc
      _ = (starRingEnd ℂ) (kernel a (-I) z) := by
        simpa only [map_neg, Complex.conj_I, neg_neg, starRingEnd_self_apply] using
          kernel_conj a (-I) ((starRingEnd ℂ) z)
      _ = _ := kernel_symm a (-I) z
  rw [hermiteBiehler, hermiteBiehler, map_mul, map_add, Complex.conj_I, kernel_symm, hk]
  linear_combination h

/-- The actual left endpoint trace lies in the Hermite–Biehler span, including both anchor points. -/
theorem evalVectorLeftTrace_hermiteBiehler_span (a : PrecontactAperture) (z : ℂ) :
    2*I*(‖evalVector a I‖ : ℂ)^2 * evalVectorLeftTrace a z =
      hermiteBiehler a ((starRingEnd ℂ) z)*evalVectorLeftTrace a (-I)-
        (starRingEnd ℂ) (hermiteBiehler a z)*evalVectorLeftTrace a I := by
  apply trace_hermiteBiehler_span a z (p := fun t => t-a.1.1)
    (fun v => evalVectorContinuousRepresentative_left_normalized_limit a v)
  exact flipAux_left_trace_zero (continuous_scaledProjectedRieszSource a I z) (supportedIn_scaledProjectedRieszSource a I z) I

/-- The actual right endpoint trace lies in the same Hermite–Biehler span. -/
theorem evalVectorRightTrace_hermiteBiehler_span (a : PrecontactAperture) (z : ℂ) :
    2*I*(‖evalVector a I‖ : ℂ)^2 * evalVectorRightTrace a z =
      hermiteBiehler a ((starRingEnd ℂ) z)*evalVectorRightTrace a (-I)-
        (starRingEnd ℂ) (hermiteBiehler a z)*evalVectorRightTrace a I := by
  apply trace_hermiteBiehler_span a z (p := fun t => a.1.1-t)
    (fun v => evalVectorContinuousRepresentative_right_normalized_limit a v)
  exact flipAux_right_trace_zero a.1.2.le (continuous_scaledProjectedRieszSource a I z) (supportedIn_scaledProjectedRieszSource a I z) (paperFT_scaledProjectedRieszSource_zero a I z)

/-- The left trace at the imaginary anchor is real by reflection and conjugation. -/
theorem evalVectorLeftTrace_I_im (a : PrecontactAperture) : (evalVectorLeftTrace a I).im = 0 := by
  have h := evalVectorLeftTrace_conj a (-I)
  rw [map_neg, Complex.conj_I, neg_neg, evalVectorRightTrace_eq_leftTrace_neg, neg_neg] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith only [hi]

/-- The right trace at the imaginary anchor is real by reflection and conjugation. -/
theorem evalVectorRightTrace_I_im (a : PrecontactAperture) : (evalVectorRightTrace a I).im = 0 := by
  have h := evalVectorLeftTrace_conj a I
  rw [Complex.conj_I, ← evalVectorRightTrace_eq_leftTrace_neg] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith only [hi]

#print axioms evalVectorLeftTrace_hermiteBiehler_span
#print axioms evalVectorRightTrace_hermiteBiehler_span

#print axioms paperFT_evalVectorContinuousRepresentative
#print axioms evalVectorLeftTrace_I_im
#print axioms evalVectorRightTrace_I_im

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
