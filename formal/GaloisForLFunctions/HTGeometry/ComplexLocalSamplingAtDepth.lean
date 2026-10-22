import GaloisForLFunctions.HTGeometry.LogDensityPlancherelPolya

/-!
# Sampling a transform at complex points of bounded depth

The reproducing identity of the localised sampling bound holds verbatim at a complex point, with
the kernel evaluated there: for `f` supported in `[−a, a]` with integrable transform,

`Φ(z) = ∫ Φ(y) K_a(z − y) dy`,  `K_a(w) = ∫ T_a(t) e^{−2πi w t} dt`,

because the trapezoidal cutoff `T_a` is one on the support of `f`.  The kernel keeps its
quadratic decay in `Re w` and pays only `e^{6πa|Im w|}` for the depth, since the box transforms
satisfy `|S_p(w)| ≤ min(2p, (π|Re w|)^{-1}) e^{2πp|Im w|}`.  Consequently the logarithmic-density
sampling inequality extends to points off the real axis, with the depth entering as one explicit
exponential factor and the right-hand side still only the logarithmically weighted energy of `Φ`
on the real line.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.LocalSampling

noncomputable section
set_option autoImplicit false

/-! ## The complex character and the box transform -/

/-- The Fourier character at a complex frequency. -/
def chi (w : ℂ) (t : ℝ) : ℂ := Complex.exp (-(2 * π * Complex.I) * w * (t : ℂ))

theorem norm_chi (w : ℂ) (t : ℝ) : ‖chi w t‖ = Real.exp (2 * π * t * w.im) := by
  rw [chi, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem norm_chi_le {p : ℝ} (_hp : 0 ≤ p) (w : ℂ) {t : ℝ} (ht : |t| ≤ p) :
    ‖chi w t‖ ≤ Real.exp (2 * π * p * |w.im|) := by
  rw [norm_chi]
  apply Real.exp_le_exp.mpr
  rcases abs_le.mp ht with ⟨h1, h2⟩
  rcases le_or_gt 0 w.im with hw | hw
  · rw [abs_of_nonneg hw]
    have : 2 * π * t ≤ 2 * π * p := by nlinarith [Real.pi_pos]
    nlinarith [Real.pi_pos]
  · rw [abs_of_neg hw]
    nlinarith [Real.pi_pos, mul_nonneg (by linarith : (0:ℝ) ≤ t + p)
      (by linarith : (0:ℝ) ≤ -w.im)]

/-- The character agrees with the real Fourier character at real frequencies. -/
theorem chi_ofReal (x t : ℝ) : chi (x : ℂ) t = Complex.exp (((-2 * π * t * x : ℝ) : ℂ) * Complex.I) := by
  rw [chi]
  congr 1
  push_cast
  ring

/-- The box transform at a complex frequency. -/
def boxTransform (p : ℝ) (w : ℂ) : ℂ := ∫ t in Icc (-p) p, chi w t

theorem boxTransform_ofReal (p x : ℝ) : boxTransform p (x : ℂ) = 𝓕 (boxFn p) x := by
  rw [boxTransform, fourier_boxFn_eq]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [chi_ofReal]
  congr 1
  push_cast
  ring

theorem norm_boxTransform_le_two_mul {p : ℝ} (hp : 0 ≤ p) (w : ℂ) :
    ‖boxTransform p w‖ ≤ 2 * p * Real.exp (2 * π * p * |w.im|) := by
  rw [boxTransform]
  have hbd : ∀ t ∈ Icc (-p) p, ‖chi w t‖ ≤ Real.exp (2 * π * p * |w.im|) := by
    intro t ht
    exact norm_chi_le hp w (abs_le.mpr ⟨ht.1, ht.2⟩)
  have := norm_setIntegral_le_of_norm_le_const
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbd
  refine this.trans (le_of_eq ?_)
  have hvol : volume.real (Icc (-p) p) = 2 * p := by
    rw [MeasureTheory.Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol]
  ring

theorem norm_boxTransform_le_inv {p : ℝ} (hp : 0 ≤ p) {w : ℂ} (hw : w ≠ 0) :
    ‖boxTransform p w‖ ≤ (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * p * |w.im|)) := by
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : -(2 * π * Complex.I) * w ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)) hw
  set c : ℂ := -(2 * π * Complex.I) * w with hcdef
  have hIcc : (∫ t in Icc (-p) p, chi w t) = ∫ t in (-p)..p, Complex.exp (c * t) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [chi, hcdef]
  rw [boxTransform, hIcc, integral_exp_mul_complex hc]
  have hnum : ‖Complex.exp (c * ((p : ℝ) : ℂ)) - Complex.exp (c * ((-p : ℝ) : ℂ))‖ ≤
      2 * Real.exp (2 * π * p * |w.im|) := by
    have h1 : ‖Complex.exp (c * ((p : ℝ) : ℂ))‖ ≤ Real.exp (2 * π * p * |w.im|) := by
      have : Complex.exp (c * ((p : ℝ) : ℂ)) = chi w p := rfl
      rw [this]
      exact norm_chi_le hp w (by rw [abs_of_nonneg hp])
    have h2 : ‖Complex.exp (c * ((-p : ℝ) : ℂ))‖ ≤ Real.exp (2 * π * p * |w.im|) := by
      have : Complex.exp (c * ((-p : ℝ) : ℂ)) = chi w (-p) := rfl
      rw [this]
      exact norm_chi_le hp w (by rw [abs_neg, abs_of_nonneg hp])
    have h3 := norm_sub_le (Complex.exp (c * ((p : ℝ) : ℂ))) (Complex.exp (c * ((-p : ℝ) : ℂ)))
    linarith
  have hden : ‖c‖ = 2 * π * ‖w‖ := by
    rw [hcdef]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
    try ring
  have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_div, hden]
  rw [div_le_iff₀ (by positivity)]
  have hfin : (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * p * |w.im|)) * (2 * π * ‖w‖) =
      4 * Real.exp (2 * π * p * |w.im|) := by
    field_simp
    ring
  rw [hfin]
  linarith [hnum, Real.exp_pos (2 * π * p * |w.im|)]

/-! ## The kernel at a complex frequency -/

/-- The kernel at a complex frequency: the transform of the trapezoidal cutoff. -/
def sampKernelAt (a : ℝ) (w : ℂ) : ℂ := ∫ t : ℝ, trapFn a t * chi w t

theorem chi_add (w : ℂ) (s t : ℝ) : chi w (s + t) = chi w s * chi w t := by
  rw [chi, chi, chi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem boxTransform_eq_integral (p : ℝ) (w : ℂ) :
    boxTransform p w = ∫ t : ℝ, boxFn p t * chi w t := by
  rw [boxTransform, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Set.indicator_apply, boxFn_apply]
  by_cases ht : t ∈ Icc (-p) p
  · rw [if_pos ht, if_pos ht, one_mul]
  · rw [if_neg ht, if_neg ht, zero_mul]

theorem integrable_boxFn_mul_chi (p : ℝ) (w : ℂ) :
    Integrable fun t : ℝ => boxFn p t * chi w t := by
  have hmeas : Measurable fun t : ℝ => boxFn p t * chi w t := by
    refine Measurable.mul ?_ ?_
    · unfold boxFn
      exact (measurable_one.indicator measurableSet_Icc)
    · exact (Complex.continuous_exp.comp ((continuous_const.mul
        Complex.continuous_ofReal))).measurable
  rcases le_or_gt 0 p with hp | hp
  · refine Integrable.mono' (g := fun t : ℝ =>
      (Icc (-p) p).indicator (fun _ => Real.exp (2 * π * p * |w.im|)) t) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    · exact (integrable_indicator_iff measurableSet_Icc).2
        (integrableOn_const (hs := measure_Icc_lt_top.ne))
    · rw [norm_mul, Set.indicator_apply]
      by_cases ht : t ∈ Icc (-p) p
      · rw [if_pos ht]
        have h1 : ‖boxFn p t‖ ≤ 1 := norm_boxFn_le p t
        have h2 : ‖chi w t‖ ≤ Real.exp (2 * π * p * |w.im|) :=
          norm_chi_le hp w (abs_le.mpr ⟨ht.1, ht.2⟩)
        calc ‖boxFn p t‖ * ‖chi w t‖ ≤ 1 * Real.exp (2 * π * p * |w.im|) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ = Real.exp (2 * π * p * |w.im|) := one_mul _
      · rw [if_neg ht]
        have : boxFn p t = 0 := by
          rw [boxFn_apply, if_neg ht]
        rw [this, norm_zero, zero_mul]
  · have hzero : ∀ t : ℝ, boxFn p t * chi w t = 0 := by
      intro t
      have : boxFn p t = 0 := by
        rw [boxFn_apply, if_neg]
        intro hmem
        rcases hmem with ⟨h1, h2⟩
        linarith
      rw [this, zero_mul]
    simp only [hzero]
    exact integrable_zero ℝ ℂ volume

/-- **The complex-frequency product formula.**  The kernel is the product of the two box
transforms, by Fubini on the convolution that defines the cutoff. -/
theorem sampKernelAt_eq {a : ℝ} (ha : 0 < a) (w : ℂ) :
    sampKernelAt a w = ((2 * a)⁻¹ : ℂ) * (boxTransform a w * boxTransform (2 * a) w) := by
  have hinner : ∀ s : ℝ, (∫ t : ℝ, boxFn (2 * a) (t - s) * chi w t) =
      chi w s * boxTransform (2 * a) w := by
    intro s
    have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => boxFn (2 * a) (t - s) * chi w t) s
    rw [← hshift]
    have hcongr : ∀ u : ℝ, boxFn (2 * a) (u + s - s) * chi w (u + s) =
        chi w s * (boxFn (2 * a) u * chi w u) := by
      intro u
      rw [add_sub_cancel_right, chi_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_const_mul, boxTransform_eq_integral]
  have hprod : Integrable (Function.uncurry fun (t s : ℝ) =>
      boxFn a s * boxFn (2 * a) (t - s) * chi w t) (volume.prod volume) := by
    have hmeas : Measurable (Function.uncurry fun (t s : ℝ) =>
        boxFn a s * boxFn (2 * a) (t - s) * chi w t) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold boxFn
        exact (measurable_one.indicator measurableSet_Icc).comp measurable_snd
      · unfold boxFn
        exact (measurable_one.indicator measurableSet_Icc).comp
          (measurable_fst.sub measurable_snd)
      · exact ((Complex.continuous_exp.comp ((continuous_const.mul
          Complex.continuous_ofReal))).measurable).comp measurable_fst
    refine Integrable.mono' (g := fun z : ℝ × ℝ =>
      (Icc (-(3 * a)) (3 * a) ×ˢ Icc (-a) a).indicator
        (fun _ => Real.exp (2 * π * (3 * a) * |w.im|)) z) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    · refine (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).2 ?_
      refine integrableOn_const (hs := ?_)
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
    · obtain ⟨t, s⟩ := z
      simp only [Function.uncurry_apply_pair, Set.indicator_apply]
      by_cases hz : (t, s) ∈ Icc (-(3 * a)) (3 * a) ×ˢ Icc (-a) a
      · rw [if_pos hz, norm_mul, norm_mul]
        have h1 : ‖boxFn a s‖ ≤ 1 := norm_boxFn_le a s
        have h2 : ‖boxFn (2 * a) (t - s)‖ ≤ 1 := norm_boxFn_le _ _
        have h3 : ‖chi w t‖ ≤ Real.exp (2 * π * (3 * a) * |w.im|) := by
          refine norm_chi_le (by linarith) w ?_
          rcases hz with ⟨hz1, _⟩
          rw [Set.mem_Icc] at hz1
          exact abs_le.mpr ⟨hz1.1, hz1.2⟩
        calc ‖boxFn a s‖ * ‖boxFn (2 * a) (t - s)‖ * ‖chi w t‖
            ≤ 1 * 1 * Real.exp (2 * π * (3 * a) * |w.im|) := by
              refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3
                (norm_nonneg _) (by norm_num)
          _ = Real.exp (2 * π * (3 * a) * |w.im|) := by ring
      · rw [if_neg hz]
        have hzero : boxFn a s * boxFn (2 * a) (t - s) = 0 := by
          by_cases h2 : s ∈ Icc (-a) a
          · have h1 : t ∉ Icc (-(3 * a)) (3 * a) := by
              intro hc
              exact hz ⟨hc, h2⟩
            rw [Set.mem_Icc] at h2
            have : boxFn (2 * a) (t - s) = 0 := by
              rw [boxFn_apply, if_neg]
              intro hc
              rw [Set.mem_Icc] at hc
              rw [Set.mem_Icc] at h1
              rcases not_and_or.mp h1 with h | h
              · have hlt : t < -(3 * a) := not_le.mp h
                linarith [hc.1, h2.2]
              · have hlt : 3 * a < t := not_le.mp h
                linarith [hc.2, h2.1]
            rw [this, mul_zero]
          · have : boxFn a s = 0 := by rw [boxFn_apply, if_neg h2]
            rw [this, zero_mul]
        rw [hzero, zero_mul, norm_zero]
  have hswap := MeasureTheory.integral_integral_swap hprod
  have houter : (∫ t : ℝ, trapFn a t * chi w t) =
      ((2 * a)⁻¹ : ℂ) * ∫ t : ℝ, ∫ s : ℝ, boxFn a s * boxFn (2 * a) (t - s) * chi w t := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [trapFn, convolution, ContinuousLinearMap.mul_apply']
    rw [MeasureTheory.integral_mul_const, mul_assoc]
  rw [sampKernelAt, houter, hswap]
  have hinner2 : ∀ s : ℝ, (∫ t : ℝ, boxFn a s * boxFn (2 * a) (t - s) * chi w t) =
      boxFn a s * chi w s * boxTransform (2 * a) w := by
    intro s
    have hc : ∀ t : ℝ, boxFn a s * boxFn (2 * a) (t - s) * chi w t =
        boxFn a s * (boxFn (2 * a) (t - s) * chi w t) := by
      intro t; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hc),
      MeasureTheory.integral_const_mul, hinner s]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner2)]
  have hfin : (∫ s : ℝ, boxFn a s * chi w s * boxTransform (2 * a) w) =
      boxTransform a w * boxTransform (2 * a) w := by
    rw [MeasureTheory.integral_mul_const, ← boxTransform_eq_integral]
  rw [hfin]

end

end GaloisForLFunctions.HTGeometry.LocalSampling
