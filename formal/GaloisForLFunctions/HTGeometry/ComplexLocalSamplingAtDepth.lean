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

/-! ## Quadratic decay in the real direction, exponential cost in the depth -/

/-- **The kernel at depth.**  Quadratic decay in the real direction is kept; the depth costs one
explicit exponential factor. -/
theorem norm_sampKernelAt_le {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ‖sampKernelAt a w‖ ≤
      Real.exp (6 * π * a * |w.im|) * ((8 * a + a⁻¹) / (1 + w.re ^ 2)) := by
  have ha2 : (0:ℝ) < 2 * a := by linarith
  have hE : (0:ℝ) < Real.exp (6 * π * a * |w.im|) := Real.exp_pos _
  have hden : (0:ℝ) < 1 + w.re ^ 2 := by positivity
  rw [sampKernelAt_eq ha, norm_mul, norm_mul]
  have hc : ‖((2 * a)⁻¹ : ℂ)‖ = (2 * a)⁻¹ := by
    rw [show ((2 * a)⁻¹ : ℂ) = (((2 * a)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hexp1 : Real.exp (2 * π * a * |w.im|) * Real.exp (2 * π * (2 * a) * |w.im|) =
      Real.exp (6 * π * a * |w.im|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rcases le_or_gt |w.re| 1 with hre | hre
  · have h1 : ‖boxTransform a w‖ ≤ 2 * a * Real.exp (2 * π * a * |w.im|) :=
      norm_boxTransform_le_two_mul ha.le w
    have h2 : ‖boxTransform (2 * a) w‖ ≤ 2 * (2 * a) * Real.exp (2 * π * (2 * a) * |w.im|) :=
      norm_boxTransform_le_two_mul ha2.le w
    have hmul : ‖boxTransform a w‖ * ‖boxTransform (2 * a) w‖ ≤
        (2 * a * Real.exp (2 * π * a * |w.im|)) *
          (2 * (2 * a) * Real.exp (2 * π * (2 * a) * |w.im|)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have hstep : (2 * a)⁻¹ * (‖boxTransform a w‖ * ‖boxTransform (2 * a) w‖) ≤
        4 * a * Real.exp (6 * π * a * |w.im|) := by
      calc (2 * a)⁻¹ * (‖boxTransform a w‖ * ‖boxTransform (2 * a) w‖)
          ≤ (2 * a)⁻¹ * ((2 * a * Real.exp (2 * π * a * |w.im|)) *
              (2 * (2 * a) * Real.exp (2 * π * (2 * a) * |w.im|))) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 4 * a * (Real.exp (2 * π * a * |w.im|) *
              Real.exp (2 * π * (2 * a) * |w.im|)) := by field_simp; ring
        _ = 4 * a * Real.exp (6 * π * a * |w.im|) := by rw [hexp1]
    refine hstep.trans ?_
    have hsq : w.re ^ 2 ≤ 1 := by nlinarith [sq_abs w.re, abs_nonneg w.re]
    have h4a : 4 * a ≤ (8 * a + a⁻¹) / (1 + w.re ^ 2) := by
      rw [le_div_iff₀ hden]
      nlinarith [hsq, ha, inv_pos.mpr ha]
    calc 4 * a * Real.exp (6 * π * a * |w.im|)
        = Real.exp (6 * π * a * |w.im|) * (4 * a) := by ring
      _ ≤ Real.exp (6 * π * a * |w.im|) * ((8 * a + a⁻¹) / (1 + w.re ^ 2)) :=
          mul_le_mul_of_nonneg_left h4a hE.le
  · have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hre
      simp at hre
      linarith
    have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
    have h1 : ‖boxTransform a w‖ ≤ (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * a * |w.im|)) :=
      norm_boxTransform_le_inv ha.le hw0
    have h2 : ‖boxTransform (2 * a) w‖ ≤
        (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * (2 * a) * |w.im|)) :=
      norm_boxTransform_le_inv ha2.le hw0
    have hmul : ‖boxTransform a w‖ * ‖boxTransform (2 * a) w‖ ≤
        ((π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * a * |w.im|))) *
          ((π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * (2 * a) * |w.im|))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have hstep : (2 * a)⁻¹ * (‖boxTransform a w‖ * ‖boxTransform (2 * a) w‖) ≤
        Real.exp (6 * π * a * |w.im|) * (2 / (a * π ^ 2 * ‖w‖ ^ 2)) := by
      refine (mul_le_mul_of_nonneg_left hmul (by positivity)).trans (le_of_eq ?_)
      rw [← hexp1]
      field_simp
    refine hstep.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hE.le
    -- the real part controls the modulus, and `π² ≥ 9` closes the comparison
    have hre2 : (1:ℝ) < w.re ^ 2 := by nlinarith [sq_abs w.re, abs_nonneg w.re]
    have hnormsq : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
      have h' : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      nlinarith [abs_nonneg w.re, sq_abs w.re, norm_nonneg w]
    have hpi2 : (9:ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
    have hX : (0:ℝ) < a * π ^ 2 * ‖w‖ ^ 2 := by positivity
    rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hX]
    have hinv : a⁻¹ * (a * π ^ 2 * ‖w‖ ^ 2) = π ^ 2 * ‖w‖ ^ 2 := by field_simp
    have h8 : (0:ℝ) ≤ 8 * a * (a * π ^ 2 * ‖w‖ ^ 2) := by positivity
    have hexpand : (8 * a + a⁻¹) * (a * π ^ 2 * ‖w‖ ^ 2) =
        8 * a * (a * π ^ 2 * ‖w‖ ^ 2) + a⁻¹ * (a * π ^ 2 * ‖w‖ ^ 2) := by ring
    have hbig : π ^ 2 * ‖w‖ ^ 2 ≤ (8 * a + a⁻¹) * (a * π ^ 2 * ‖w‖ ^ 2) := by
      rw [hexpand, hinv]
      linarith
    have hfinal : 9 * w.re ^ 2 ≤ π ^ 2 * ‖w‖ ^ 2 := by
      nlinarith [hpi2, hnormsq, sq_nonneg w.re, norm_nonneg w]
    nlinarith [hbig, hfinal, hre2]

/-! ## The reproducing identity at a complex frequency -/

/-- The transform at a complex frequency. -/
def fourierAt (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, f t * chi z t

theorem chi_sub_ofReal (z : ℂ) (y t : ℝ) :
    chi (z - (y : ℂ)) t = chi z t * Complex.exp (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I) := by
  rw [chi, chi, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The kernel of a cutoff at a complex frequency. -/
def cutoffKernel (T : ℝ → ℂ) (w : ℂ) : ℂ := ∫ t : ℝ, T t * chi w t

theorem sampKernelAt_eq_cutoffKernel (a : ℝ) (w : ℂ) :
    sampKernelAt a w = cutoffKernel (trapFn a) w := rfl

/-- **The reproducing identity for an arbitrary plateau cutoff.**  If `T` is one on `[−a, a]` and
vanishes off `[−R, R]`, then a transform of a source supported in `[−a, a]` is, at every complex
frequency, the average of its restriction to the real line against the cutoff's kernel. -/
theorem fourierAt_eq_integral_of_cutoff {a R : ℝ} (hR : 0 ≤ R)
    {T : ℝ → ℂ} (hTc : Continuous T) (hTi : Integrable T)
    (hT1 : ∀ t : ℝ, |t| ≤ a → T t = 1) (hT0 : ∀ t : ℝ, R < |t| → T t = 0)
    {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (z : ℂ) :
    fourierAt f z = ∫ y : ℝ, 𝓕 f y * cutoffKernel T (z - (y : ℂ)) := by
  have hΦc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hcharc : Continuous fun p : ℝ × ℝ =>
      Complex.exp (((2 * π * (p.1 * p.2) : ℝ) : ℂ) * Complex.I) := by
    refine Complex.continuous_exp.comp ?_
    exact ((Complex.continuous_ofReal.comp (continuous_const.mul
      (continuous_fst.mul continuous_snd))).mul continuous_const)
  have hchic : Continuous fun t : ℝ => chi z t := by
    refine Complex.continuous_exp.comp ?_
    exact continuous_const.mul Complex.continuous_ofReal
  have hcharnorm : ∀ y t : ℝ,
      ‖Complex.exp (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    intro y t
    rw [Complex.norm_exp]
    have hre : (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  -- the double integrand
  let G : ℝ → ℝ → ℂ := fun y t =>
    𝓕 f y * (T t * chi z t *
      Complex.exp (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I))
  have hmeas : Measurable (Function.uncurry G) :=
    ((hΦc.measurable.comp measurable_fst).mul
      (((hTc.measurable.comp measurable_snd).mul
        (hchic.measurable.comp measurable_snd)).mul hcharc.measurable))
  have hFint : Integrable (Function.uncurry G) (volume.prod volume) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ =>
      ‖𝓕 f p.1‖ * (‖T p.2‖ * Real.exp (2 * π * R * |z.im|)))
      (Integrable.mul_prod hFi.norm (hTi.norm.mul_const _))
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp2 : |p.2| ≤ R
    · have hchi : ‖chi z p.2‖ ≤ Real.exp (2 * π * R * |z.im|) := norm_chi_le hR z hp2
      show ‖G p.1 p.2‖ ≤ _
      simp only [G, norm_mul, hcharnorm p.1 p.2, mul_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hchi (norm_nonneg _)) (norm_nonneg _)
    · have hTz : T p.2 = 0 := hT0 p.2 (not_le.mp hp2)
      show ‖G p.1 p.2‖ ≤ _
      simp [G, hTz]
  -- swap, then use inversion and that the cutoff is one on the support
  have hswap := MeasureTheory.integral_integral_swap hFint
  have hright : (∫ y : ℝ, 𝓕 f y * cutoffKernel T (z - (y : ℂ))) = ∫ y : ℝ, ∫ t : ℝ, G y t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [cutoffKernel]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [G]
    rw [chi_sub_ofReal]
    ring
  have hinner : ∀ t : ℝ, (∫ y : ℝ, G y t) = f t * (T t * chi z t) := by
    intro t
    have hfac : ∀ y : ℝ, G y t =
        (T t * chi z t) *
          (Complex.exp (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I) * 𝓕 f y) := by
      intro y
      simp only [G]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfac),
      MeasureTheory.integral_const_mul]
    have hinv : (∫ y : ℝ, Complex.exp (((2 * π * (y * t) : ℝ) : ℂ) * Complex.I) * 𝓕 f y) =
        f t := by
      have h := Real.fourierInv_eq' (𝓕 f) t
      have hfe : 𝓕⁻ (𝓕 f) = f := hfc.fourierInv_fourier_eq hf hFi
      rw [hfe] at h
      rw [h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have hinner_eq : (inner ℝ y t : ℝ) = y * t := by simp [RCLike.inner_apply, mul_comm]
      simp only [smul_eq_mul, hinner_eq]
    rw [hinv]
    ring
  rw [hright, hswap, integral_congr_ae (Filter.Eventually.of_forall hinner), fourierAt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show f t * chi z t = f t * (T t * chi z t)
  by_cases ht : |t| ≤ a
  · rw [hT1 t ht, one_mul]
  · rw [hsupp t (not_le.mp ht), zero_mul, zero_mul]

/-- **The reproducing identity at a complex frequency.**  The cutoff is one on the support of
`f`, so the transform at `z` is the kernel average of the transform on the real line. -/
theorem fourierAt_eq_integral {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (z : ℂ) :
    fourierAt f z = ∫ y : ℝ, 𝓕 f y * sampKernelAt a (z - (y : ℂ)) :=
  fourierAt_eq_integral_of_cutoff (a := a) (R := 3 * a) (by linarith)
    (continuous_trapFn a) (integrable_trapFn ha)
    (fun _ ht => trapFn_eq_one ha ht) (fun _ ht => trapFn_eq_zero ha ht)
    hfc hf hFi hsupp z

/-! ## Sampling at depth against a logarithmic density -/

theorem sub_ofReal_re (z : ℂ) (y : ℝ) : (z - (y : ℂ)).re = z.re - y := by simp

theorem sub_ofReal_im (z : ℂ) (y : ℝ) : (z - (y : ℂ)).im = z.im := by simp

/-- The kernel is measurable along a horizontal line. -/
theorem measurable_sampKernelAt_sub (a : ℝ) (z : ℂ) :
    Measurable fun y : ℝ => sampKernelAt a (z - (y : ℂ)) := by
  have hjoint : Continuous
      (Function.uncurry fun (y t : ℝ) => trapFn a t * chi (z - (y : ℂ)) t) := by
    refine Continuous.mul ((continuous_trapFn a).comp continuous_snd) ?_
    refine Complex.continuous_exp.comp ?_
    exact ((continuous_const.mul (continuous_const.sub
      (Complex.continuous_ofReal.comp continuous_fst))).mul
      (Complex.continuous_ofReal.comp continuous_snd))
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- **Sampling at depth against a kernel of quadratic decay.**  For any kernel reproducing the
transform of `f` on the real line, with quadratic decay in the real direction and an exponential
cost `e^{2πR|Im w|}` in the depth, a weighted sum of squares over sample points of depth at most
`σ` whose real parts carry kernel mass at most `B φ` is bounded by the `φ`-weighted energy of the
transform.  The rate `R` is the support radius of the cutoff behind the kernel. -/
theorem sum_norm_sq_fourierAt_le_of_kernel {B σ R C : ℝ} (hR : 0 ≤ R) (hCnn : 0 ≤ C)
    (_hB : 0 ≤ B) (_hσ : 0 ≤ σ)
    {f : ℝ → ℂ} (hf : Integrable f)
    (K : ℂ → ℂ)
    (hKb : ∀ w : ℂ, ‖K w‖ ≤ Real.exp (2 * π * R * |w.im|) * (C / (1 + w.re ^ 2)))
    (hKm : ∀ z : ℂ, Measurable fun y : ℝ => K (z - (y : ℂ)))
    (hrep : ∀ z : ℂ, fourierAt f z = ∫ y : ℝ, 𝓕 f y * K (z - (y : ℂ)))
    (φ : ℝ → ℝ) (_hφ : ∀ y : ℝ, 0 ≤ φ y)
    (hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * φ y)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ q ∈ S, |(p q).im| ≤ σ) (hm : ∀ q, 0 ≤ m q)
    (hker : ∀ y : ℝ, (∑ q ∈ S, m q * (1 + ((p q).re - y) ^ 2)⁻¹) ≤ B * φ y) :
    ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2 ≤
      ((Real.exp (2 * π * R * σ) * (C * π)) *
        (Real.exp (2 * π * R * σ) * (C * B))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y := by
  classical
  have hM : (0:ℝ) ≤ C := hCnn
  have hE : (0:ℝ) < Real.exp (2 * π * R * σ) := Real.exp_pos _
  have hR2 : (0:ℝ) ≤ 2 * π * R := by
    have := Real.pi_pos
    nlinarith
  have hΦc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hcauchy : ∀ c : ℝ, Integrable fun y : ℝ => (1 + (c - y) ^ 2)⁻¹ := by
    intro c
    simpa using integrable_inv_one_add_sq.comp_sub_left c
  have hcauchymass : ∀ c : ℝ, (∫ y : ℝ, (1 + (c - y) ^ 2)⁻¹) = π := by
    intro c
    have h := MeasureTheory.integral_sub_left_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) volume c
    rw [h]
    exact integral_univ_inv_one_add_sq
  have hcw : ∀ c : ℝ, Integrable fun y : ℝ => (1 + (c - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 := by
    intro c
    have hmeas : Measurable fun y : ℝ => (1 + (c - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2 :=
      ((measurable_const.add ((measurable_const.sub measurable_id).pow_const 2)).inv).mul
        ((hΦc.norm.pow 2).measurable)
    refine Integrable.mono' hΦ2 hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hk1 : (1 + (c - y) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith [sq_nonneg (c - y)]
    nlinarith [hk1, sq_nonneg ‖𝓕 f y‖]
  -- the pointwise bound at one sample point
  have hpt : ∀ z : ℂ, |z.im| ≤ σ → ‖fourierAt f z‖ ^ 2 ≤
      (Real.exp (2 * π * R * σ) * (C * π)) *
        (Real.exp (2 * π * R * σ) * (C *
          ∫ y : ℝ, (1 + (z.re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2)) := by
    intro z hzs
    have hexpmono : Real.exp (2 * π * R * |z.im|) ≤ Real.exp (2 * π * R * σ) := by
      refine Real.exp_le_exp.mpr ?_
      have hprod : (0:ℝ) ≤ 2 * π * R * (σ - |z.im|) := mul_nonneg hR2 (by linarith)
      nlinarith [hprod]
    have hKb : ∀ y : ℝ, ‖K (z - (y : ℂ))‖ ≤
        Real.exp (2 * π * R * σ) * (C * (1 + (z.re - y) ^ 2)⁻¹) := by
      intro y
      have h := hKb (z - (y : ℂ))
      rw [sub_ofReal_re, sub_ofReal_im] at h
      calc ‖K (z - (y : ℂ))‖
          ≤ Real.exp (2 * π * R * |z.im|) * (C / (1 + (z.re - y) ^ 2)) := h
        _ = Real.exp (2 * π * R * |z.im|) * (C * (1 + (z.re - y) ^ 2)⁻¹) := by
            rw [div_eq_mul_inv]
        _ ≤ Real.exp (2 * π * R * σ) * (C * (1 + (z.re - y) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_right hexpmono (mul_nonneg hCnn (by positivity))
    have hwm : Measurable fun y : ℝ => ‖K (z - (y : ℂ))‖ :=
      (hKm z).norm
    have hwi : Integrable fun y : ℝ => ‖K (z - (y : ℂ))‖ := by
      refine Integrable.mono' (((hcauchy z.re).const_mul C).const_mul
        (Real.exp (2 * π * R * σ))) hwm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hKb y
    have hwg2 : Integrable fun y : ℝ => ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2 := by
      refine Integrable.mono' (hΦ2.const_mul (Real.exp (2 * π * R * σ) * C))
        (hwm.mul ((hΦc.norm.pow 2).measurable)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb : ‖K (z - (y : ℂ))‖ ≤
          Real.exp (2 * π * R * σ) * C := by
        refine (hKb y).trans ?_
        have hk1 : (1 + (z.re - y) ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          nlinarith [sq_nonneg (z.re - y)]
        have hle : C * (1 + (z.re - y) ^ 2)⁻¹ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hk1 hM
        nlinarith [hE.le, hle]
      calc ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2
          ≤ (Real.exp (2 * π * R * σ) * C) * ‖𝓕 f y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = Real.exp (2 * π * R * σ) * C * ‖𝓕 f y‖ ^ 2 := by ring
    have hnorm : ‖fourierAt f z‖ ≤
        ∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ := by
      rw [hrep z]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      congr 1 with y
      rw [norm_mul]
      ring
    have hCS := sq_integral_weighted_le (μ := (volume : Measure ℝ))
      (w := fun y : ℝ => ‖K (z - (y : ℂ))‖) (g := fun y : ℝ => ‖𝓕 f y‖)
      (fun y => norm_nonneg _) hwm.aestronglyMeasurable
      (hΦc.norm).aestronglyMeasurable hwi hwg2
    have hsq : ‖fourierAt f z‖ ^ 2 ≤
        (∫ y : ℝ, ‖K (z - (y : ℂ))‖) *
          ∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hCS
    have hmass : (∫ y : ℝ, ‖K (z - (y : ℂ))‖) ≤
        Real.exp (2 * π * R * σ) * (C * π) := by
      refine (integral_mono hwi (((hcauchy z.re).const_mul C).const_mul
        (Real.exp (2 * π * R * σ))) hKb).trans (le_of_eq ?_)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hcauchymass]
    have hsecond : (∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2) ≤
        Real.exp (2 * π * R * σ) * (C *
          ∫ y : ℝ, (1 + (z.re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by
      have hdom : Integrable fun y : ℝ =>
          Real.exp (2 * π * R * σ) * (C * ((1 + (z.re - y) ^ 2)⁻¹ *
            ‖𝓕 f y‖ ^ 2)) := ((hcw z.re).const_mul C).const_mul _
      refine (integral_mono hwg2 hdom fun y => ?_).trans (le_of_eq ?_)
      · have hb := hKb y
        calc ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2
            ≤ (Real.exp (2 * π * R * σ) * (C * (1 + (z.re - y) ^ 2)⁻¹)) *
                ‖𝓕 f y‖ ^ 2 := mul_le_mul_of_nonneg_right hb (by positivity)
          _ = Real.exp (2 * π * R * σ) * (C * ((1 + (z.re - y) ^ 2)⁻¹ *
                ‖𝓕 f y‖ ^ 2)) := by ring
      · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hpos1 : (0:ℝ) ≤ ∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2 :=
      integral_nonneg fun y => by positivity
    have hpos2 : (0:ℝ) ≤ Real.exp (2 * π * R * σ) * (C * π) :=
      mul_nonneg hE.le (mul_nonneg hCnn Real.pi_pos.le)
    calc ‖fourierAt f z‖ ^ 2
        ≤ (∫ y : ℝ, ‖K (z - (y : ℂ))‖) *
            ∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2 := hsq
      _ ≤ (Real.exp (2 * π * R * σ) * (C * π)) *
            ∫ y : ℝ, ‖K (z - (y : ℂ))‖ * ‖𝓕 f y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmass hpos1
      _ ≤ (Real.exp (2 * π * R * σ) * (C * π)) *
            (Real.exp (2 * π * R * σ) * (C *
              ∫ y : ℝ, (1 + (z.re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsecond hpos2
  -- sum over the sample points with their weights, exchange, and reproduce the density
  have hsum : ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2 ≤
      ∑ q ∈ S, m q * ((Real.exp (2 * π * R * σ) * (C * π)) *
        (Real.exp (2 * π * R * σ) * (C *
          ∫ y : ℝ, (1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2))) :=
    Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hpt (p q) (hSim q hq)) (hm q)
  have hCpos : (0:ℝ) ≤ (Real.exp (2 * π * R * σ) * (C * π)) *
      (Real.exp (2 * π * R * σ) * C) :=
    mul_nonneg (mul_nonneg hE.le (mul_nonneg hCnn Real.pi_pos.le))
      (mul_nonneg hE.le hCnn)
  have hstep1 : ∑ q ∈ S, m q * ((Real.exp (2 * π * R * σ) * (C * π)) *
      (Real.exp (2 * π * R * σ) * (C *
        ∫ y : ℝ, (1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2))) =
      ((Real.exp (2 * π * R * σ) * (C * π)) *
        (Real.exp (2 * π * R * σ) * C)) *
        ∑ q ∈ S, ∫ y : ℝ, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MeasureTheory.integral_const_mul]
    ring
  have hexch : ∑ q ∈ S, ∫ y : ℝ, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) =
      ∫ y : ℝ, ∑ q ∈ S, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) :=
    (MeasureTheory.integral_finsetSum S fun q _ => (hcw (p q).re).const_mul (m q)).symm
  have hinner : (∫ y : ℝ, ∑ q ∈ S, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2)) ≤
      B * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y := by
    have hL : Integrable fun y : ℝ =>
        ∑ q ∈ S, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) :=
      integrable_finsetSum S fun q _ => (hcw (p q).re).const_mul (m q)
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono hL (hint.const_mul _) fun y => ?_
    have hk := hker y
    have hfactor : ∑ q ∈ S, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) =
        (∑ q ∈ S, m q * (1 + ((p q).re - y) ^ 2)⁻¹) * ‖𝓕 f y‖ ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hfactor]
    calc (∑ q ∈ S, m q * (1 + ((p q).re - y) ^ 2)⁻¹) * ‖𝓕 f y‖ ^ 2
        ≤ (B * φ y) * ‖𝓕 f y‖ ^ 2 := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = B * (‖𝓕 f y‖ ^ 2 * φ y) := by ring
  calc ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2
      ≤ ∑ q ∈ S, m q * ((Real.exp (2 * π * R * σ) * (C * π)) *
          (Real.exp (2 * π * R * σ) * (C *
            ∫ y : ℝ, (1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2))) := hsum
    _ = ((Real.exp (2 * π * R * σ) * (C * π)) *
          (Real.exp (2 * π * R * σ) * C)) *
          ∑ q ∈ S, ∫ y : ℝ, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := hstep1
    _ = ((Real.exp (2 * π * R * σ) * (C * π)) *
          (Real.exp (2 * π * R * σ) * C)) *
          ∫ y : ℝ, ∑ q ∈ S, m q * ((1 + ((p q).re - y) ^ 2)⁻¹ * ‖𝓕 f y‖ ^ 2) := by rw [hexch]
    _ ≤ ((Real.exp (2 * π * R * σ) * (C * π)) *
          (Real.exp (2 * π * R * σ) * C)) *
          (B * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y) :=
        mul_le_mul_of_nonneg_left hinner hCpos
    _ = ((Real.exp (2 * π * R * σ) * (C * π)) *
          (Real.exp (2 * π * R * σ) * (C * B))) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y := by ring

/-- **Sampling at depth against a logarithmic density.**  A transform of a source supported in
`[−a, a]`, sampled with nonnegative weights at complex points of depth at most `σ` whose real
parts carry weight at most `A₀ log(|n|+3)` per unit window, is bounded by the logarithmically
weighted energy of the transform on the real line; the depth costs one explicit exponential. -/
theorem sum_norm_sq_fourierAt_le_of_kernelBound {a B σ : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0)
    (φ : ℝ → ℝ) (hφ : ∀ y : ℝ, 0 ≤ φ y)
    (hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * φ y)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ q ∈ S, |(p q).im| ≤ σ) (hm : ∀ q, 0 ≤ m q)
    (hker : ∀ y : ℝ, (∑ q ∈ S, m q * (1 + ((p q).re - y) ^ 2)⁻¹) ≤ B * φ y) :
    ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2 ≤
      ((Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * π)) *
        (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * B))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y := by
  have hrate : 2 * π * (3 * a) * σ = 6 * π * a * σ := by ring
  have hconc := sum_norm_sq_fourierAt_le_of_kernel (R := 3 * a) (C := 8 * a + a⁻¹)
    (by linarith) (by positivity) hB hσ hf (sampKernelAt a)
    (fun w => by
      have h := norm_sampKernelAt_le ha w
      have e : 2 * π * (3 * a) * |w.im| = 6 * π * a * |w.im| := by ring
      rw [e]
      exact h)
    (fun z => measurable_sampKernelAt_sub a z)
    (fun z => fourierAt_eq_integral ha hfc hf hFi hsupp z)
    φ hφ hΦ2 hint S p m hSim hm hker
  rwa [hrate] at hconc

/-- **Sampling at depth against a logarithmic density.**  The instance of the kernel-bound form in
which the per-window weight is `A₀ log(|n|+3)`: the right-hand side carries the archimedean
logarithm. -/
theorem sum_norm_sq_fourierAt_le {a A₀ σ : ℝ} (ha : 0 < a) (hA₀ : 0 ≤ A₀) (hσ : 0 ≤ σ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3))
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ q ∈ S, |(p q).im| ≤ σ) (hm : ∀ q, 0 ≤ m q)
    (hcount : ∀ n : ℤ,
      (∑ q ∈ S.filter fun q => (n : ℝ) ≤ (p q).re ∧ (p q).re ≤ (n : ℝ) + 1, m q) ≤
      A₀ * Real.log (|(n : ℝ)| + 3)) :
    ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2 ≤
      ((Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * π)) *
        (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * (3 * A₀ * logKernelConst)))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) := by
  have hΦc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hlog1 : ∀ y : ℝ, (1:ℝ) ≤ Real.log (|y| + 3) := by
    intro y
    have hlog3 : (1:ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
    linarith [abs_nonneg y]
  have hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 := by
    refine Integrable.mono' hint (hΦc.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hlog1 y, sq_nonneg ‖𝓕 f y‖]
  exact sum_norm_sq_fourierAt_le_of_kernelBound ha
    (by have := logKernelConst_nonneg; positivity) hσ hfc hf hFi hsupp
    (fun y => Real.log (|y| + 3)) (fun y => by linarith [hlog1 y]) hΦ2 hint S p m hSim hm
    (fun y => sum_kernel_le hA₀ S (fun q => (p q).re) m hm hcount y)

/-- **Sampling at depth against a bounded density.**  When the per-window weight is bounded by a
constant the right-hand side is the plain `L²` energy of the transform: no weight at all. -/
theorem sum_norm_sq_fourierAt_le_const {a A₀ σ : ℝ} (ha : 0 < a) (hA₀ : 0 ≤ A₀) (hσ : 0 ≤ σ)
    {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0)
    (hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ q ∈ S, |(p q).im| ≤ σ) (hm : ∀ q, 0 ≤ m q)
    (hcount : ∀ n : ℤ,
      (∑ q ∈ S.filter fun q => (n : ℝ) ≤ (p q).re ∧ (p q).re ≤ (n : ℝ) + 1, m q) ≤ A₀) :
    ∑ q ∈ S, m q * ‖fourierAt f (p q)‖ ^ 2 ≤
      ((Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * π)) *
        (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * (3 * A₀ * kernelConst)))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 := by
  have hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * (1 : ℝ) := by
    simpa using hΦ2
  have hconc := sum_norm_sq_fourierAt_le_of_kernelBound ha
    (by have := kernelConst_nonneg; positivity : (0:ℝ) ≤ 3 * A₀ * kernelConst)
    hσ hfc hf hFi hsupp
    (fun _ => (1 : ℝ)) (fun y => zero_le_one) hΦ2 hint S p m hSim hm
    (fun y => by
      have h := sum_kernel_le_const hA₀ S (fun q => (p q).re) m hm hcount y
      simpa using h)
  refine hconc.trans (le_of_eq ?_)
  congr 1
  simp

end

end GaloisForLFunctions.HTGeometry.LocalSampling
