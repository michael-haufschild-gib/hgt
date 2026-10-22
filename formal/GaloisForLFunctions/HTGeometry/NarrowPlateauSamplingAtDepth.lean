import GaloisForLFunctions.HTGeometry.ComplexLocalSamplingAtDepth

/-!
# Plateau cutoffs with a narrow collar, and the depth rate of the aperture

The trapezoidal cutoff `(2a)⁻¹(1_{[−a,a]} ⋆ 1_{[−2a,2a]})` is one on `[−a, a]` but supported in
`[−3a, 3a]`, so sampling a transform at depth `σ` through its kernel costs `e^{6πaσ}`: three times
the aperture of the source.  Keeping the two radii apart gives the cutoff

`T_{p,q} = (2q)⁻¹ (1_{[−q,q]} ⋆ 1_{[−p,p]})`,

one on the plateau `[−(p−q), p−q]` and supported in `[−(p+q), p+q]`.  At `p = a + δ`, `q = δ` the
plateau is exactly `[−a, a]` and the support radius is `a + 2δ`, so the depth costs only
`e^{2π(a+2δ)σ}` while the kernel constant grows like `δ⁻¹`.  Letting the collar `δ` shrink, the
sampling rate is the aperture of the source itself, not three times it; the constant pays for the
sharpening.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry.LocalSampling

noncomputable section
set_option autoImplicit false

/-! ## The two-radius trapezoid -/

/-- The convolution of two symmetric boxes is the length of the overlapping interval. -/
theorem convolution_boxFn_two (p q t : ℝ) :
    convolution (boxFn q) (boxFn p) (ContinuousLinearMap.mul ℂ ℂ) volume t =
      ((max 0 (min q (t + p) - max (-q) (t - p)) : ℝ) : ℂ) := by
  have hint : ∀ s : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (boxFn q s) (boxFn p (t - s)) =
      (Icc (max (-q) (t - p)) (min q (t + p))).indicator (fun _ => (1:ℂ)) s := by
    intro s
    rw [ContinuousLinearMap.mul_apply', boxFn_apply, boxFn_apply, Set.indicator_apply]
    by_cases h1 : s ∈ Icc (-q) q
    · rw [Set.mem_Icc] at h1
      by_cases h2 : t - s ∈ Icc (-(p)) (p)
      · rw [Set.mem_Icc] at h2
        have hmem : s ∈ Icc (max (-q) (t - p)) (min q (t + p)) := by
          rw [Set.mem_Icc, max_le_iff, le_min_iff]
          exact ⟨⟨h1.1, by linarith [h2.2]⟩, h1.2, by linarith [h2.1]⟩
        rw [if_pos (Set.mem_Icc.mpr h1), if_pos (Set.mem_Icc.mpr h2), if_pos hmem]
        norm_num
      · have hnot : s ∉ Icc (max (-q) (t - p)) (min q (t + p)) := by
          intro hc
          rw [Set.mem_Icc] at hc
          have hb1 : t - p ≤ s := le_trans (le_max_right _ _) hc.1
          have hb2 : s ≤ t + p := le_trans hc.2 (min_le_right _ _)
          exact h2 (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
        rw [if_pos (Set.mem_Icc.mpr h1), if_neg h2, if_neg hnot]
        norm_num
    · have hnot : s ∉ Icc (max (-q) (t - p)) (min q (t + p)) := by
        intro hc
        rw [Set.mem_Icc] at hc
        have hb1 : -q ≤ s := le_trans (le_max_left _ _) hc.1
        have hb2 : s ≤ q := le_trans hc.2 (min_le_left _ _)
        exact h1 (Set.mem_Icc.mpr ⟨hb1, hb2⟩)
      rw [if_neg h1, if_neg hnot]
      norm_num
  have hconv : convolution (boxFn q) (boxFn p) (ContinuousLinearMap.mul ℂ ℂ) volume t =
      ∫ s : ℝ, (Icc (max (-q) (t - p)) (min q (t + p))).indicator (fun _ => (1:ℂ)) s :=
    integral_congr_ae (Filter.Eventually.of_forall hint)
  have hvol : volume.real (Icc (max (-q) (t - p)) (min q (t + p))) =
      max 0 (min q (t + p) - max (-q) (t - p)) := by
    rw [MeasureTheory.Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal']
    exact max_comm _ _
  rw [hconv, MeasureTheory.integral_indicator_const (1:ℂ) measurableSet_Icc,
    Complex.real_smul, mul_one, hvol]


/-- The two-radius trapezoidal cutoff: one on `[−(p−q), p−q]`, supported in `[−(p+q), p+q]`. -/
def trapTwo (p q : ℝ) : ℝ → ℂ := fun t =>
  ((2 * q)⁻¹ : ℂ) * convolution (boxFn q) (boxFn p) (ContinuousLinearMap.mul ℂ ℂ) volume t

theorem trapTwo_eq (p q t : ℝ) :
    trapTwo p q t = (((2 * q)⁻¹ * max 0 (min q (t + p) - max (-q) (t - p)) : ℝ) : ℂ) := by
  rw [trapTwo, convolution_boxFn_two]
  push_cast
  ring

/-- The cutoff is one on the plateau. -/
theorem trapTwo_eq_one {p q : ℝ} (hq : 0 < q) {t : ℝ} (ht : |t| ≤ p - q) :
    trapTwo p q t = 1 := by
  rw [abs_le] at ht
  have h1 : min q (t + p) = q := min_eq_left (by linarith [ht.1])
  have h2 : max (-q) (t - p) = -q := max_eq_left (by linarith [ht.2])
  rw [trapTwo_eq, h1, h2, max_eq_right (by linarith)]
  have hval : ((2 * q)⁻¹ * (q - -q) : ℝ) = 1 := by
    rw [show q - -q = 2 * q by ring]
    field_simp
  rw [hval]
  norm_num

/-- The cutoff vanishes off the support interval. -/
theorem trapTwo_eq_zero {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) {t : ℝ} (ht : p + q < |t|) :
    trapTwo p q t = 0 := by
  rw [trapTwo_eq]
  rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
  · have h1 : min q (t + p) = q := min_eq_left (by rw [he] at ht; linarith)
    have h2 : max (-q) (t - p) = t - p := max_eq_right (by rw [he] at ht; linarith)
    rw [h1, h2, max_eq_left (by rw [he] at ht; linarith)]
    norm_num
  · have h1 : min q (t + p) = t + p := min_eq_right (by rw [he] at ht; linarith)
    have h2 : max (-q) (t - p) = -q := max_eq_left (by rw [he] at ht; linarith)
    rw [h1, h2, max_eq_left (by rw [he] at ht; linarith)]
    norm_num

theorem continuous_trapTwo (p q : ℝ) : Continuous (trapTwo p q) := by
  have hcont : Continuous fun t : ℝ =>
      ((2 * q)⁻¹ * max 0 (min q (t + p) - max (-q) (t - p)) : ℝ) :=
    continuous_const.mul ((continuous_const.max
      ((continuous_const.min (continuous_id.add continuous_const)).sub
        (continuous_const.max (continuous_id.sub continuous_const)))))
  exact Complex.continuous_ofReal.comp hcont |>.congr fun t => (trapTwo_eq p q t).symm

theorem hasCompactSupport_trapTwo {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    HasCompactSupport (trapTwo p q) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(p + q)) (b := p + q))
  intro t ht
  refine trapTwo_eq_zero hp hq ?_
  by_contra hcon
  exact ht (Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hcon)))

theorem integrable_trapTwo {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : Integrable (trapTwo p q) :=
  (continuous_trapTwo p q).integrable_of_hasCompactSupport (hasCompactSupport_trapTwo hp hq)

/-! ## Its kernel at a complex frequency -/

/-- The kernel of the two-radius cutoff at a complex frequency. -/
def kernelTwo (p q : ℝ) (w : ℂ) : ℂ := cutoffKernel (trapTwo p q) w

/-- **The complex-frequency product formula** for the two-radius cutoff: the kernel is the
product of the two box transforms, by Fubini on the convolution that defines the cutoff. -/
theorem kernelTwo_eq {p q : ℝ} (hp : 0 ≤ p) (ha : 0 < q) (w : ℂ) :
    kernelTwo p q w = ((2 * q)⁻¹ : ℂ) * (boxTransform q w * boxTransform p w) := by
  have hinner : ∀ s : ℝ, (∫ t : ℝ, boxFn p (t - s) * chi w t) =
      chi w s * boxTransform p w := by
    intro s
    have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => boxFn p (t - s) * chi w t) s
    rw [← hshift]
    have hcongr : ∀ u : ℝ, boxFn p (u + s - s) * chi w (u + s) =
        chi w s * (boxFn p u * chi w u) := by
      intro u
      rw [add_sub_cancel_right, chi_add]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_const_mul, boxTransform_eq_integral]
  have hprod : Integrable (Function.uncurry fun (t s : ℝ) =>
      boxFn q s * boxFn p (t - s) * chi w t) (volume.prod volume) := by
    have hmeas : Measurable (Function.uncurry fun (t s : ℝ) =>
        boxFn q s * boxFn p (t - s) * chi w t) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold boxFn
        exact (measurable_one.indicator measurableSet_Icc).comp measurable_snd
      · unfold boxFn
        exact (measurable_one.indicator measurableSet_Icc).comp
          (measurable_fst.sub measurable_snd)
      · exact ((Complex.continuous_exp.comp ((continuous_const.mul
          Complex.continuous_ofReal))).measurable).comp measurable_fst
    refine Integrable.mono' (g := fun z : ℝ × ℝ =>
      (Icc (-(p + q)) (p + q) ×ˢ Icc (-q) q).indicator
        (fun _ => Real.exp (2 * π * (p + q) * |w.im|)) z) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    · refine (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).2 ?_
      refine integrableOn_const (hs := ?_)
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
    · obtain ⟨t, s⟩ := z
      simp only [Function.uncurry_apply_pair, Set.indicator_apply]
      by_cases hz : (t, s) ∈ Icc (-(p + q)) (p + q) ×ˢ Icc (-q) q
      · rw [if_pos hz, norm_mul, norm_mul]
        have h1 : ‖boxFn q s‖ ≤ 1 := norm_boxFn_le q s
        have h2 : ‖boxFn p (t - s)‖ ≤ 1 := norm_boxFn_le _ _
        have h3 : ‖chi w t‖ ≤ Real.exp (2 * π * (p + q) * |w.im|) := by
          refine norm_chi_le (by linarith) w ?_
          rcases hz with ⟨hz1, _⟩
          rw [Set.mem_Icc] at hz1
          exact abs_le.mpr ⟨hz1.1, hz1.2⟩
        calc ‖boxFn q s‖ * ‖boxFn p (t - s)‖ * ‖chi w t‖
            ≤ 1 * 1 * Real.exp (2 * π * (p + q) * |w.im|) := by
              refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)) h3
                (norm_nonneg _) (by norm_num)
          _ = Real.exp (2 * π * (p + q) * |w.im|) := by ring
      · rw [if_neg hz]
        have hzero : boxFn q s * boxFn p (t - s) = 0 := by
          by_cases h2 : s ∈ Icc (-q) q
          · have h1 : t ∉ Icc (-(p + q)) (p + q) := by
              intro hc
              exact hz ⟨hc, h2⟩
            rw [Set.mem_Icc] at h2
            have : boxFn p (t - s) = 0 := by
              rw [boxFn_apply, if_neg]
              intro hc
              rw [Set.mem_Icc] at hc
              rw [Set.mem_Icc] at h1
              rcases not_and_or.mp h1 with h | h
              · have hlt : t < -(p + q) := not_le.mp h
                linarith [hc.1, h2.2]
              · have hlt : p + q < t := not_le.mp h
                linarith [hc.2, h2.1]
            rw [this, mul_zero]
          · have : boxFn q s = 0 := by rw [boxFn_apply, if_neg h2]
            rw [this, zero_mul]
        rw [hzero, zero_mul, norm_zero]
  have hswap := MeasureTheory.integral_integral_swap hprod
  have houter : (∫ t : ℝ, trapTwo p q t * chi w t) =
      ((2 * q)⁻¹ : ℂ) * ∫ t : ℝ, ∫ s : ℝ, boxFn q s * boxFn p (t - s) * chi w t := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [trapTwo, convolution, ContinuousLinearMap.mul_apply']
    rw [MeasureTheory.integral_mul_const, mul_assoc]
  simp only [kernelTwo, cutoffKernel]
  rw [houter, hswap]
  have hinner2 : ∀ s : ℝ, (∫ t : ℝ, boxFn q s * boxFn p (t - s) * chi w t) =
      boxFn q s * chi w s * boxTransform p w := by
    intro s
    have hc : ∀ t : ℝ, boxFn q s * boxFn p (t - s) * chi w t =
        boxFn q s * (boxFn p (t - s) * chi w t) := by
      intro t; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hc),
      MeasureTheory.integral_const_mul, hinner s]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner2)]
  have hfin : (∫ s : ℝ, boxFn q s * chi w s * boxTransform p w) =
      boxTransform q w * boxTransform p w := by
    rw [MeasureTheory.integral_mul_const, ← boxTransform_eq_integral]
  rw [hfin]

/-- **The kernel at depth, with the support radius as the rate.**  Quadratic decay in the real
direction is kept; the depth costs `e^{2π(p+q)|Im w|}`, the support radius of the cutoff. -/
theorem norm_kernelTwo_le {p q : ℝ} (hp : 0 < p) (ha : 0 < q) (w : ℂ) :
    ‖kernelTwo p q w‖ ≤
      Real.exp (2 * π * (p + q) * |w.im|) * ((4 * p + q⁻¹) / (1 + w.re ^ 2)) := by
  have ha2 : (0:ℝ) < p := hp
  have hq0 : q ≠ 0 := ne_of_gt ha
  have hE : (0:ℝ) < Real.exp (2 * π * (p + q) * |w.im|) := Real.exp_pos _
  have hden : (0:ℝ) < 1 + w.re ^ 2 := by positivity
  rw [kernelTwo_eq hp.le ha, norm_mul, norm_mul]
  have hc : ‖((2 * q)⁻¹ : ℂ)‖ = (2 * q)⁻¹ := by
    rw [show ((2 * q)⁻¹ : ℂ) = (((2 * q)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hexp1 : Real.exp (2 * π * q * |w.im|) * Real.exp (2 * π * p * |w.im|) =
      Real.exp (2 * π * (p + q) * |w.im|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rcases le_or_gt |w.re| 1 with hre | hre
  · have h1 : ‖boxTransform q w‖ ≤ 2 * q * Real.exp (2 * π * q * |w.im|) :=
      norm_boxTransform_le_two_mul ha.le w
    have h2 : ‖boxTransform p w‖ ≤ 2 * p * Real.exp (2 * π * p * |w.im|) :=
      norm_boxTransform_le_two_mul ha2.le w
    have hmul : ‖boxTransform q w‖ * ‖boxTransform p w‖ ≤
        (2 * q * Real.exp (2 * π * q * |w.im|)) *
          (2 * p * Real.exp (2 * π * p * |w.im|)) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have hstep : (2 * q)⁻¹ * (‖boxTransform q w‖ * ‖boxTransform p w‖) ≤
        2 * p * Real.exp (2 * π * (p + q) * |w.im|) := by
      calc (2 * q)⁻¹ * (‖boxTransform q w‖ * ‖boxTransform p w‖)
          ≤ (2 * q)⁻¹ * ((2 * q * Real.exp (2 * π * q * |w.im|)) *
              (2 * p * Real.exp (2 * π * p * |w.im|))) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 2 * p * (Real.exp (2 * π * q * |w.im|) *
              Real.exp (2 * π * p * |w.im|)) := by field_simp
        _ = 2 * p * Real.exp (2 * π * (p + q) * |w.im|) := by rw [hexp1]
    refine hstep.trans ?_
    have hsq : w.re ^ 2 ≤ 1 := by nlinarith [sq_abs w.re, abs_nonneg w.re]
    have h4a : 2 * p ≤ (4 * p + q⁻¹) / (1 + w.re ^ 2) := by
      rw [le_div_iff₀ hden]
      nlinarith [hsq, hp, ha, inv_pos.mpr ha]
    calc 2 * p * Real.exp (2 * π * (p + q) * |w.im|)
        = Real.exp (2 * π * (p + q) * |w.im|) * (2 * p) := by ring
      _ ≤ Real.exp (2 * π * (p + q) * |w.im|) * ((4 * p + q⁻¹) / (1 + w.re ^ 2)) :=
          mul_le_mul_of_nonneg_left h4a hE.le
  · have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hre
      simp at hre
      linarith
    have hwpos : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
    have h1 : ‖boxTransform q w‖ ≤ (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * q * |w.im|)) :=
      norm_boxTransform_le_inv ha.le hw0
    have h2 : ‖boxTransform p w‖ ≤
        (π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * p * |w.im|)) :=
      norm_boxTransform_le_inv ha2.le hw0
    have hmul : ‖boxTransform q w‖ * ‖boxTransform p w‖ ≤
        ((π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * q * |w.im|))) *
          ((π * ‖w‖)⁻¹ * (2 * Real.exp (2 * π * p * |w.im|))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    have hstep : (2 * q)⁻¹ * (‖boxTransform q w‖ * ‖boxTransform p w‖) ≤
        Real.exp (2 * π * (p + q) * |w.im|) * (2 / (q * π ^ 2 * ‖w‖ ^ 2)) := by
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
    have hX : (0:ℝ) < q * π ^ 2 * ‖w‖ ^ 2 := by positivity
    rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hX]
    have hinv : q⁻¹ * (q * π ^ 2 * ‖w‖ ^ 2) = π ^ 2 * ‖w‖ ^ 2 := by field_simp
    have h8 : (0:ℝ) ≤ 4 * p * (q * π ^ 2 * ‖w‖ ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    have hexpand : (4 * p + q⁻¹) * (q * π ^ 2 * ‖w‖ ^ 2) =
        4 * p * (q * π ^ 2 * ‖w‖ ^ 2) + q⁻¹ * (q * π ^ 2 * ‖w‖ ^ 2) := by ring
    have hbig : π ^ 2 * ‖w‖ ^ 2 ≤ (4 * p + q⁻¹) * (q * π ^ 2 * ‖w‖ ^ 2) := by
      rw [hexpand, hinv]
      linarith
    have hfinal : 9 * w.re ^ 2 ≤ π ^ 2 * ‖w‖ ^ 2 := by
      nlinarith [hpi2, hnormsq, sq_nonneg w.re, norm_nonneg w]
    nlinarith [hbig, hfinal, hre2]


/-! ## Sampling at the rate of the support radius -/

theorem measurable_kernelTwo_sub (p q : ℝ) (z : ℂ) :
    Measurable fun y : ℝ => kernelTwo p q (z - (y : ℂ)) := by
  have hjoint : Continuous
      (Function.uncurry fun (y t : ℝ) => trapTwo p q t * chi (z - (y : ℂ)) t) := by
    refine Continuous.mul ((continuous_trapTwo p q).comp continuous_snd) ?_
    refine Complex.continuous_exp.comp ?_
    exact ((continuous_const.mul (continuous_const.sub
      (Complex.continuous_ofReal.comp continuous_fst))).mul
      (Complex.continuous_ofReal.comp continuous_snd))
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The reproducing identity through the two-radius cutoff: the plateau covers the support. -/
theorem fourierAt_eq_integral_kernelTwo {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) {f : ℝ → ℂ}
    (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, p - q < |t| → f t = 0) (z : ℂ) :
    fourierAt f z = ∫ y : ℝ, 𝓕 f y * kernelTwo p q (z - (y : ℂ)) :=
  fourierAt_eq_integral_of_cutoff (a := p - q) (R := p + q) (by linarith)
    (continuous_trapTwo p q) (integrable_trapTwo hp hq)
    (fun _ ht => trapTwo_eq_one hq ht) (fun _ ht => trapTwo_eq_zero hp hq ht)
    hfc hf hFi hsupp z

/-- **Sampling at depth with the support radius as the rate.**  The two-radius cutoff samples a
transform of a source supported in `[−(p−q), p−q]` at complex points of depth at most `σ`, paying
`e^{2π(p+q)σ}` for the depth and `4p + q⁻¹` for the kernel. -/
theorem sum_norm_sq_fourierAt_le_two {p q B σ : ℝ} (hp : 0 < p) (hq : 0 < q) (hB : 0 ≤ B)
    (hσ : 0 ≤ σ) {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, p - q < |t| → f t = 0)
    (φ : ℝ → ℝ) (hφ : ∀ y : ℝ, 0 ≤ φ y)
    (hΦ2 : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * φ y)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (pt : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ i ∈ S, |(pt i).im| ≤ σ) (hm : ∀ i, 0 ≤ m i)
    (hker : ∀ y : ℝ, (∑ i ∈ S, m i * (1 + ((pt i).re - y) ^ 2)⁻¹) ≤ B * φ y) :
    ∑ i ∈ S, m i * ‖fourierAt f (pt i)‖ ^ 2 ≤
      ((Real.exp (2 * π * (p + q) * σ) * ((4 * p + q⁻¹) * π)) *
        (Real.exp (2 * π * (p + q) * σ) * ((4 * p + q⁻¹) * B))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * φ y :=
  sum_norm_sq_fourierAt_le_of_kernel (R := p + q) (C := 4 * p + q⁻¹)
    (by linarith) (by have := inv_pos.mpr hq; linarith) hB hσ hf (kernelTwo p q)
    (fun w => norm_kernelTwo_le hp hq w)
    (fun z => measurable_kernelTwo_sub p q z)
    (fun z => fourierAt_eq_integral_kernelTwo hp.le hq hfc hf hFi hsupp z)
    φ hφ hΦ2 hint S pt m hSim hm hker

/-- **Sampling at depth against a logarithmic density, at the rate of the aperture.**  For a source
supported in `[−a, a]` and any collar `δ > 0`, the depth costs `e^{2π(a+2δ)σ}`: the rate is the
aperture of the source up to the collar, and the collar is paid for by the constant `δ⁻¹`. -/
theorem sum_norm_sq_fourierAt_le_collar {a δ A₀ σ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA₀ : 0 ≤ A₀)
    (hσ : 0 ≤ σ) {f : ℝ → ℂ} (hfc : Continuous f) (hf : Integrable f) (hFi : Integrable (𝓕 f))
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0)
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3))
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (pt : ι → ℂ) (m : ι → ℝ)
    (hSim : ∀ i ∈ S, |(pt i).im| ≤ σ) (hm : ∀ i, 0 ≤ m i)
    (hcount : ∀ n : ℤ,
      (∑ i ∈ S.filter fun i => (n : ℝ) ≤ (pt i).re ∧ (pt i).re ≤ (n : ℝ) + 1, m i) ≤
      A₀ * Real.log (|(n : ℝ)| + 3)) :
    ∑ i ∈ S, m i * ‖fourierAt f (pt i)‖ ^ 2 ≤
      ((Real.exp (2 * π * (a + 2 * δ) * σ) * ((4 * (a + δ) + δ⁻¹) * π)) *
        (Real.exp (2 * π * (a + 2 * δ) * σ) *
          ((4 * (a + δ) + δ⁻¹) * (3 * A₀ * logKernelConst)))) *
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
  have hsupp' : ∀ t : ℝ, (a + δ) - δ < |t| → f t = 0 := by
    intro t ht
    exact hsupp t (by linarith)
  have hconc := sum_norm_sq_fourierAt_le_two (p := a + δ) (q := δ) (by linarith) hδ
    (by have := logKernelConst_nonneg; positivity) hσ hfc hf hFi hsupp'
    (fun y => Real.log (|y| + 3)) (fun y => by linarith [hlog1 y]) hΦ2 hint S pt m hSim hm
    (fun y => sum_kernel_le hA₀ S (fun i => (pt i).re) m hm hcount y)
  have hrad : a + δ + δ = a + 2 * δ := by ring
  rwa [hrad] at hconc

end

end GaloisForLFunctions.HTGeometry.LocalSampling
