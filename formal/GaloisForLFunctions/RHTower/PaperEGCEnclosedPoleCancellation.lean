import GaloisForLFunctions.RHTower.PaperEGCSourceLanding
import GaloisForLFunctions.RHTower.RectanglePoleWeightedLogDeriv

/-!
# Exact enclosed-pole cancellation in the EGC source contour

When both prescribed poles enter the contour, the finite pair row must be supplemented by
the complete source difference. Their enclosed-copy contributions cancel exactly to unit
mass. The remaining defect is the exterior-copy correction, uniformly small along cofinal
source rectangles. This is an inner contour law; it does not provide the outer covariance sign.
-/

open Complex Filter Set intervalIntegral
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- A positively oriented rectangle on which the literal continued source is admissible. -/
structure PaperEGCSourceRectangle where
  lower : ℂ
  upper : ℂ
  re_lt : lower.re < upper.re
  im_lt : lower.im < upper.im
  bottom : ∀ x ∈ uIcc lower.re upper.re,
    XiExplicitAdmissible ((x : ℂ) + lower.im * I)
  top : ∀ x ∈ uIcc lower.re upper.re,
    XiExplicitAdmissible ((x : ℂ) + upper.im * I)
  right : ∀ y ∈ uIcc lower.im upper.im,
    XiExplicitAdmissible ((upper.re : ℂ) + y * I)
  left : ∀ y ∈ uIcc lower.im upper.im,
    XiExplicitAdmissible ((lower.re : ℂ) + y * I)

namespace PaperEGCSourceRectangle

/-- Strict interior, used only for the geometric location of prescribed poles. -/
def Inside (R : PaperEGCSourceRectangle) (z : ℂ) : Prop :=
  R.lower.re < z.re ∧ z.re < R.upper.re ∧ R.lower.im < z.im ∧ z.im < R.upper.im

private theorem zeros_inside (R : PaperEGCSourceRectangle) :
    ∀ z ∈ xiCClosedRectangleZeros R.lower R.upper, R.Inside z := by
  intro z hz
  obtain ⟨hzK, hz0⟩ := mem_xiCClosedRectangleZeros.mp hz
  obtain ⟨hr, hi⟩ := Complex.mem_reProdIm.mp hzK
  have hr' := hr
  have hi' := hi
  rw [uIcc_of_le R.re_lt.le] at hr'
  rw [uIcc_of_le R.im_lt.le] at hi'
  have hleft : z.re ≠ R.lower.re := by
    intro he
    have h := XiC_ne_zero_of_admissible (R.left z.im hi)
    apply h
    convert hz0 using 1
    apply congrArg XiC
    apply Complex.ext <;> simp [he]
  have hright : z.re ≠ R.upper.re := by
    intro he
    have h := XiC_ne_zero_of_admissible (R.right z.im hi)
    apply h
    convert hz0 using 1
    apply congrArg XiC
    apply Complex.ext <;> simp [he]
  have hbottom : z.im ≠ R.lower.im := by
    intro he
    have h := XiC_ne_zero_of_admissible (R.bottom z.re hr)
    apply h
    convert hz0 using 1
    apply congrArg XiC
    apply Complex.ext <;> simp [he]
  have htop : z.im ≠ R.upper.im := by
    intro he
    have h := XiC_ne_zero_of_admissible (R.top z.re hr)
    apply h
    convert hz0 using 1
    apply congrArg XiC
    apply Complex.ext <;> simp [he]
  exact ⟨lt_of_le_of_ne hr'.1 hleft.symm, lt_of_le_of_ne hr'.2 hright,
    lt_of_le_of_ne hi'.1 hbottom.symm, lt_of_le_of_ne hi'.2 htop⟩

private theorem source_eq_log (R : PaperEGCSourceRectangle) (g : ℂ → ℂ) :
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) R.lower R.upper =
      rectIntegral (fun z => g z * logDeriv XiC z) R.lower R.upper := by
  apply rectIntegral_congr (S := {z | XiExplicitAdmissible z})
    (fun z hz => congrArg (g z * ·)
      (continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC hz))
    R.bottom R.top R.right R.left

private theorem order_sum (R : PaperEGCSourceRectangle) (g : ℂ → ℂ) :
    (∑ z ∈ xiCClosedRectangleZeros R.lower R.upper,
      ((analyticOrderAt XiC z).toNat : ℂ) * g z) =
      ∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper, g (xiSpectralPoint a) := by
  rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat (mem_xiCClosedRectangleZeros.mp hz).2]

private theorem log_cauchy (R : PaperEGCSourceRectangle) {p : ℂ}
    (hp : R.Inside p) (hp0 : XiC p ≠ 0) :
    rectIntegral (fun z => (z - p)⁻¹ * logDeriv XiC z) R.lower R.upper =
      2 * Real.pi * I *
        ((∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper,
          (xiSpectralPoint a - p)⁻¹) + logDeriv XiC p) := by
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization R.lower R.upper
  let U : Set ℂ := {z | h z ≠ 0}
  have hres := rectIntegral_mul_inv_sub_mul_logDeriv_multi_zero
    (xiCClosedRectangleZeros R.lower R.upper) (fun z => z) m
    (φ := fun _ => 1) (U := U) analyticOnNhd_const R.zeros_inside hp
    (fun z hz he => hp0 (he ▸ (mem_xiCClosedRectangleZeros.mp hz).2))
    hhK (hhan.mono (subset_univ U)) (fun _ hz => hz)
  rw [← funext hfact] at hres
  simp only [one_mul] at hres
  rw [hres]
  congr 2
  rw [← R.order_sum (fun z => (z - p)⁻¹)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hm z hz]

/-- Both shifted poles contribute their literal source values, with their forced signs. -/
theorem enclosed_poles (R : PaperEGCSourceRectangle) (eps : ℝ) (w : ℂ)
    (hp : R.Inside (w + (eps : ℂ))) (hm : R.Inside (w - (eps : ℂ)))
    (hp0 : XiC (w + (eps : ℂ)) ≠ 0) (hm0 : XiC (w - (eps : ℂ)) ≠ 0) :
    normalizedMeromorphicCauchyPairInnerSourceContour eps w R.lower R.upper =
      (∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper,
        meromorphicCauchyPairKernel eps (xiSpectralPoint a) w) +
      (eps / 2 : ℂ) * (logDeriv XiC (w + (eps : ℂ)) -
        logDeriv XiC (w - (eps : ℂ))) := by
  let p := w + (eps : ℂ)
  let q := w - (eps : ℂ)
  let L := logDeriv XiC
  let P : ℂ → ℂ := fun z => (eps / 2 : ℂ) * ((z - p)⁻¹ * L z)
  let Q : ℂ → ℂ := fun z => -(eps / 2 : ℂ) * ((z - q)⁻¹ * L z)
  let S : Set ℂ := {z | XiExplicitAdmissible z ∧ z ≠ p ∧ z ≠ q}
  have hb : ∀ x ∈ uIcc R.lower.re R.upper.re,
      ((x : ℂ) + R.lower.im * I) ∈ S := by
    intro x hx
    refine ⟨R.bottom x hx, ?_, ?_⟩ <;> intro he
    · have := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at this
      exact (ne_of_lt hp.2.2.1) this
    · have := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at this
      exact (ne_of_lt hm.2.2.1) this
  have ht : ∀ x ∈ uIcc R.lower.re R.upper.re,
      ((x : ℂ) + R.upper.im * I) ∈ S := by
    intro x hx
    refine ⟨R.top x hx, ?_, ?_⟩ <;> intro he
    · have := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at this
      exact (ne_of_lt hp.2.2.2) this.symm
    · have := congrArg Complex.im he
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add] at this
      exact (ne_of_lt hm.2.2.2) this.symm
  have hr : ∀ y ∈ uIcc R.lower.im R.upper.im,
      ((R.upper.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨R.right y hy, ?_, ?_⟩ <;> intro he
    · have := congrArg Complex.re he
      simp only [add_re, ofReal_im, mul_re, ofReal_re, I_im, I_re,
        mul_one, mul_zero, sub_zero, add_zero] at this
      exact (ne_of_lt hp.2.1) this.symm
    · have := congrArg Complex.re he
      simp only [add_re, ofReal_im, mul_re, ofReal_re, I_im, I_re,
        mul_one, mul_zero, sub_zero, add_zero] at this
      exact (ne_of_lt hm.2.1) this.symm
  have hl : ∀ y ∈ uIcc R.lower.im R.upper.im,
      ((R.lower.re : ℂ) + y * I) ∈ S := by
    intro y hy
    refine ⟨R.left y hy, ?_, ?_⟩ <;> intro he
    · have := congrArg Complex.re he
      simp only [add_re, ofReal_im, mul_re, ofReal_re, I_im, I_re,
        mul_one, mul_zero, sub_zero, add_zero] at this
      exact (ne_of_lt hp.1) this
    · have := congrArg Complex.re he
      simp only [add_re, ofReal_im, mul_re, ofReal_re, I_im, I_re,
        mul_one, mul_zero, sub_zero, add_zero] at this
      exact (ne_of_lt hm.1) this
  have hL : ContinuousOn L S := by
    intro z hz
    exact (((XiC_analytic.deriv z (mem_univ z)).div (XiC_analytic z (mem_univ z))
      (XiC_ne_zero_of_admissible hz.1)).continuousAt).continuousWithinAt
  have hP : ContinuousOn P S := continuousOn_const.mul
    (((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr hz.2.1)).mul hL)
  have hQ : ContinuousOn Q S := continuousOn_const.mul
    (((continuousOn_id.sub continuousOn_const).inv₀
      (fun z hz => sub_ne_zero.mpr hz.2.2)).mul hL)
  have II {a b : ℝ} (pt : ℝ → ℂ) (hpt : Continuous pt)
      (hS : ∀ u ∈ uIcc a b, pt u ∈ S) {f : ℂ → ℂ} (hf : ContinuousOn f S) :
      IntervalIntegrable (fun u => f (pt u)) MeasureTheory.volume a b :=
    (hf.comp hpt.continuousOn hS).intervalIntegrable
  have hdecomp : ∀ z ∈ S, meromorphicCauchyPairKernel eps z w * L z =
      (L z + P z) + Q z := by
    intro z hz
    have hzP : z - w - (eps : ℂ) ≠ 0 := by
      simpa only [p, sub_add_eq_sub_sub] using sub_ne_zero.mpr hz.2.1
    have hzQ : z - w + (eps : ℂ) ≠ 0 := by
      rw [show z - w + (eps : ℂ) = z - q by dsimp only [q]; ring]
      exact sub_ne_zero.mpr hz.2.2
    rw [meromorphicCauchyPairKernel_eq_resolventDifference eps z w hzP hzQ]
    dsimp only [P, Q, p, q]
    rw [sub_add_eq_sub_sub, show z - (w - (eps : ℂ)) = z - w + (eps : ℂ) by ring]
    ring
  have h0 : rectIntegral L R.lower R.upper =
      2 * Real.pi * I * ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ) := by
    have h := rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (g := fun _ => 1) analyticOnNhd_const R.re_lt R.im_lt R.bottom R.top R.right R.left
    rw [R.source_eq_log] at h
    simpa only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have hPint := R.log_cauchy hp hp0
  have hQint := R.log_cauchy hm hm0
  have hpair : ∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper,
      meromorphicCauchyPairKernel eps (xiSpectralPoint a) w =
        ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ) +
          (eps / 2 : ℂ) * ((∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper,
            (xiSpectralPoint a - p)⁻¹) -
            ∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper, (xiSpectralPoint a - q)⁻¹) := by
    have hreg (a : XiZeroCopy) (z : ℂ) (hz : XiC z ≠ 0) : xiSpectralPoint a ≠ z :=
      fun he => hz (he ▸ XiC_xiSpectralPoint_eq_zero a)
    calc
      _ = ∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper,
          (1 + (eps / 2 : ℂ) * ((xiSpectralPoint a - p)⁻¹ -
            (xiSpectralPoint a - q)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro a _
        simpa only [p, q, sub_add_eq_sub_sub,
          show xiSpectralPoint a - (w - (eps : ℂ)) =
            xiSpectralPoint a - w + (eps : ℂ) by ring] using
          meromorphicCauchyPairKernel_eq_resolventDifference eps (xiSpectralPoint a) w
            (by simpa only [sub_add_eq_sub_sub] using sub_ne_zero.mpr (hreg a _ hp0))
            (by
              rw [show xiSpectralPoint a - w + (eps : ℂ) =
                xiSpectralPoint a - (w - (eps : ℂ)) by ring]
              exact sub_ne_zero.mpr (hreg a _ hm0))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]; simp
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [normalizedMeromorphicCauchyPairInnerSourceContour, R.source_eq_log,
    rectIntegral_congr hdecomp hb ht hr hl,
    rectIntegral_add (g₁ := fun z => L z + P z) (g₂ := Q)
      (II _ (by fun_prop) hb (hL.add hP)) (II _ (by fun_prop) hb hQ)
      (II _ (by fun_prop) ht (hL.add hP)) (II _ (by fun_prop) ht hQ)
      (II _ (by fun_prop) hr (hL.add hP)) (II _ (by fun_prop) hr hQ)
      (II _ (by fun_prop) hl (hL.add hP)) (II _ (by fun_prop) hl hQ),
    rectIntegral_add (II _ (by fun_prop) hb hL) (II _ (by fun_prop) hb hP)
      (II _ (by fun_prop) ht hL) (II _ (by fun_prop) ht hP)
      (II _ (by fun_prop) hr hL) (II _ (by fun_prop) hr hP)
      (II _ (by fun_prop) hl hL) (II _ (by fun_prop) hl hP)]
  dsimp only [P, Q, L, p, q]
  rw [rectIntegral_const_mul, rectIntegral_const_mul, hPint, hQint, h0, hpair]
  dsimp only [p, q]
  field_simp
  ring

private theorem shifted_regular (eps x : PaperEGCSmallParameter) (t : ℝ) :
    XiC ((((x : ℝ) : ℂ) + (t : ℂ) * I) + ((eps : ℝ) : ℂ)) ≠ 0 ∧
      XiC ((((x : ℝ) : ℂ) + (t : ℂ) * I) - ((eps : ℝ) : ℂ)) ≠ 0 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h
    apply paperEGC_line_minus_ne_zero eps x t a
    rw [ha]
    ring
  · intro h
    obtain ⟨a, ha⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp h
    apply paperEGC_line_plus_ne_zero eps x t a
    rw [ha]
    ring

/-- Exact contour defect: only the full exterior-copy correction survives after unit mass. -/
theorem enclosed_poles_eq_count_add_tail (R : PaperEGCSourceRectangle)
    (eps x : PaperEGCSmallParameter) (t : ℝ)
    (hp : R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) + ((eps : ℝ) : ℂ)))
    (hm : R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) - ((eps : ℝ) : ℂ))) :
    normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ)
        (((x : ℝ) : ℂ) + (t : ℂ) * I) R.lower R.upper =
      ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ) +
        paperEGCCompleteCorrection eps x t -
        ∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper, paperEGCLineCopy eps x t a := by
  have hreg := shifted_regular eps x t
  rw [R.enclosed_poles _ _ hp hm hreg.1 hreg.2,
    ← paperEGCCompleteCorrection_eq_logDeriv]
  have hterm (a : XiZeroCopy) :
      meromorphicCauchyPairKernel (eps : ℝ) (xiSpectralPoint a)
          (((x : ℝ) : ℂ) + (t : ℂ) * I) = 1 - paperEGCLineCopy eps x t a := by
    have hp' := paperEGC_line_minus_ne_zero eps x t a
    have hm' := paperEGC_line_plus_ne_zero eps x t a
    have hd : (xiSpectralPoint a - (((x : ℝ) : ℂ) + (t : ℂ) * I))^2 -
        ((eps : ℝ) : ℂ)^2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hm' hp'
    rw [paperEGCLineCopy, meromorphicCauchyPairShiftResidueCorrection_eq_negative_square_div
      _ _ _ hp' hm', meromorphicCauchyPairKernel]
    field_simp
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- The defect is literally the absolutely summable row of all exterior multiplicity copies. -/
theorem enclosed_poles_eq_count_add_exterior (R : PaperEGCSourceRectangle)
    (eps x : PaperEGCSmallParameter) (t : ℝ)
    (hp : R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) + ((eps : ℝ) : ℂ)))
    (hm : R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) - ((eps : ℝ) : ℂ))) :
    normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ)
        (((x : ℝ) : ℂ) + (t : ℂ) * I) R.lower R.upper =
      ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ) +
        ∑' a : {a : XiZeroCopy // a ∉ xiZeroCopyClosedRectangle R.lower R.upper},
          paperEGCLineCopy eps x t a.1 := by
  have hs := (summable_norm_paperEGCLineCopy eps x t).of_norm.sum_add_tsum_compl
    (s := xiZeroCopyClosedRectangle R.lower R.upper)
  change (∑ a ∈ xiZeroCopyClosedRectangle R.lower R.upper, paperEGCLineCopy eps x t a) +
    (∑' a : {a : XiZeroCopy // a ∉ xiZeroCopyClosedRectangle R.lower R.upper},
      paperEGCLineCopy eps x t a.1) = ∑' a : XiZeroCopy, paperEGCLineCopy eps x t a at hs
  rw [R.enclosed_poles_eq_count_add_tail eps x t hp hm, paperEGCCompleteCorrection, ← hs]
  ring

/-- One finite cutoff controls every admissible contour containing it, simultaneously for all
small shifts, small real offsets, and every height at which both poles are enclosed. -/
theorem exists_uniform_contour_cutoff (n : ℕ) :
    ∃ F : Finset XiZeroCopy, ∀ R : PaperEGCSourceRectangle,
      F ⊆ xiZeroCopyClosedRectangle R.lower R.upper →
      ∀ (eps x : PaperEGCSmallParameter) (t : ℝ),
        R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) + ((eps : ℝ) : ℂ)) →
        R.Inside ((((x : ℝ) : ℂ) + (t : ℂ) * I) - ((eps : ℝ) : ℂ)) →
        ‖normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ)
            (((x : ℝ) : ℂ) + (t : ℂ) * I) R.lower R.upper -
          ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ)‖ < 1 / ((n : ℝ) + 1) := by
  have h := Metric.tendstoUniformly_iff.mp tendstoUniformly_paperEGCCompleteCorrection
    (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨F, hF⟩ := eventually_atTop.mp h
  refine ⟨F, fun R hR eps x t hp hm => ?_⟩
  have hnear := hF (xiZeroCopyClosedRectangle R.lower R.upper) hR (eps, x, t)
  rw [R.enclosed_poles_eq_count_add_tail eps x t hp hm]
  convert hnear using 1
  rw [dist_eq_norm]
  congr 1
  ring

/-- Source-admissible rectangles are cofinal and can simultaneously enclose every centered
prescribed pole, without an assumption about the location of any Xi zero. -/
theorem exists_containing_centered_window (F : Finset XiZeroCopy) :
    ∃ R : PaperEGCSourceRectangle,
      F ⊆ xiZeroCopyClosedRectangle R.lower R.upper ∧
      ∀ u ∈ Icc (-2 : ℝ) 2, R.Inside (u : ℂ) := by
  classical
  obtain ⟨a⟩ := exists_xiZeroCopy
  let S := F ∪ {a, xiZeroCopyReflectEquiv a}
  obtain ⟨l, r, hre, him, hpacket, hb, ht, hr, hl⟩ :=
    exists_admissible_rectangle_containing_xiZeroCopy_finset S
  let R : PaperEGCSourceRectangle := ⟨l, r, hre, him, hb, ht, hr, hl⟩
  have ha := hpacket a (by simp [S])
  have ha' := hpacket (xiZeroCopyReflectEquiv a) (by simp [S])
  rw [xiSpectralPoint_reflect, neg_re, neg_im] at ha'
  have hgap := xiSpectral_re_sq_gt_thirtytwo a
  have hleft : l.re < -2 := by
    rcases le_total 0 (xiSpectralPoint a).re with h | h
    · have : 2 < (xiSpectralPoint a).re := by nlinarith
      linarith [ha'.1]
    · have : (xiSpectralPoint a).re < -2 := by nlinarith
      linarith [ha.1]
  have hright : 2 < r.re := by
    rcases le_total 0 (xiSpectralPoint a).re with h | h
    · have : 2 < (xiSpectralPoint a).re := by nlinarith
      linarith [ha.2.1]
    · have : (xiSpectralPoint a).re < -2 := by nlinarith
      linarith [ha'.2.1]
  refine ⟨R, ?_, ?_⟩
  · intro b hbF
    have hbS := hpacket b (Finset.mem_union.mpr (Or.inl hbF))
    rw [mem_xiZeroCopyClosedRectangle, Complex.mem_reProdIm, uIcc_of_le hre.le,
      uIcc_of_le him.le]
    exact ⟨⟨hbS.1.le, hbS.2.1.le⟩, ⟨hbS.2.2.1.le, hbS.2.2.2.le⟩⟩
  · intro u hu
    change l.re < (u : ℂ).re ∧ (u : ℂ).re < r.re ∧
      l.im < (u : ℂ).im ∧ (u : ℂ).im < r.im
    simp only [ofReal_re, ofReal_im]
    exact ⟨hleft.trans_le hu.1, hu.2.trans_lt hright,
      by linarith [ha.2.2.1, ha'.2.2.1], by linarith [ha.2.2.2, ha'.2.2.2]⟩

/-- Unconditional cofinal realization of the uniformly vanishing, mass-subtracted source
contour. The source integral retains every copy and both prescribed residues. -/
theorem exists_uniform_centered_source_contour (n : ℕ) (F : Finset XiZeroCopy) :
    ∃ R : PaperEGCSourceRectangle,
      F ⊆ xiZeroCopyClosedRectangle R.lower R.upper ∧
      (∀ u ∈ Icc (-2 : ℝ) 2, R.Inside (u : ℂ)) ∧
      ∀ eps x : PaperEGCSmallParameter,
        ‖normalizedMeromorphicCauchyPairInnerSourceContour (eps : ℝ) ((x : ℝ) : ℂ)
            R.lower R.upper - ((xiZeroCopyClosedRectangle R.lower R.upper).card : ℂ)‖ <
          1 / ((n : ℝ) + 1) := by
  obtain ⟨G, hG⟩ := exists_uniform_contour_cutoff n
  obtain ⟨R, hR, hwindow⟩ := exists_containing_centered_window (F ∪ G)
  refine ⟨R, fun a ha => hR (Finset.mem_union.mpr (Or.inl ha)), hwindow, ?_⟩
  intro eps x
  have hp : R.Inside (((x : ℝ) : ℂ) + ((eps : ℝ) : ℂ)) := by
    rw [← ofReal_add]
    exact hwindow _ ⟨by linarith [x.2.1, eps.2.1], by linarith [x.2.2, eps.2.2]⟩
  have hm : R.Inside (((x : ℝ) : ℂ) - ((eps : ℝ) : ℂ)) := by
    rw [← ofReal_sub]
    exact hwindow _ ⟨by linarith [x.2.1, eps.2.2], by linarith [x.2.2, eps.2.1]⟩
  simpa only [ofReal_zero, zero_mul, add_zero] using
    hG R (fun a ha => hR (Finset.mem_union.mpr (Or.inr ha))) eps x 0
      (by simpa only [ofReal_zero, zero_mul, add_zero] using hp)
      (by simpa only [ofReal_zero, zero_mul, add_zero] using hm)

end PaperEGCSourceRectangle
end
end RHTower
