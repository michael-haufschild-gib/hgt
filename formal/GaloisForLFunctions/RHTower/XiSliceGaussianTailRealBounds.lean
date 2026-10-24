import GaloisForLFunctions.RHTower.XiSliceGaussianTailCompensation
import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPrimeSummability
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCone

/-!
# Global real-axis Gaussian control of Xi tails

Outside the distance cutoff, each reciprocal square lies in a narrow positive
cone. Scalar exponential bounds and reflection pairing bracket the real tail
between two Gaussians and bound its relative error by the fourth moment times
`x⁴` on the whole real axis. Multiplication by the finite head gives the same
global comparison for the actual normalized Xi slice.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

private theorem gaussian_real_reciprocal_cone (t : ℝ) {R : ℝ} (hR : 4 ≤ R)
    (q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R}) :
    3 / 4 * ‖xiSliceGaussianReciprocal t q‖ ≤ (xiSliceGaussianReciprocal t q).re := by
  let z := xiSpectralPoint q - (t : ℂ)
  have hdR : R < ‖z‖ := lt_of_not_ge (fun h =>
    q.property ((mem_xiSliceGaussianRadiusHead t R q).2 h))
  have hd : 0 < ‖z‖ := by linarith only [hR, hdR]
  have hi : z.im ^ 2 < 1 / 4 := by
    simpa only [z, Complex.sub_im, Complex.ofReal_im, sub_zero] using
      xiSpectralPoint_im_sq_lt_quarter q
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre : (z ^ 2).re = ‖z‖ ^ 2 - 2 * z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    nlinarith only [hnorm]
  change 3 / 4 * ‖(z ^ 2)⁻¹‖ ≤ ((z ^ 2)⁻¹).re
  rw [norm_inv, norm_pow, Complex.inv_re, Complex.normSq_eq_norm_sq, norm_pow, hre]
  rw [show 3 / 4 * (‖z‖ ^ 2)⁻¹ = (3 / 4) / ‖z‖ ^ 2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos (sq_pos_of_pos hd))).2
  have hwide : 8 * z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith only [hi, hR, hdR, sq_nonneg (‖z‖ - 4)]
  nlinarith only [mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.mpr hwide)]

private theorem gaussian_norm_one_add_upper {v : ℂ} (hr : 0 ≤ v.re)
    (hv : ‖v‖ ^ 2 ≤ 2 * v.re ^ 2) : ‖1 + v‖ ≤ Real.exp v.re := by
  have hid : ‖1 + v‖ ^ 2 = 1 + 2 * v.re + ‖v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, zero_add]
    ring
  have he := WeilLevyHarmonicDoubling.one_add_add_half_sq_le_exp
    (show 0 ≤ 2 * v.re from mul_nonneg (by norm_num) hr)
  have heq : Real.exp (2 * v.re) = (Real.exp v.re) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [heq] at he
  nlinarith only [hid, hv, he, norm_nonneg (1 + v), Real.exp_pos v.re]

private theorem gaussian_norm_one_add_lower {v : ℂ} (hr : 0 ≤ v.re) :
    Real.exp (v.re - ‖v‖ ^ 2) ≤ ‖1 + v‖ := by
  have hnorm : 1 + v.re ≤ ‖1 + v‖ := by
    have h := (le_abs_self (1 + v).re).trans (Complex.abs_re_le_norm (1 + v))
    simpa only [Complex.add_re, Complex.one_re] using h
  have hpos : 0 < 1 + v.re := by linarith only [hr]
  have hsq : v.re ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg v.im]
  have hlog : v.re - ‖v‖ ^ 2 ≤ Real.log ‖1 + v‖ :=
    (sub_le_sub_left hsq _).trans
      ((WeilSingularArithmetic.log_one_add_lower_quadratic hr).trans
        (Real.log_le_log hpos hnorm))
  simpa only [Real.exp_log (hpos.trans_le hnorm)] using Real.exp_le_exp.mpr hlog

private theorem gaussian_tprod_eq_norm_of_involution {ι : Type*} (f : ι → ℂ)
    (hf : Multipliable f) (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i)
    (hconj : ∀ i, f (σ i) = (starRingEnd ℂ) (f i)) (hre : ∀ i, 0 ≤ (f i).re) :
    tprod f = (‖tprod f‖ : ℂ) := by
  classical
  let P : (ℂ → ℂ) → Prop := fun g => g 0 = (‖g 0‖ : ℂ)
  have hone : P (fun _ => 1) := by simp [P]
  have hmul : ∀ g h : ℂ → ℂ, P g → P h → P (g * h) := by
    intro g h hg hh
    change g 0 * h 0 = (‖g 0 * h 0‖ : ℂ)
    rw [norm_mul, Complex.ofReal_mul, ← hg, ← hh]
  have hfix : ∀ i, σ i = i → P (fun _ => f i) := by
    intro i hi
    have hc : (starRingEnd ℂ) (f i) = f i := by rw [← hconj, hi]
    have him := Complex.conj_eq_iff_im.mp hc
    have heq : f i = ((f i).re : ℂ) := Complex.ext rfl (by simpa using him)
    change f i = (‖f i‖ : ℂ)
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hre i)]
  have hpair : ∀ i, σ i ≠ i → P ((fun _ => f i) * (fun _ => f (σ i))) := by
    intro i _
    change f i * f (σ i) = (‖f i * f (σ i)‖ : ℂ)
    rw [hconj, Complex.mul_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _)]
  let c : Finset ι → Finset ι := fun F => F ∪ F.image σ
  have hc : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun F => Finset.subset_union_left) tendsto_id
  have hclosed : ∀ F, ∀ i ∈ c F, σ i ∈ c F := by
    intro F i hi
    simp only [c, Finset.mem_union, Finset.mem_image] at hi ⊢
    rcases hi with hi | ⟨j, hj, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl (by simpa only [hσ] using hj)
  have hfin (F : Finset ι) : (∏ i ∈ c F, f i) = (‖∏ i ∈ c F, f i‖ : ℂ) :=
    prod_of_involution_of_mul hone hmul σ hσ (fun i _ => f i) hfix hpair (c F) (hclosed F)
  have hp0 : Tendsto (fun F : Finset ι => ∏ i ∈ F, f i) atTop (𝓝 (tprod f)) := hf.hasProd
  have hp := hp0.comp hc
  have hn : Tendsto (fun F : Finset ι => (‖∏ i ∈ c F, f i‖ : ℂ)) atTop
      (𝓝 (‖tprod f‖ : ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp hp.norm
  exact tendsto_nhds_unique hp (hn.congr (fun F => (hfin F).symm))

private def gaussian_real_tailPartner (t R : ℝ)
    (q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R}) :
    {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R} :=
  ⟨lagPartner q, by
    intro h
    apply q.property
    rw [mem_xiSliceGaussianRadiusHead] at h ⊢
    rw [xiSpectralPoint_lagPartner] at h
    have hc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
    rwa [← hc, ← map_sub, Complex.norm_conj] at h⟩

/-- The real-axis tail is positive in orientation: it equals its nonnegative norm. -/
theorem xiSliceGaussianTail_real_eq_norm (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ) =
      (‖xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ : ℂ) := by
  let H := xiSliceGaussianRadiusHead t R
  let f : {q : XiZeroCopy // q ∉ H} → ℂ := fun q =>
    1 + (x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q
  have hs : Summable fun q : {q : XiZeroCopy // q ∉ H} =>
      ‖(x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q‖ := by
    simpa only [norm_mul, norm_pow] using
      (summable_norm_xiSliceGaussianTail t H).mul_left (‖(x : ℂ)‖ ^ 2)
  change tprod f = (‖tprod f‖ : ℂ)
  apply gaussian_tprod_eq_norm_of_involution f (multipliable_one_add_of_summable hs)
    (gaussian_real_tailPartner t R)
  · intro q
    exact Subtype.ext (lagPartner_lagPartner q)
  · intro q
    change 1 + (x : ℂ) ^ 2 * ((xiSpectralPoint (lagPartner q) - (t : ℂ)) ^ 2)⁻¹ = _
    simp only [f, xiSliceGaussianReciprocal, xiSpectralPoint_lagPartner,
      map_add, map_one, map_mul, map_pow, map_inv₀, map_sub, Complex.conj_ofReal]
  · intro q
    have hb := gaussian_real_reciprocal_cone t hR q
    have hb0 : 0 ≤ (xiSliceGaussianReciprocal t q).re :=
      (mul_nonneg (by norm_num) (norm_nonneg _)).trans hb
    change 0 ≤ (1 + (x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q).re
    rw [Complex.add_re, Complex.one_re, ← Complex.ofReal_pow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    positivity

private theorem gaussian_real_factor_bounds (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ)
    (q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R}) :
    Real.exp (x ^ 2 * (xiSliceGaussianReciprocal t q).re -
      x ^ 4 * ‖xiSliceGaussianReciprocal t q‖ ^ 2) ≤
        ‖1 + (x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q‖ ∧
    ‖1 + (x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q‖ ≤
      Real.exp (x ^ 2 * (xiSliceGaussianReciprocal t q).re) := by
  let b := xiSliceGaussianReciprocal t q
  have hb : 3 / 4 * ‖b‖ ≤ b.re := gaussian_real_reciprocal_cone t hR q
  have hb0 : 0 ≤ b.re := (mul_nonneg (by norm_num) (norm_nonneg b)).trans hb
  have hbsq : ‖b‖ ^ 2 ≤ 2 * b.re ^ 2 := by
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 3 / 4 * ‖b‖) hb
    nlinarith only [hsq, sq_nonneg ‖b‖]
  have hre : ((x : ℂ) ^ 2 * b).re = x ^ 2 * b.re := by
    rw [← Complex.ofReal_pow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hnorm : ‖(x : ℂ) ^ 2 * b‖ ^ 2 = x ^ 4 * ‖b‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hr : 0 ≤ ((x : ℂ) ^ 2 * b).re := by rw [hre]; positivity
  constructor
  · simpa only [hre, hnorm] using gaussian_norm_one_add_lower hr
  · have hv : ‖(x : ℂ) ^ 2 * b‖ ^ 2 ≤ 2 * (((x : ℂ) ^ 2 * b).re) ^ 2 := by
      rw [hre, hnorm]
      nlinarith only [mul_le_mul_of_nonneg_left hbsq (by positivity : 0 ≤ x ^ 4)]
    simpa only [hre] using gaussian_norm_one_add_upper hr hv

/-- Global Gaussian bracketing on the real axis uses the exact oriented quadratic coefficient. -/
theorem norm_xiSliceGaussianTail_real_bounds (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    Real.exp (x ^ 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re -
      x ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) ≤
        ‖xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ ∧
    ‖xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ ≤
      Real.exp (x ^ 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re) := by
  classical
  let H := xiSliceGaussianRadiusHead t R
  have hs := summable_norm_xiSliceGaussianTail t H
  have hsre : Summable fun q : {q : XiZeroCopy // q ∉ H} =>
      (xiSliceGaussianReciprocal t q).re := by
    apply Summable.of_norm
    exact hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (xiSliceGaussianReciprocal t q))
  have hssq := summable_sq_norm_xiSliceGaussianTail t H
  have htsum : (∑' q : {q : XiZeroCopy // q ∉ H}, (xiSliceGaussianReciprocal t q).re) =
      (xiSliceGaussianTailQuadratic t H).re := (Complex.re_tsum hs.of_norm).symm
  have hsr : Tendsto (fun F : Finset {q : XiZeroCopy // q ∉ H} =>
      ∑ q ∈ F, (xiSliceGaussianReciprocal t q).re) atTop
      (𝓝 (xiSliceGaussianTailQuadratic t H).re) := by
    rw [← htsum]
    exact hsre.hasSum
  have hsb : Tendsto (fun F : Finset {q : XiZeroCopy // q ∉ H} =>
      ∑ q ∈ F, ‖xiSliceGaussianReciprocal t q‖ ^ 2) atTop
      (𝓝 (xiSliceGaussianTailFourth t H)) := hssq.hasSum
  have hprod : Tendsto (fun F : Finset {q : XiZeroCopy // q ∉ H} =>
      ∏ q ∈ F, (1 + (x : ℂ) ^ 2 * xiSliceGaussianReciprocal t q)) atTop
      (𝓝 (xiSliceGaussianTail t H (x : ℂ))) :=
    (multipliable_one_add_of_summable (by
      simpa only [norm_mul, norm_pow] using hs.mul_left (‖(x : ℂ)‖ ^ 2))).hasProd
  have hup : Tendsto (fun F : Finset {q : XiZeroCopy // q ∉ H} =>
      Real.exp (x ^ 2 * ∑ q ∈ F, (xiSliceGaussianReciprocal t q).re)) atTop
      (𝓝 (Real.exp (x ^ 2 * (xiSliceGaussianTailQuadratic t H).re))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp (hsr.const_mul (x ^ 2))
  have hlo : Tendsto (fun F : Finset {q : XiZeroCopy // q ∉ H} =>
      Real.exp (x ^ 2 * (∑ q ∈ F, (xiSliceGaussianReciprocal t q).re) -
        x ^ 4 * ∑ q ∈ F, ‖xiSliceGaussianReciprocal t q‖ ^ 2)) atTop
      (𝓝 (Real.exp (x ^ 2 * (xiSliceGaussianTailQuadratic t H).re -
        x ^ 4 * xiSliceGaussianTailFourth t H))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((hsr.const_mul (x ^ 2)).sub (hsb.const_mul (x ^ 4)))
  constructor
  · apply le_of_tendsto_of_tendsto' hlo hprod.norm
    intro F
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Real.exp_sum, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun q _ => (gaussian_real_factor_bounds t hR x q).1)
  · apply le_of_tendsto_of_tendsto' hprod.norm hup
    intro F
    rw [Finset.mul_sum, Real.exp_sum, norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun q _ => (gaussian_real_factor_bounds t hR x q).2)

/-- On the whole real axis, multiplicative Gaussian compensation has only fourth-moment error. -/
theorem norm_xiSliceGaussianTail_real_compensated_sub_one_le
    (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    ‖Complex.exp (-((x : ℂ) ^ 2 *
        xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
      xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ) - 1‖ ≤
        x ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) := by
  let H := xiSliceGaussianRadiusHead t R
  let A := x ^ 2 * (xiSliceGaussianTailQuadratic t H).re
  let B := x ^ 4 * xiSliceGaussianTailFourth t H
  let T := ‖xiSliceGaussianTail t H (x : ℂ)‖
  have hb := norm_xiSliceGaussianTail_real_bounds t hR x
  have hu : Real.exp (-A) * T ≤ 1 := by
    calc
      _ ≤ Real.exp (-A) * Real.exp A :=
        mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hl : Real.exp (-B) ≤ Real.exp (-A) * T := by
    calc
      _ = Real.exp (-A) * Real.exp (A - B) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos _).le
  have hC : xiSliceGaussianTailQuadratic t H =
      ((xiSliceGaussianTailQuadratic t H).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using xiSliceGaussianTailQuadratic_im_eq_zero t R
  change ‖Complex.exp (-((x : ℂ) ^ 2 * xiSliceGaussianTailQuadratic t H)) *
      xiSliceGaussianTail t H (x : ℂ) - 1‖ ≤ B
  rw [hC, xiSliceGaussianTail_real_eq_norm t hR x]
  have heq :
      Complex.exp (-((x : ℂ) ^ 2 * ((xiSliceGaussianTailQuadratic t H).re : ℂ))) *
        (T : ℂ) - 1 = ((Real.exp (-A) * T - 1 : ℝ) : ℂ) := by
    simp only [A, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith only [hl, Real.add_one_le_exp (-B)]

/-- The actual real Xi slice has a global fourth-moment error after retaining its finite head. -/
theorem norm_xiSliceProduct_real_compensated_sub_head_le {t : ℝ} (ht : XiC t ≠ 0)
    {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    ‖Complex.exp (-((x : ℂ) ^ 2 *
        xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
      (xiSliceProduct t (x : ℂ) / xiSliceProduct t 0) -
        xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ ≤
      ‖xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ *
        (x ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) := by
  rw [xiSliceProduct_div_eq_gaussianHead_mul_tail ht]
  rw [show Complex.exp (-((x : ℂ) ^ 2 *
        xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
      (xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) (x : ℂ) *
        xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)) -
      xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) (x : ℂ) =
      xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) (x : ℂ) *
        (Complex.exp (-((x : ℂ) ^ 2 *
          xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
          xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ) - 1) by ring,
    norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_xiSliceGaussianTail_real_compensated_sub_one_le t hR x) (norm_nonneg _)

end
end RHTower

