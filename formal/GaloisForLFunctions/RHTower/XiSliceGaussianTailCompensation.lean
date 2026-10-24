import GaloisForLFunctions.RHTower.CanonicalProductE1RealLineBounds
import GaloisForLFunctions.RHTower.XiSliceGaussianTailLimit
import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion

/-!
# Exact real orientation and multiplicative Gaussian compensation

Reflection makes a radius tail's quadratic coefficient real. Its deficit from the absolute
reciprocal-square mass is exactly twice the transverse fourth moment, bounded by half the
fourth reciprocal-distance moment. Compensating each factor by its exponential turns it into
a genus-one Weierstrass factor. On the cutoff disc this bounds the relative product error by
`exp(‖z‖⁴ B)-1`, with no exponential cost in the total reciprocal-square mass.
-/

open Filter Topology Complex
namespace RHTower
noncomputable section

private theorem reciprocal_square_real_defect (z : ℂ) :
    ((z ^ 2)⁻¹).re = ‖(z ^ 2)⁻¹‖ - 2 * z.im ^ 2 * ‖(z ^ 2)⁻¹‖ ^ 2 := by
  by_cases hz : z = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), inv_zero, Complex.zero_re,
      Complex.zero_im, norm_zero, mul_zero, sub_zero]
  have hd : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq, norm_pow, hre, norm_inv, norm_pow]
  field_simp [hd]
  nlinarith only [hnorm]

/-- The transverse fourth moment is the deficit of the real quadratic sum from norm mass. -/
def xiSliceGaussianTailTransverse (t : ℝ) (H : Finset XiZeroCopy) : ℝ :=
  ∑' q : {q : XiZeroCopy // q ∉ H},
    2 * (xiSpectralPoint q).im ^ 2 * ‖xiSliceGaussianReciprocal t q‖ ^ 2

private theorem gaussian_transverse_term_le (t : ℝ) (q : XiZeroCopy) :
    2 * (xiSpectralPoint q).im ^ 2 * ‖xiSliceGaussianReciprocal t q‖ ^ 2 ≤
      (1 / 2) * ‖xiSliceGaussianReciprocal t q‖ ^ 2 := by
  have h : 2 * (xiSpectralPoint q).im ^ 2 ≤ 1 / 2 := by
    linarith only [xiSpectralPoint_im_sq_lt_quarter q]
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

theorem summable_xiSliceGaussianTailTransverse (t : ℝ) (H : Finset XiZeroCopy) :
    Summable fun q : {q : XiZeroCopy // q ∉ H} =>
      2 * (xiSpectralPoint q).im ^ 2 * ‖xiSliceGaussianReciprocal t q‖ ^ 2 :=
  ((summable_sq_norm_xiSliceGaussianTail t H).mul_left (1 / 2)).of_nonneg_of_le
    (fun _ => by positivity) (fun q => gaussian_transverse_term_le t q)

theorem xiSliceGaussianTailTransverse_bounds (t : ℝ) (H : Finset XiZeroCopy) :
    0 ≤ xiSliceGaussianTailTransverse t H ∧
      xiSliceGaussianTailTransverse t H ≤ xiSliceGaussianTailFourth t H / 2 := by
  refine ⟨tsum_nonneg (fun _ => by positivity), ?_⟩
  calc
    xiSliceGaussianTailTransverse t H ≤
        ∑' q : {q : XiZeroCopy // q ∉ H}, (1 / 2) * ‖xiSliceGaussianReciprocal t q‖ ^ 2 :=
      Summable.tsum_le_tsum (fun q => gaussian_transverse_term_le t q)
        (summable_xiSliceGaussianTailTransverse t H)
        ((summable_sq_norm_xiSliceGaussianTail t H).mul_left (1 / 2))
    _ = xiSliceGaussianTailFourth t H / 2 := by
      rw [tsum_mul_left, xiSliceGaussianTailFourth]
      ring

/-- The real quadratic coefficient has an exact nonnegative transverse defect. -/
theorem xiSliceGaussianTailQuadratic_re_eq (t : ℝ) (H : Finset XiZeroCopy) :
    (xiSliceGaussianTailQuadratic t H).re =
      xiSliceGaussianTailMass t H - xiSliceGaussianTailTransverse t H := by
  have hs := summable_norm_xiSliceGaussianTail t H
  have hterm (q : {q : XiZeroCopy // q ∉ H}) :
      (xiSliceGaussianReciprocal t q).re = ‖xiSliceGaussianReciprocal t q‖ -
        2 * (xiSpectralPoint q).im ^ 2 * ‖xiSliceGaussianReciprocal t q‖ ^ 2 := by
    simpa only [xiSliceGaussianReciprocal, Complex.sub_im, Complex.ofReal_im, sub_zero] using
      reciprocal_square_real_defect (xiSpectralPoint q - (t : ℂ))
  rw [xiSliceGaussianTailQuadratic, Complex.re_tsum hs.of_norm]
  calc
    _ = ∑' q : {q : XiZeroCopy // q ∉ H}, (‖xiSliceGaussianReciprocal t q‖ -
        2 * (xiSpectralPoint q).im ^ 2 * ‖xiSliceGaussianReciprocal t q‖ ^ 2) := tsum_congr hterm
    _ = xiSliceGaussianTailMass t H - xiSliceGaussianTailTransverse t H :=
      hs.tsum_sub (summable_xiSliceGaussianTailTransverse t H)

private theorem gaussian_radiusHead_lagPartner (t R : ℝ) (q : XiZeroCopy) :
    lagPartner q ∈ xiSliceGaussianRadiusHead t R ↔ q ∈ xiSliceGaussianRadiusHead t R := by
  rw [mem_xiSliceGaussianRadiusHead, mem_xiSliceGaussianRadiusHead, xiSpectralPoint_lagPartner]
  have hc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [← hc, ← map_sub, Complex.norm_conj, hc]

private def gaussian_tailPartnerEquiv (t R : ℝ) :
    {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R} ≃
      {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R} where
  toFun q := ⟨lagPartner q, fun h => q.property ((gaussian_radiusHead_lagPartner t R q).mp h)⟩
  invFun q := ⟨lagPartner q, fun h => q.property ((gaussian_radiusHead_lagPartner t R q).mp h)⟩
  left_inv q := Subtype.ext (lagPartner_lagPartner q)
  right_inv q := Subtype.ext (lagPartner_lagPartner q)

private theorem gaussian_reciprocal_lagPartner (t : ℝ) (q : XiZeroCopy) :
    xiSliceGaussianReciprocal t (lagPartner q) = (starRingEnd ℂ) (xiSliceGaussianReciprocal t q) := by
  have hc : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [xiSliceGaussianReciprocal, xiSliceGaussianReciprocal, xiSpectralPoint_lagPartner,
    map_inv₀, map_pow, map_sub, hc]

/-- Reflection makes the quadratic coefficient of the actual radius tail real. -/
theorem xiSliceGaussianTailQuadratic_im_eq_zero (t R : ℝ) :
    (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [xiSliceGaussianTailQuadratic, Complex.conj_tsum]
  calc
    _ = ∑' q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R},
        xiSliceGaussianReciprocal t (gaussian_tailPartnerEquiv t R q) :=
      tsum_congr (fun q => (gaussian_reciprocal_lagPartner t q).symm)
    _ = _ := (gaussian_tailPartnerEquiv t R).tsum_eq
      (fun q : {q : XiZeroCopy // q ∉ xiSliceGaussianRadiusHead t R} =>
        xiSliceGaussianReciprocal t q)

/-- Exact real orientation: positive norm mass minus the transverse fourth-moment defect. -/
theorem xiSliceGaussianTailQuadratic_eq_mass_sub_transverse (t R : ℝ) :
    xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R) =
      ((xiSliceGaussianTailMass t (xiSliceGaussianRadiusHead t R) -
        xiSliceGaussianTailTransverse t (xiSliceGaussianRadiusHead t R) : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      xiSliceGaussianTailQuadratic_re_eq t (xiSliceGaussianRadiusHead t R)
  · simpa only [Complex.ofReal_im] using xiSliceGaussianTailQuadratic_im_eq_zero t R

private theorem norm_compensated_tprod_sub_one_le {ι : Type*} (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (hsmall : ∀ i, ‖a i‖ ≤ 1) :
    ‖Complex.exp (-tsum a) * tprod (fun i : ι => (1 : ℂ) + a i) - 1‖ ≤
      Real.exp (∑' i, ‖a i‖ ^ 2) - 1 := by
  let u := fun i => (1 + a i) * Complex.exp (-a i) - 1
  have hbound (i : ι) : ‖u i‖ ≤ ‖a i‖ ^ 2 := by
    have h := weierstrassE1_sub_one_norm_le (z := -a i) (by
      simpa only [norm_neg] using hsmall i)
    simpa only [u, weierstrassE1, sub_neg_eq_add, norm_neg] using h
  have hsq : Summable fun i => ‖a i‖ ^ 2 :=
    ha.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => by
      nlinarith only [mul_le_mul_of_nonneg_left (hsmall i) (norm_nonneg (a i))])
  have hu : Summable fun i => ‖u i‖ :=
    hsq.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hp : Tendsto (fun F : Finset ι => ∏ i ∈ F, (1 + a i)) atTop
      (𝓝 (tprod (fun i : ι => (1 : ℂ) + a i))) :=
    (multipliable_one_add_of_summable ha).hasProd
  have hs : Tendsto (fun F : Finset ι => ∑ i ∈ F, a i) atTop (𝓝 (tsum a)) :=
    ha.of_norm.hasSum
  have he : Tendsto (fun F : Finset ι => Complex.exp (-∑ i ∈ F, a i)) atTop
      (𝓝 (Complex.exp (-tsum a))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp hs.neg
  have hid (F : Finset ι) : (∏ i ∈ F, (1 + u i)) =
      (∏ i ∈ F, (1 + a i)) * Complex.exp (-∑ i ∈ F, a i) := by
    have hfactor : ∀ i, 1 + u i = (1 + a i) * Complex.exp (-a i) := by
      intro i
      dsimp only [u]
      ring
    simp only [hfactor, Finset.prod_mul_distrib, ← Complex.exp_sum,
      Finset.sum_neg_distrib]
  have hprod : HasProd (fun i => 1 + u i)
      (tprod (fun i : ι => (1 : ℂ) + a i) * Complex.exp (-tsum a)) := by
    change Tendsto (fun F : Finset ι => ∏ i ∈ F, (1 + u i)) atTop _
    simpa only [hid] using hp.mul he
  have hsum : (∑' i, ‖u i‖) ≤ ∑' i, ‖a i‖ ^ 2 :=
    Summable.tsum_le_tsum hbound hu hsq
  simpa only [mul_comm] using
    GaloisForLFunctions.HTGeometry.norm_tprod_one_add_sub_one_le hprod hu hsum

/-- Compensating the actual tail by its exact quadratic exponential removes the total-mass
envelope: only the fourth reciprocal-distance moment remains on the cutoff disc. -/
theorem norm_xiSliceGaussianTail_compensated_sub_one_le (t : ℝ) {R : ℝ}
    (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z - 1‖ ≤
      Real.exp (‖z‖ ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) - 1 := by
  let H := xiSliceGaussianRadiusHead t R
  have hs : Summable fun q : {q : XiZeroCopy // q ∉ H} =>
      ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ := by
    simpa only [norm_mul, norm_pow] using
      (summable_norm_xiSliceGaussianTail t H).mul_left (‖z‖ ^ 2)
  have hsmall (q : {q : XiZeroCopy // q ∉ H}) :
      ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ ≤ 1 := by
    have hd : R < ‖xiSpectralPoint q - (t : ℂ)‖ :=
      lt_of_not_ge (fun h => q.property ((mem_xiSliceGaussianRadiusHead t R q).2 h))
    rw [norm_mul, norm_pow, xiSliceGaussianReciprocal, norm_inv, norm_pow, ← div_eq_mul_inv]
    exact (div_le_one (sq_pos_of_pos (hR.trans hd))).2
      (pow_le_pow_left₀ (norm_nonneg _) (hz.trans hd.le) 2)
  have h := norm_compensated_tprod_sub_one_le
    (fun q : {q : XiZeroCopy // q ∉ H} => z ^ 2 * xiSliceGaussianReciprocal t q) hs hsmall
  have hquad : (∑' q : {q : XiZeroCopy // q ∉ H}, z ^ 2 * xiSliceGaussianReciprocal t q) =
      z ^ 2 * xiSliceGaussianTailQuadratic t H := tsum_mul_left
  have hfourth : (∑' q : {q : XiZeroCopy // q ∉ H}, ‖z ^ 2 * xiSliceGaussianReciprocal t q‖ ^ 2) =
      ‖z‖ ^ 4 * xiSliceGaussianTailFourth t H := by
    simp only [norm_mul, norm_pow, mul_pow, ← pow_mul, tsum_mul_left,
      xiSliceGaussianTailFourth]
  simpa only [hquad, hfourth, xiSliceGaussianTail] using h

/-- The complete normalized Xi slice has a compensated finite-block approximation whose
relative tail error contains no exponential in the reciprocal-square mass. -/
theorem norm_xiSliceProduct_compensated_sub_head_le {t R : ℝ} (ht : XiC t ≠ 0)
    (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        (xiSliceProduct t z / xiSliceProduct t 0) -
          xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) z‖ ≤
      ‖xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) z‖ *
        (Real.exp (‖z‖ ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) - 1) := by
  rw [xiSliceProduct_div_eq_gaussianHead_mul_tail ht (xiSliceGaussianRadiusHead t R)]
  rw [show Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
      (xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) z *
        xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z) -
          xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) z =
      xiSliceGaussianHead t (xiSliceGaussianRadiusHead t R) z *
        (Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
          xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z - 1) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_xiSliceGaussianTail_compensated_sub_one_le t hR hz) (norm_nonneg _)

end
end RHTower
