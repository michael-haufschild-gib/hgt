import GaloisForLFunctions.RHTower.ArithmeticLogarithmicFourierTail
import GaloisForLFunctions.RHTower.ArithmeticRemainderPhaseCutoff

/-!
# A linear height cutoff for the literal arithmetic remainder phase

For `0 < Re(s) ≤ 1` and `Im(s) ≥ 1`, every integer cutoff `N ≥ Im(s)` has strictly
negative imaginary normalized weighted remainder. Signed Fourier control supplies the
uniform disk `1 / (15N)` at high heights, and the existing quartic disk covers heights
from one through five. Both estimates retain the original arithmetic power weights.

This improves the superlinear region `N² ≥ Im(s)³`. The exceptional initial indices
`N < Im(s)` still require a source comparison. No zero equation is assumed, and neither
RH nor the stronger proposed threshold `Im(s) < 2πN` is proved here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators

namespace RHTower.DeletionMixedRefinement

/-- Exact positive-real normalization of the actual weighted remainder. -/
theorem normalizedWeightedRemainder_scaled_eq_tail {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) =
      RHTower.zetaBernoulliTail N (star s) * (N:ℂ)^(star s+1) := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have he : ((2*s.re+1:ℝ):ℂ)=s+star s+1 := by
    apply Complex.ext <;> simp
    ring
  rw [normalizedWeightedRemainder_eq_bernoulli hs hs1 hN, Complex.ofReal_cpow hp.le, he]
  push_cast
  calc
    _ = RHTower.zetaBernoulliTail N (star s) * ((N:ℂ)^(-s)*(N:ℂ)^(s+star s+1)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hn]
      congr 2
      ring

/-- The literal normalized source lies in the explicit disk of radius `1/(15N)`. -/
theorem norm_normalizedWeightedRemainder_scaled_sub_mean_le_linear {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) (ht : |s.im| ≤ N) :
    ‖normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) - (-(star s+1)⁻¹/12)‖ ≤
      1/(15*(N:ℝ)) := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs' : -1 < (star s).re := by simp; linarith
  have hb := norm_centeredBernoulliTail_le_linear hp hs' (by simpa using ht)
  rw [centeredBernoulliTail_eq_sub_mean hs' hN] at hb
  have hd : (N:ℂ)^(-star s-1)*(N:ℂ)^(star s+1)=1 := by
    rw [← Complex.cpow_add _ _ hn, show -star s-1+(star s+1)=0 by ring, Complex.cpow_zero]
  have he : normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) - (-(star s+1)⁻¹/12) =
      (RHTower.zetaBernoulliTail N (star s) + (N:ℂ)^(-star s-1)/(12*(star s+1))) *
        (N:ℂ)^(star s+1) := by
    rw [normalizedWeightedRemainder_scaled_eq_tail hs hs1 hN, add_mul]
    have hh : ((N:ℂ)^(-star s-1)/(12*(star s+1)))*(N:ℂ)^(star s+1) = (star s+1)⁻¹/12 := by
      calc
        _ = ((N:ℂ)^(-star s-1)*(N:ℂ)^(star s+1))/(12*(star s+1)) := by ring
        _ = _ := by rw [hd]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    rw [hh]
    ring
  rw [he, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.one_re] at hb ⊢
  refine (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp.le _)).trans_eq ?_
  calc
    _ = ((N:ℝ)^(-s.re-2)*(N:ℝ)^(s.re+1))/15 := by ring
    _ = _ := by
      rw [← Real.rpow_add hp, show -s.re-2+(s.re+1)=(-1:ℝ) by ring, Real.rpow_neg_one]
      ring

/-- A source-derived linear disk criterion gives strict negative imaginary part. -/
theorem normalizedWeightedRemainder_im_neg_of_linear_bound {s : ℂ}
    (hs : 0 < s.re) (ht : 0 < s.im) {N : ℕ} (hN : 1 ≤ N) (htN : s.im ≤ N)
    (hcut : 4*Complex.normSq (s+1) < 5*s.im*(N:ℝ)) :
    (normalizedWeightedRemainder s N).im < 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hden : 0 < Complex.normSq (s+1) := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero]
    nlinarith [sq_nonneg (s.re+1)]
  have hscale : 0 < (N:ℝ)^(2*s.re+1) := Real.rpow_pos_of_pos hp _
  have hc : (-(star s+1)⁻¹/12).im = -s.im/(12*Complex.normSq (s+1)) := by
    simp only [Complex.div_ofNat_im,Complex.neg_im,Complex.inv_im,
      Complex.add_im,Complex.star_def,Complex.conj_im,Complex.one_im,add_zero,neg_neg]
    have he : Complex.normSq ((starRingEnd ℂ) s+1)=Complex.normSq (s+1) := by
      simp [Complex.normSq_apply]
    rw [he]
    ring
  have hb := norm_normalizedWeightedRemainder_scaled_sub_mean_le_linear hs hs1 hN
    (by simpa [abs_of_pos ht] using htN)
  have hsmall : 1/(15*(N:ℝ)) < s.im/(12*Complex.normSq (s+1)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have him := (le_abs_self _).trans (Complex.abs_im_le_norm
    (normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ)- (-(star s+1)⁻¹/12)))
  rw [Complex.sub_im,hc] at him
  simp only [neg_div] at hb him
  have hprod : (normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ)).im < 0 := by linarith
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at hprod
  by_contra h
  have hnonneg := mul_nonneg (le_of_not_gt h) hscale.le
  linarith

/-- The existing quartic bound covers every remaining height from one through five. -/
theorem normalizedWeightedRemainder_im_neg_of_height_le_five {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) (ht5 : s.im ≤ 5)
    {N : ℕ} (hN : 1 ≤ N) (htN : s.im ≤ N) :
    (normalizedWeightedRemainder s N).im < 0 := by
  have htpos : 0 < s.im := by linarith
  have e1 : Complex.normSq (s+1)=(s.re+1)^2+s.im^2 := by simp [Complex.normSq_apply,pow_two]
  have e2 : ‖s+2‖^2=(s.re+2)^2+s.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
  have e3 : ‖s+3‖^2=(s.re+3)^2+s.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
  have b1 : Complex.normSq (s+1) ≤ s.im^2+4 := by
    rw [e1]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+3 by linarith)]
  have b2 : ‖s+2‖^2 ≤ s.im^2+9 := by
    rw [e2]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+5 by linarith)]
  have b3 : ‖s+3‖^2 ≤ s.im^2+16 := by
    rw [e3]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+7 by linarith)]
  have bp : ‖s+2‖*‖s+3‖ ≤ s.im^2+25/2 := by
    nlinarith [sq_nonneg (‖s+2‖-‖s+3‖)]
  have bfull := mul_le_mul bp b1 (Complex.normSq_nonneg _) (by positivity : 0 ≤ s.im^2+25/2)
  have bt2 : s.im^2 ≤ s.im^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg s.im)]
  have bt3 : 1 ≤ s.im^3 := by nlinarith [sq_nonneg (s.im-1)]
  have bt4 : s.im^4 ≤ 5*s.im^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht5) (pow_nonneg htpos.le 3)]
  have bN : s.im^2 ≤ (N:ℝ)^2 := by nlinarith
  have hx := mul_le_mul_of_nonneg_left bN htpos.le
  apply normalizedWeightedRemainder_im_neg_of_quartic_bound hs htpos hN
  have hst := mul_pos hs (mul_pos htpos (by positivity : 0 < (N:ℝ)^2))
  nlinarith [bfull, bt2, bt3, bt4, hx, hst]

/-- Uniform linear cutoff: every actual remainder with `N ≥ Im(s) ≥ 1` has negative phase. -/
theorem normalizedWeightedRemainder_im_neg_of_height_le_cutoff {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (htN : s.im ≤ N) : (normalizedWeightedRemainder s N).im < 0 := by
  by_cases ht5 : s.im ≤ 5
  · exact normalizedWeightedRemainder_im_neg_of_height_le_five hs hs' ht ht5 hN htN
  apply normalizedWeightedRemainder_im_neg_of_linear_bound hs (by linarith) hN htN
  have e1 : Complex.normSq (s+1)=(s.re+1)^2+s.im^2 := by simp [Complex.normSq_apply,pow_two]
  rw [e1]
  have hr := mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+3 by linarith)
  have hprod := mul_le_mul_of_nonneg_left htN (by linarith : 0 ≤ s.im)
  nlinarith [sq_nonneg (s.im-5)]

end RHTower.DeletionMixedRefinement
