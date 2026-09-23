import GaloisForLFunctions.RHTower.EulerDeletionQuarticRemainder
import GaloisForLFunctions.RHTower.ArithmeticPrimeSievePhase

/-!
# A joint height and cutoff bound for the literal arithmetic remainder phase

The quartic Bernoulli correction bounds the normalized ordinary remainder by an
explicit disk around `-1/(12*(conjugate(s)+1))`. Comparing that disk with the real
axis gives a source-derived strict phase sign, uniform jointly in the complex
parameter and the integer cutoff.

For `0 < Re(s) ≤ 1`, `Im(s) ≥ 1`, and `N² ≥ Im(s)³`, the actual normalized
weighted remainder has negative imaginary part. No zero equation is used.
The initial indices outside this region retain their full arithmetic content;
this tail bound does not impose a sign on the unit remainder at a high zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The normalized arithmetic remainder is the anchored Bernoulli tail itself. -/
theorem normalizedWeightedRemainder_eq_bernoulli {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    normalizedWeightedRemainder s N = (N:ℂ)^(-s)*RHTower.zetaBernoulliTail N (star s) := by
  have hu : star s  ≠  0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : star s+1  ≠  0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hs' : -1 < (star s).re := by simp; linarith
  have hs1' : star s ≠ 1 := by intro h; apply hs1; simpa using congrArg star h
  rw [normalizedWeightedRemainder,weightedPowerRemainder,
    ← powerSumRemainder_star (by linarith) hs1 N,
    powerSumRemainder_eq_bernoulli hs' hs1' hN,minimumNormalization,kernel]
  field_simp

/-- The scaled remainder retains its exact quartic correction, with all phases unchanged. -/
theorem normalizedWeightedRemainder_scaled_eq_quartic {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) =
      -(star s+1)⁻¹/12 +
      ((star s+2)*(star s+3))*quarticPrimitiveTail N (star s)*(N:ℂ)^(star s+1) := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs' : -1 < (star s).re := by simp; linarith
  have he : ((2*s.re+1:ℝ):ℂ)=s+star s+1 := by
    apply Complex.ext  <;> simp
    ring
  have hc : (N:ℂ)^(-s)*(N:ℂ)^(s+star s+1)=(N:ℂ)^(star s+1) := by
    rw [← Complex.cpow_add _ _ hn]
    congr 1; ring
  have hd : (N:ℂ)^(-star s-1)*(N:ℂ)^(star s+1)=1 := by
    rw [← Complex.cpow_add _ _ hn,show -star s-1+(star s+1)=0 by ring,Complex.cpow_zero]
  rw [normalizedWeightedRemainder_eq_bernoulli hs hs1 hN,
    bernoulliTail_eq_mean_add_quartic hs' hN,Complex.ofReal_cpow hp.le,he]
  push_cast
  calc
    _ = (-(N:ℂ)^(-star s-1)/(12*(star s+1))+
        ((star s+2)*(star s+3))*quarticPrimitiveTail N (star s))*
          ((N:ℂ)^(-s)*(N:ℂ)^(s+star s+1)) := by ring
    _ = _ := by
      rw [hc,add_mul]
      have hmain : (-(N:ℂ)^(-star s-1)/(12*(star s+1)))*(N:ℂ)^(star s+1) =
          -(star s+1)⁻¹/12 := by
        calc
          _ = -((N:ℂ)^(-star s-1)*(N:ℂ)^(star s+1))/(12*(star s+1)) := by ring
          _ = _ := by rw [hd]; simp only [mul_inv_rev,div_eq_mul_inv]; ring
      rw [hmain]

/-- An explicit bound uniform jointly in height and positive integer cutoff. -/
theorem norm_normalizedWeightedRemainder_scaled_sub_mean_le {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ) - (-(star s+1)⁻¹/12)‖  ≤
      (‖s+2‖*‖s+3‖)/(384*(s.re+3)*(N:ℝ)^(2 : ℕ)) := by
  have hp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs' : -1 < (star s).re := by simp; linarith
  have hq := norm_quarticPrimitiveTail_le hs' hN
  simp only [Complex.star_def,Complex.conj_re] at hq
  have h2 : star s+2=star (s+2) := by simp
  have h3 : star s+3=star (s+3) := by simp
  rw [normalizedWeightedRemainder_scaled_eq_quartic hs hs1 hN,add_sub_cancel_left,
    norm_mul,norm_mul,norm_mul,h2,h3,norm_star,norm_star,
    Complex.norm_natCast_cpow_of_pos (by omega)]
  have he : (star s+1).re=s.re+1 := by simp
  rw [he]
  refine (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (Real.rpow_nonneg hp.le _)).trans_eq ?_
  calc
    _ = (‖s+2‖*‖s+3‖)/(384*(s.re+3))*
        ((N:ℝ)^(-s.re-3)*(N:ℝ)^(s.re+1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hp,show -s.re-3+(s.re+1)=(-2:ℝ) by ring,
        Real.rpow_neg hp.le,Real.rpow_two]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- The leading imaginary margin dominates the complete arithmetic error on this explicit region. -/
theorem normalizedWeightedRemainder_im_neg_of_quartic_bound {s : ℂ}
    (hs : 0 < s.re) (ht : 0 < s.im) {N : ℕ} (hN : 1 ≤ N)
    (hcut : ‖s+2‖*‖s+3‖*Complex.normSq (s+1)  <
      32*(s.re+3)*s.im*(N:ℝ)^(2 : ℕ)) :
    (normalizedWeightedRemainder s N).im  <  0 := by
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
  have hb := norm_normalizedWeightedRemainder_scaled_sub_mean_le hs hs1 hN
  have hsmall : (‖s+2‖*‖s+3‖)/(384*(s.re+3)*(N:ℝ)^(2 : ℕ))  <
      s.im/(12*Complex.normSq (s+1)) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 384*(s.re+3)*(N:ℝ)^(2 : ℕ))
      (by positivity : 0 < 12*Complex.normSq (s+1))).mpr
    nlinarith [hcut]
  have him := (le_abs_self _).trans (Complex.abs_im_le_norm
    (normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ)- (-(star s+1)⁻¹/12)))
  rw [Complex.sub_im,hc] at him
  simp only [neg_div] at hb him
  have hprod : (normalizedWeightedRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ)).im  <  0 := by
    linarith
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add] at hprod
  by_contra h
  have hnonneg := mul_nonneg (le_of_not_gt h) hscale.le
  linarith

/-- In the strip, the cutoff `N² ≥ Im(s)³` controls every remainder phase simultaneously. -/
theorem normalizedWeightedRemainder_im_neg_of_height_cube {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 1 ≤ s.im) {N : ℕ} (hN : 1 ≤ N)
    (hcut : s.im^(3 : ℕ) ≤ (N:ℝ)^(2 : ℕ)) :
    (normalizedWeightedRemainder s N).im  <  0 := by
  have htpos : 0 < s.im := by linarith
  have ht2 : 1 ≤ s.im^(2 : ℕ) := by nlinarith
  have e1 : Complex.normSq (s+1)=(s.re+1)^(2 : ℕ)+s.im^(2 : ℕ) := by
    simp [Complex.normSq_apply,pow_two]
  have e2 : ‖s+2‖^(2 : ℕ)=(s.re+2)^(2 : ℕ)+s.im^(2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
  have e3 : ‖s+3‖^(2 : ℕ)=(s.re+3)^(2 : ℕ)+s.im^(2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,pow_two]
  have b1 : Complex.normSq (s+1) ≤ 5*s.im^(2 : ℕ) := by
    rw [e1]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+3 by linarith)]
  have b2 : ‖s+2‖^(2 : ℕ) ≤ 10*s.im^(2 : ℕ) := by
    rw [e2]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+5 by linarith)]
  have b3 : ‖s+3‖^(2 : ℕ) ≤ 17*s.im^(2 : ℕ) := by
    rw [e3]
    nlinarith [mul_nonneg (show 0 ≤ 1-s.re by linarith) (show 0 ≤ s.re+7 by linarith)]
  have bp : ‖s+2‖*‖s+3‖ ≤ 27/2*s.im^(2 : ℕ) := by
    nlinarith [sq_nonneg (‖s+2‖-‖s+3‖)]
  have bfull : ‖s+2‖*‖s+3‖*Complex.normSq (s+1) ≤ 135/2*s.im^(4 : ℕ) := by
    have h := mul_le_mul bp b1 (Complex.normSq_nonneg _) (by positivity : 0 ≤ 27/2*s.im^(2 : ℕ))
    nlinarith [h]
  apply normalizedWeightedRemainder_im_neg_of_quartic_bound hs htpos hN
  have ht4 : 0 < s.im^(4 : ℕ) := pow_pos htpos _
  have hx := mul_le_mul_of_nonneg_left hcut htpos.le
  have hN2 : 0 < (N:ℝ)^(2 : ℕ) := by positivity
  have hst := mul_pos hs (mul_pos htpos hN2)
  nlinarith [bfull,hx,hst]

end RHTower.DeletionMixedRefinement
