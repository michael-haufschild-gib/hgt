import GaloisForLFunctions.RHTower.WeilLogShiftPositiveTailGain

/-!
# Lower bounds retaining only the two facing cutoff edges

When the opposite cutoff factors lie on their plateaux, a central interval
loses two smooth-transition factors. The earlier symmetric margin estimate
lost four. The resulting inverse-distance exponential bound is suited to
recovery entries immediately below the diagonal.
-/

open MeasureTheory Filter Topology Set Real

noncomputable section

namespace RHTower

/-- A positive transition argument has an explicit inverse-distance lower bound. -/
theorem smoothTransition_ge_exp_edge {x : ℝ} (hx : 0 < x) :
    exp (-1 / x) / 2 ≤ smoothTransition x := by
  have hglue (t : ℝ) : expNegInvGlue t ≤ 1 := by
    by_cases ht : t ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos ht]
      norm_num
    · rw [expNegInvGlue, if_neg ht]
      exact exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge ht)))
  have hden : expNegInvGlue x + expNegInvGlue (1 - x) ≤ 2 := by
    linarith only [hglue x, hglue (1 - x)]
  calc
    _ = expNegInvGlue x / 2 := by
      rw [expNegInvGlue, if_neg (not_le_of_gt hx), inv_eq_one_div, neg_div]
    _ ≤ _ := div_le_div_of_nonneg_left (expNegInvGlue.nonneg x)
      (smoothTransition.pos_denom x) hden

/-- With the two opposite edges on their plateaux, only the facing transition
factors enter the central-interval lower bound. -/
theorem truncatedRiemannAutocorr_central_lower_two_edges {L z d a : ℝ}
    (hd : 0 < d) (hz : 0 ≤ z) (hmargin : z / 2 + d + a ≤ L)
    (hplateau : 1 ≤ L + z / 2 - d) :
    (2 * d * ((2 * π ^ 2) * smoothTransition a) ^ 2) *
      exp (-(2 * π * exp (z + 2 * d))) ≤ truncatedRiemannAutocorr L z := by
  let q := (2 * π ^ 2) * smoothTransition a
  have htransition := smoothTransition.nonneg a
  have hfactor (u : ℝ) (hcut : smoothTransition a ≤ bulkCutoff L u) :
      q * exp (-(π * exp (2 * |u|))) ≤ truncatedRiemannKernelReal L u := by
    have h := mul_le_mul (ExposingRayTail.phi_lower u) hcut
      (smoothTransition.nonneg a) (riemannKernelReal_pos u).le
    change _ ≤ riemannKernelReal u * bulkCutoff L u at h ⊢
    calc q * exp (-(π * exp (2 * |u|))) =
        (2 * π ^ 2 * exp (-(π * exp (2 * |u|)))) * smoothTransition a := by
          dsimp only [q]
          ring
      _ ≤ _ := h
  have hpoint : ∀ t ∈ Ioc (z / 2 - d) (z / 2 + d),
      q ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - z) := by
    intro t ht
    have hc1 : smoothTransition a ≤ bulkCutoff L t := by
      rw [bulkCutoff, smoothTransition.one_of_one_le
        (show 1 ≤ L + t by linarith only [ht.1, hplateau]), mul_one]
      exact smoothTransition.monotone (by linarith only [ht.2, hmargin])
    have hc2 : smoothTransition a ≤ bulkCutoff L (t - z) := by
      rw [bulkCutoff, smoothTransition.one_of_one_le
        (show 1 ≤ L - (t - z) by linarith only [ht.2, hplateau]), one_mul]
      exact smoothTransition.monotone (by linarith only [ht.1, hmargin])
    have ht1 : |t| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have ht2 : |t - z| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have h1 := exp_le_exp.mpr (show 2 * |t| ≤ z + 2 * d by linarith only [ht1])
    have h2 := exp_le_exp.mpr (show 2 * |t - z| ≤ z + 2 * d by linarith only [ht2])
    have hs : π * (exp (2 * |t|) + exp (2 * |t - z|)) ≤
        2 * π * exp (z + 2 * d) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) pi_pos.le
      nlinarith only [h]
    have heq (U V : ℝ) : (q * exp U) * (q * exp V) = q ^ 2 * exp (U + V) := by
      rw [exp_add]
      ring
    have hprod : q ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        (q * exp (-(π * exp (2 * |t|)))) * (q * exp (-(π * exp (2 * |t - z|)))) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply exp_le_exp.mpr
      linarith only [hs]
    exact hprod.trans (mul_le_mul (hfactor t hc1) (hfactor (t - z) hc2)
      (by dsimp only [q]; positivity) (truncatedRiemannKernelReal_nonneg L t))
  have hi := setIntegral_mono_on (integrableOn_const (by simp))
    (integrable_truncatedRiemannKernel_prod L z).integrableOn measurableSet_Ioc hpoint
  have hconst : (∫ t in Ioc (z / 2 - d) (z / 2 + d),
      q ^ 2 * exp (-(2 * π * exp (z + 2 * d)))) =
      (2 * d * q ^ 2) * exp (-(2 * π * exp (z + 2 * d))) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hi
  exact hi.trans (setIntegral_le_integral (integrable_truncatedRiemannKernel_prod L z)
    (Eventually.of_forall fun t => mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
      (truncatedRiemannKernelReal_nonneg L (t - z))))

/-- The two facing edges cost at most the explicit exponential factor exp(-2/a). -/
theorem truncatedRiemannAutocorr_central_lower_exp_two_edges {L z d a : ℝ}
    (hd : 0 < d) (hz : 0 ≤ z) (ha : 0 < a) (hmargin : z / 2 + d + a ≤ L)
    (hplateau : 1 ≤ L + z / 2 - d) :
    (d * (2 * π ^ 2) ^ 2 / 2) *
      exp (-2 / a - 2 * π * exp (z + 2 * d)) ≤ truncatedRiemannAutocorr L z := by
  have h := smoothTransition_ge_exp_edge ha
  calc
    _ = (2 * d * ((2 * π ^ 2) * (exp (-1 / a) / 2)) ^ 2) *
        exp (-(2 * π * exp (z + 2 * d))) := by
      rw [show -2 / a - 2 * π * exp (z + 2 * d) =
        (-1 / a + -1 / a) + -(2 * π * exp (z + 2 * d)) by ring, exp_add, exp_add]
      ring
    _ ≤ (2 * d * ((2 * π ^ 2) * smoothTransition a) ^ 2) *
        exp (-(2 * π * exp (z + 2 * d))) := by
      gcongr
    _ ≤ _ := truncatedRiemannAutocorr_central_lower_two_edges hd hz hmargin hplateau

end RHTower
