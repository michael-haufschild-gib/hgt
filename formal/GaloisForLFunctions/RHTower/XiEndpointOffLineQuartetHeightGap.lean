import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound

/-!
# Off-line quartet amplification of the Xi endpoint height gap

An off-critical Xi zero has four distinct multiplicity copies under Schwarz conjugation and
critical-line conjugation.  Their endpoint cross charges are equal and nonnegative.  Charging the
whole orbit, rather than one copy, multiplies the endpoint height budget by four and forces every
off-line zero above squared height `85`.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The real endpoint cross charge of one multiplicity copy. -/
def xiEndpointCrossCharge (q : XiZeroCopy) : ℝ :=
  (xiRawReciprocalCoordinate q *
    (starRingEnd ℂ)
      (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re

/-- The endpoint cross charge is invariant under critical-line conjugation. -/
lemma xiEndpointCrossCharge_lineConj (q : XiZeroCopy) :
    xiEndpointCrossCharge (xiZeroCopyLineConjEquiv q) =
      xiEndpointCrossCharge q := by
  rw [xiEndpointCrossCharge, xiEndpointCrossCharge, endpoint_cross_term_re_eq,
    endpoint_cross_term_re_eq]
  change
    ((1 - (starRingEnd ℂ) (q.1 : ℂ)).im ^ 2 +
        (1 - (starRingEnd ℂ) (q.1 : ℂ)).re *
          (1 - (1 - (starRingEnd ℂ) (q.1 : ℂ)).re)) /
      (((1 - (starRingEnd ℂ) (q.1 : ℂ)).re ^ 2 +
          (1 - (starRingEnd ℂ) (q.1 : ℂ)).im ^ 2) *
        ((1 - (1 - (starRingEnd ℂ) (q.1 : ℂ)).re) ^ 2 +
          (1 - (starRingEnd ℂ) (q.1 : ℂ)).im ^ 2)) = _
  simp only [sub_re, sub_im, one_re, one_im, conj_re, conj_im]
  ring

/-- The endpoint cross charge is invariant under ordinary conjugation. -/
lemma xiEndpointCrossCharge_conj (q : XiZeroCopy) :
    xiEndpointCrossCharge (xiZeroCopyConjEquiv q) =
      xiEndpointCrossCharge q := by
  rw [xiEndpointCrossCharge, xiEndpointCrossCharge, endpoint_cross_term_re_eq,
    endpoint_cross_term_re_eq]
  change
    (((starRingEnd ℂ) (q.1 : ℂ)).im ^ 2 +
        ((starRingEnd ℂ) (q.1 : ℂ)).re *
          (1 - ((starRingEnd ℂ) (q.1 : ℂ)).re)) /
      ((((starRingEnd ℂ) (q.1 : ℂ)).re ^ 2 +
          ((starRingEnd ℂ) (q.1 : ℂ)).im ^ 2) *
        ((1 - ((starRingEnd ℂ) (q.1 : ℂ)).re) ^ 2 +
          ((starRingEnd ℂ) (q.1 : ℂ)).im ^ 2)) = _
  simp only [conj_re, conj_im]
  ring

lemma xiZeroCopy_ne_lineConj_of_re_ne_half (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    q ≠ xiZeroCopyLineConjEquiv q := by
  intro h
  have hs := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_lineConj] at hs
  have him := congrArg Complex.im hs
  simp only [conj_im] at him
  have haim : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, mul_im]
  rw [haim] at him
  apply hoff
  linarith

lemma xiZeroCopy_ne_conj (q : XiZeroCopy) :
    q ≠ xiZeroCopyConjEquiv q := by
  intro h
  have hs := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_copyConj] at hs
  have hre := congrArg Complex.re hs
  simp only [neg_re, conj_re] at hre
  have hare : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint, mul_re]
  rw [hare] at hre
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

lemma xiZeroCopy_lineConj_ne_conj (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q ≠ xiZeroCopyConjEquiv q := by
  intro h
  have hs := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_lineConj, xiSpectralPoint_copyConj] at hs
  have hre := congrArg Complex.re hs
  simp only [conj_re, neg_re] at hre
  have hare : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint, mul_re]
  rw [hare] at hre
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

lemma xiZeroCopy_ne_lineConjConj (q : XiZeroCopy) :
    q ≠ xiZeroCopyLineConjEquiv (xiZeroCopyConjEquiv q) := by
  intro h
  have hs := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_lineConj, xiSpectralPoint_copyConj] at hs
  have hre := congrArg Complex.re hs
  simp only [map_neg, neg_re, conj_re] at hre
  have hare : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    simp [xiSpectralPoint, mul_re]
  rw [hare] at hre
  exact xi_divisor_support_im_ne_zero q.1 (by linarith)

lemma xiZeroCopy_lineConj_ne_lineConjConj (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q ≠
      xiZeroCopyLineConjEquiv (xiZeroCopyConjEquiv q) := by
  exact xiZeroCopyLineConjEquiv.injective.ne (xiZeroCopy_ne_conj q)

lemma xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiZeroCopyConjEquiv q ≠
      xiZeroCopyLineConjEquiv (xiZeroCopyConjEquiv q) := by
  exact xiZeroCopy_ne_lineConj_of_re_ne_half (xiZeroCopyConjEquiv q) (by
    simpa using hoff)

/-- The four FE--Schwarz copies of an off-line zero charge at most the full endpoint curvature. -/
theorem four_mul_xiEndpointCrossCharge_le_curvature_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * xiEndpointCrossCharge q ≤ xiEndpointCompletedCurvature := by
  let qJ := xiZeroCopyLineConjEquiv q
  let qC := xiZeroCopyConjEquiv q
  let qCJ := xiZeroCopyLineConjEquiv qC
  let s : Finset XiZeroCopy := {q, qJ, qC, qCJ}
  have hqJ : q ≠ qJ := by
    simpa only [qJ] using xiZeroCopy_ne_lineConj_of_re_ne_half q hoff
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hqCJ : q ≠ qCJ := by
    simpa only [qC, qCJ] using xiZeroCopy_ne_lineConjConj q
  have hqJqC : qJ ≠ qC := by
    simpa only [qJ, qC] using xiZeroCopy_lineConj_ne_conj q
  have hqJqCJ : qJ ≠ qCJ := by
    simpa only [qJ, qC, qCJ] using xiZeroCopy_lineConj_ne_lineConjConj q
  have hqCqCJ : qC ≠ qCJ := by
    simpa only [qC, qCJ] using
      xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half q hoff
  have hsum : Summable xiEndpointCrossCharge := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun j => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hle := hsum.sum_le_tsum s (fun j _ => by
    exact endpoint_cross_term_re_nonneg j)
  have hJ : xiEndpointCrossCharge qJ = xiEndpointCrossCharge q := by
    simpa only [qJ] using xiEndpointCrossCharge_lineConj q
  have hC : xiEndpointCrossCharge qC = xiEndpointCrossCharge q := by
    simpa only [qC] using xiEndpointCrossCharge_conj q
  have hCJ : xiEndpointCrossCharge qCJ = xiEndpointCrossCharge q := by
    calc
      xiEndpointCrossCharge qCJ = xiEndpointCrossCharge qC := by
        simpa only [qC, qCJ] using xiEndpointCrossCharge_lineConj qC
      _ = xiEndpointCrossCharge q := hC
  have hfinite : ∑ j ∈ s, xiEndpointCrossCharge j =
      4 * xiEndpointCrossCharge q := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ]),
      Finset.sum_insert (by simp [hqCqCJ]), Finset.sum_singleton,
      hJ, hC, hCJ]
    ring
  rw [hfinite] at hle
  rw [xiEndpointCompletedCurvature_eq_cross_re,
    Complex.re_tsum summable_xiEndpointCrossTerm]
  simpa only [xiEndpointCrossCharge] using hle

/-- **Exact off-line quartet height law.**  The completed endpoint source pays four units for
every off-critical FE--Schwarz orbit. -/
theorem four_le_curvature_mul_one_add_im_sq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 ≤ xiEndpointCompletedCurvature * ((q.1 : ℂ).im ^ 2 + 1) := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q
  have horbit :=
    four_mul_xiEndpointCrossCharge_le_curvature_of_offLine q hoff
  have hden : 0 < (q.1 : ℂ).im ^ 2 + 1 := by positivity
  have hcharge : 4 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      4 * xiEndpointCrossCharge q := by
    calc
      4 / ((q.1 : ℂ).im ^ 2 + 1) =
          4 * (1 / ((q.1 : ℂ).im ^ 2 + 1)) := by ring
      _ ≤ 4 * xiEndpointCrossCharge q :=
        mul_le_mul_of_nonneg_left hlower (by norm_num)
  have hbudget : 4 / ((q.1 : ℂ).im ^ 2 + 1) ≤
      xiEndpointCompletedCurvature := hcharge.trans horbit
  rwa [div_le_iff₀ hden] at hbudget

/-- **Off-line quartet height amplification.** Every off-critical Xi zero has squared ordinate
strictly greater than `85`. -/
theorem xiZeroCopy_offLine_eightyFive_lt_im_sq (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    85 < (q.1 : ℂ).im ^ 2 := by
  have hbudget := four_le_curvature_mul_one_add_im_sq_of_offLine q hoff
  have hC := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  nlinarith

end

end RHTower
