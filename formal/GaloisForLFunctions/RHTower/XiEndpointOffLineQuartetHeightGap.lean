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

/-- **Quartet mass bound.**  The functional-equation/Schwarz orbit `{q, Jq, Cq, JCq}` of a zero copy
off the critical line has four distinct elements, so any nonnegative summable weight invariant under
both involutions carries at least four times its value at `q`.

This is the source of the factor four in every off-line orbit estimate: the arithmetic input is only
that the orbit is a four-element set, and the analytic input only that the weight is nonnegative,
summable and orbit-invariant. -/
theorem four_mul_le_tsum_of_quartet_invariant
    {f : XiZeroCopy → ℝ} (hnonneg : ∀ r, 0 ≤ f r) (hsum : Summable f)
    (hJinv : ∀ r, f (xiZeroCopyLineConjEquiv r) = f r)
    (hCinv : ∀ r, f (xiZeroCopyConjEquiv r) = f r)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * f q ≤ ∑' r, f r := by
  classical
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
  have hle := hsum.sum_le_tsum s (fun j _ => hnonneg j)
  have hJ : f qJ = f q := by simpa only [qJ] using hJinv q
  have hC : f qC = f q := by simpa only [qC] using hCinv q
  have hCJ : f qCJ = f q := by
    calc f qCJ = f qC := by simpa only [qC, qCJ] using hJinv qC
      _ = f q := hC
  have hfinite : ∑ j ∈ s, f j = 4 * f q := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ]),
      Finset.sum_insert (by simp [hqCqCJ]), Finset.sum_singleton,
      hJ, hC, hCJ]
    ring
  rw [hfinite] at hle
  exact hle

/-- The four FE--Schwarz copies of an off-line zero charge at most the full endpoint curvature. -/
theorem four_mul_xiEndpointCrossCharge_le_curvature_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    4 * xiEndpointCrossCharge q ≤ xiEndpointCompletedCurvature := by
  have hsum : Summable xiEndpointCrossCharge := by
    exact Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm (fun j => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hle := four_mul_le_tsum_of_quartet_invariant
    (fun j => endpoint_cross_term_re_nonneg j) hsum
    xiEndpointCrossCharge_lineConj xiEndpointCrossCharge_conj q hoff
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

/-- **A sector failure is confined to an edge corner.**  A sector certificate `P < A` that holds
both on the inner width region `(Re - 1/2)^2 ≤ c` and above the height `K` leaves only the
complementary window: a point where the certificate fails has width square strictly between `c`
and `1/4`, and ordinate square strictly between `85` and `K`.  The certificate itself is abstract
here, so the same law serves every order and every choice of the auxiliary coordinate. -/
theorem xiZeroCopy_sectorFailure_mem_edgeCorner {P A c K : ℝ} (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ c → P < A)
    (hhigh : K ≤ (q.1 : ℂ).im ^ 2 → P < A) (hfail : A ≤ P) :
    c < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧ ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧ (q.1 : ℂ).im ^ 2 < K := by
  refine ⟨?_, xi_divisor_support_centered_re_sq_lt_quarter q.1,
    xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff, ?_⟩
  · by_contra h
    exact absurd (hinner (not_lt.mp h)) (not_lt.mpr hfail)
  · by_contra h
    exact absurd (hhigh (not_lt.mp h)) (not_lt.mpr hfail)

end

end RHTower
