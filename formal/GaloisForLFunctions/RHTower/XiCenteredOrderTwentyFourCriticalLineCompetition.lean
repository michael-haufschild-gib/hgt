import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure
import GaloisForLFunctions.RHTower.HardyZ

/-!
# Centered order-24 critical-line competition

The order-24 sector certificate leaves a compact possible off-line annulus.  A quartet in this
annulus and a critical-line conjugate pair of squared height below `383` cannot coexist: their six
distinct nonnegative fourth-trace atoms exceed the complete source budget `17 / 200000`.

Consequently, existence of one such low critical-line zero empties the order-24 residual annulus
and advances reciprocal-power positivity, and hence source positivity, by one further order.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private lemma xiZeroCopyLineConj_re_ne_half_of_re_ne_half (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  change (1 - (starRingEnd ℂ) (q.1 : ℂ)).re ≠ 1 / 2
  simp only [sub_re, one_re, conj_re]
  intro heq
  apply h
  linarith

private lemma xiZeroCopyConj_re_ne_half_of_re_ne_half (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyConjEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  change ((starRingEnd ℂ) (q.1 : ℂ)).re ≠ 1 / 2
  simpa only [conj_re] using h

private lemma xiZeroCopy_ne_of_re_ne_half_of_re_eq_half (q r : XiZeroCopy)
    (hq : (q.1 : ℂ).re ≠ 1 / 2) (hr : (r.1 : ℂ).re = 1 / 2) : q ≠ r := by
  intro h
  apply hq
  rw [h]
  exact hr

/-- A four-element off-line FE--Schwarz orbit and a two-element critical-line Schwarz orbit are
disjoint.  Thus any nonnegative summable weight invariant under both symmetries pays for all six
copies simultaneously. -/
theorem four_mul_add_two_mul_le_tsum_of_quartet_and_criticalPair
    {f : XiZeroCopy → ℝ} (hnonneg : ∀ r, 0 ≤ f r) (hsum : Summable f)
    (hJinv : ∀ r, f (xiZeroCopyLineConjEquiv r) = f r)
    (hCinv : ∀ r, f (xiZeroCopyConjEquiv r) = f r)
    (q q0 : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hline : (q0.1 : ℂ).re = 1 / 2) :
    4 * f q + 2 * f q0 ≤ ∑' r, f r := by
  classical
  let qJ := xiZeroCopyLineConjEquiv q
  let qC := xiZeroCopyConjEquiv q
  let qCJ := xiZeroCopyLineConjEquiv qC
  let q0C := xiZeroCopyConjEquiv q0
  let s : Finset XiZeroCopy := {q, qJ, qC, qCJ, q0, q0C}
  have hqJoff : (qJ.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qJ] using xiZeroCopyLineConj_re_ne_half_of_re_ne_half q hoff
  have hqCoff : (qC.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qC] using xiZeroCopyConj_re_ne_half_of_re_ne_half q hoff
  have hqCJoff : (qCJ.1 : ℂ).re ≠ 1 / 2 := by
    simpa only [qC, qCJ] using
      xiZeroCopyLineConj_re_ne_half_of_re_ne_half (xiZeroCopyConjEquiv q)
        (xiZeroCopyConj_re_ne_half_of_re_ne_half q hoff)
  have hq0Cline : (q0C.1 : ℂ).re = 1 / 2 := by
    change ((starRingEnd ℂ) (q0.1 : ℂ)).re = 1 / 2
    simpa only [conj_re] using hline
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
  have hq0q0C : q0 ≠ q0C := by
    simpa only [q0C] using xiZeroCopy_ne_conj q0
  have hqq0 := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half q q0 hoff hline
  have hqq0C := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half q q0C hoff hq0Cline
  have hqJq0 := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qJ q0 hqJoff hline
  have hqJq0C := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qJ q0C hqJoff hq0Cline
  have hqCq0 := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qC q0 hqCoff hline
  have hqCq0C := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qC q0C hqCoff hq0Cline
  have hqCJq0 := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qCJ q0 hqCJoff hline
  have hqCJq0C := xiZeroCopy_ne_of_re_ne_half_of_re_eq_half qCJ q0C hqCJoff hq0Cline
  have hle := hsum.sum_le_tsum s (fun j _ => hnonneg j)
  have hJ : f qJ = f q := by simpa only [qJ] using hJinv q
  have hC : f qC = f q := by simpa only [qC] using hCinv q
  have hCJ : f qCJ = f q := by
    calc
      f qCJ = f qC := by simpa only [qC, qCJ] using hJinv qC
      _ = f q := hC
  have h0C : f q0C = f q0 := by simpa only [q0C] using hCinv q0
  have hfinite : ∑ j ∈ s, f j = 4 * f q + 2 * f q0 := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ, hqq0, hqq0C]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ, hqJq0, hqJq0C]),
      Finset.sum_insert (by simp [hqCqCJ, hqCq0, hqCq0C]),
      Finset.sum_insert (by simp [hqCJq0, hqCJq0C]),
      Finset.sum_insert (by simp [hq0q0C]), Finset.sum_singleton,
      hJ, hC, hCJ, h0C]
    ring
  rw [hfinite] at hle
  exact hle

theorem orderTwentyFourReciprocalPower_re_pos_of_sectorRatio
    {A B : ℝ} (hA : 0 < A) (hsector : 234 * B ^ 2 < A ^ 2) :
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 24).re :=
  GaloisForLFunctions.HTGeometry.re_inv_sub_mul_I_pow_pos_of_sq_lt
    (t := 327 / 5000) hA (by norm_num) (by norm_num) hsector
    (by norm_num; nlinarith [Real.pi_gt_d20])

theorem xiCenteredOrderTwentyFourSectorRatio_of_offLine_inner
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hinner : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ (2365 / 15008 : ℝ)) :
    234 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  have hv : (2365 / 16 : ℝ) ≤ (q.1 : ℂ).im ^ 2 :=
    le_of_not_gt fun hvlt => hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q hvlt)
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 234)
      (u₀ := 2365 / 15008) (v₀ := 2365 / 16) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl hinner hv (by norm_num) (by norm_num)

theorem xiCenteredOrderTwentyFourSectorRatio_of_fourHundredSixtyNineHalves_le_im_sq
    (q : XiZeroCopy) (hhigh : 469 / 2 ≤ (q.1 : ℂ).im ^ 2) :
    234 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  simpa only [add_zero] using
    GaloisForLFunctions.HTGeometry.sector_ratio_of_corner (N := 234)
      (u₀ := 1 / 4) (v₀ := 469 / 2) (y₀ := 0) (y := 0)
      (by norm_num) le_rfl
      (xi_divisor_support_centered_re_sq_lt_quarter q.1).le hhigh
      (by norm_num) (by norm_num)

def XiCenteredOrderTwentyFourResidualAnnulus (q : XiZeroCopy) : Prop :=
  (q.1 : ℂ).re ≠ 1 / 2 ∧
    (2365 / 15008 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
        2365 / 16 ≤ (q.1 : ℂ).im ^ 2 ∧
          (q.1 : ℂ).im ^ 2 < 469 / 2

theorem xiCenteredOrderTwentyFourSectorFailure_mem_residualAnnulus
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (hfail :
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 ≤
        234 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2) :
    XiCenteredOrderTwentyFourResidualAnnulus q := by
  refine ⟨hoff, ?_, xi_divisor_support_centered_re_sq_lt_quarter q.1, ?_, ?_⟩
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyFourSectorRatio_of_offLine_inner q hoff (not_lt.mp h))
      (not_lt.mpr hfail)
  · by_contra h
    exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (not_le.mp h))
  · by_contra h
    exact absurd
      (xiCenteredOrderTwentyFourSectorRatio_of_fourHundredSixtyNineHalves_le_im_sq q
        (not_lt.mp h))
      (not_lt.mpr hfail)

theorem xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_not_mem_residualAnnulus
    (q : XiZeroCopy) (hnot : ¬ XiCenteredOrderTwentyFourResidualAnnulus q) :
    0 < (xiZeroCopyReciprocalSquare q ^ 24).re :=
  xiZeroCopyReciprocalSquare_pow_re_pos_of_window_empty q
    (fun _ _ hA h => orderTwentyFourReciprocalPower_re_pos_of_sectorRatio hA h)
    (fun hoff hfail => xiCenteredOrderTwentyFourSectorFailure_mem_residualAnnulus q hoff hfail)
    hnot

/-- Every fourth-trace atom in the order-24 residual annulus exceeds `1 / 56000`. -/
theorem one_over_fiftySixThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyFour
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 469 / 2) :
    (1 / 56000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 939 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 469 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ 2 < w ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < W ^ 2 + w ^ 2 - 56000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      56000 * W ^ 2 - W ^ 4 < 56000 * w ^ 2 - w ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (56000 * w ^ 2 - w ^ 4) - (56000 * W ^ 2 - W ^ 4) =
          (W ^ 2 - w ^ 2) * (W ^ 2 + w ^ 2 - 56000) := by
      ring
    nlinarith
  have huv : u * v < 469 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (469 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 469 / 8 := by ring
  have hendpoint :
      448000 * (469 / 8 : ℝ) < 56000 * W ^ 2 - W ^ 4 := by
    norm_num [W]
  have huvScaled : 448000 * (u * v) < 448000 * (469 / 8 : ℝ) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain : 448000 * (u * v) < 56000 * w ^ 2 - w ^ 4 :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 56000 * (v ^ 2 - 6 * u * v + u ^ 2) - w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith [hchain]
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 56000) (pow_pos hw0 4)]
  nlinarith

/-- A critical-line copy below squared height `383` contributes more than `1 / 383^2` to the
fourth reciprocal trace. -/
theorem one_over_threeHundredEightyThree_sq_lt_xiFourthReciprocalTraceAtom_of_criticalLine
    (q0 : XiZeroCopy) (hline : (q0.1 : ℂ).re = 1 / 2)
    (hheight : (q0.1 : ℂ).im ^ 2 < 383) :
    (1 / (383 : ℝ) ^ 2) < (xiZeroCopyReciprocalSquare q0 ^ 2).re := by
  let v : ℝ := (q0.1 : ℂ).im ^ 2
  have hv0 : 0 < v := by
    dsimp only [v]
    exact sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q0.1)
  have hvU : v < 383 := by simpa only [v] using hheight
  have hformula :
      (xiZeroCopyReciprocalSquare q0 ^ 2).re = v ^ 2 / v ^ 4 := by
    simp only [v]
    rw [xiZeroCopyReciprocalSquare_sq_re_formula, hline]
    norm_num
  rw [hformula]
  have hvSq : v ^ 2 < (383 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hv0.le (by norm_num)).2 hvU
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (383 : ℝ) ^ 2)
    (pow_pos hv0 4)]
  have hv2 : 0 < v ^ 2 := pow_pos hv0 2
  nlinarith

/-- An order-24 residual quartet cannot coexist with a critical-line pair below squared height
`383`; the six atoms would overspend the exact fourth-trace source budget. -/
theorem not_orderTwentyFourResidualAnnulus_of_criticalLine_below_threeHundredEightyThree
    (q0 : XiZeroCopy) (hline : (q0.1 : ℂ).re = 1 / 2)
    (hheight : (q0.1 : ℂ).im ^ 2 < 383) :
    ¬ ∃ q : XiZeroCopy, XiCenteredOrderTwentyFourResidualAnnulus q := by
  rintro ⟨q, hq⟩
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hmass := four_mul_add_two_mul_le_tsum_of_quartet_and_criticalPair
    xiFourthReciprocalTraceAtom_nonneg hsum xiFourthReciprocalTraceAtom_lineConj
      xiFourthReciprocalTraceAtom_conj q q0 hq.1 hline
  rw [tsum_xiFourthReciprocalTraceAtom_eq_source] at hmass
  have hquartet :=
    one_over_fiftySixThousand_lt_xiFourthReciprocalTraceAtom_orderTwentyFour
      q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  have hpair :=
    one_over_threeHundredEightyThree_sq_lt_xiFourthReciprocalTraceAtom_of_criticalLine
      q0 hline hheight
  have hupper := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have hrat :
      (17 / 200000 : ℝ) < 4 * (1 / 56000 : ℝ) + 2 * (1 / (383 : ℝ) ^ 2) := by
    norm_num
  nlinarith

/-- Reverse form of the competition law: any surviving order-24 off-line obstruction forces a
critical-line zero-free band through squared height `383`. -/
theorem threeHundredEightyThree_le_criticalLine_im_sq_of_orderTwentyFourResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyFourResidualAnnulus q)
    (q0 : XiZeroCopy) (hline : (q0.1 : ℂ).re = 1 / 2) :
    (383 : ℝ) ≤ (q0.1 : ℂ).im ^ 2 := by
  by_contra hnot
  exact not_orderTwentyFourResidualAnnulus_of_criticalLine_below_threeHundredEightyThree
    q0 hline (lt_of_not_ge hnot) ⟨q, hq⟩

theorem xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_criticalLine_below_threeHundredEightyThree
    (q0 : XiZeroCopy) (hline : (q0.1 : ℂ).re = 1 / 2)
    (hheight : (q0.1 : ℂ).im ^ 2 < 383) (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 24).re :=
  xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_not_mem_residualAnnulus q
    (fun hq =>
      not_orderTwentyFourResidualAnnulus_of_criticalLine_below_threeHundredEightyThree
        q0 hline hheight ⟨q, hq⟩)

/-- One low critical-line zero forces positivity of centered source moment 23. -/
theorem normalizedPrimeArchMoment_twentyThree_pos_of_criticalLine_below_threeHundredEightyThree
    (q0 : XiZeroCopy) (hline : (q0.1 : ℂ).re = 1 / 2)
    (hheight : (q0.1 : ℂ).im ^ 2 < 383) :
    0 < normalizedPrimeArchMoment 23 := by
  apply normalizedPrimeArchMoment_pos_of_atomwise_re_pos 23
  simpa using
    xiZeroCopyReciprocalSquare_pow_twentyFour_re_pos_of_criticalLine_below_threeHundredEightyThree
      q0 hline hheight

/-- Hardy-route interface: any certified Hardy zero of squared height below `383` closes the
order-24 centered source moment. -/
theorem normalizedPrimeArchMoment_twentyThree_pos_of_hardyZ_zero_below_threeHundredEightyThree
    {τ : ℝ} (hZ : hardyZ τ = 0) (hheight : τ ^ 2 < 383) :
    0 < normalizedPrimeArchMoment 23 := by
  have hxi : xi (linePt τ) = 0 := (xi_line_eq_zero_iff_hardyZ τ).2 hZ
  let rho : XiDivisorSupport :=
    ⟨linePt τ, mem_xi_divisor_support_of_eq_zero hxi⟩
  let q0 : XiZeroCopy := by
    have hpos := xi_divisor_pos_on_support rho
    have hn : 0 < Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    exact ⟨rho, ⟨0, hn⟩⟩
  apply normalizedPrimeArchMoment_twentyThree_pos_of_criticalLine_below_threeHundredEightyThree
    q0
  · change (linePt τ).re = 1 / 2
    exact linePt_re τ
  · change (linePt τ).im ^ 2 < 383
    simpa only [linePt_im] using hheight

end

end RHTower
