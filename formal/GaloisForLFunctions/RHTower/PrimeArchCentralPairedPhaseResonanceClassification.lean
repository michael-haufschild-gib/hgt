import GaloisForLFunctions.RHTower.PrimeArchCentralPairedFourthTraceBand

/-!
# Exact Route-Q atomwise phase resonance classification

A line-conjugate reciprocal-square pair has nonnegative upper-quadrant phase when its
Xi zero lies on the critical line.  Conversely, each off-line zero copy has an
upper-strip point avoiding both pair poles where that literal pair has negative imaginary response.
The proof uses the order-23 source sector ratio, the exact paired denominator, and a
small transverse perturbation of its real resonance.  This classifies the atomwise
all-strip sign; it does not bound the complete signed trace or prove RH.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private def pairedBarrier (w lam : ℂ) : ℝ :=
  Complex.normSq lam *
      ((1 - w.re * lam.re) ^ (2 : ℕ) + (w.re * lam.im) ^ (2 : ℕ) +
        w.im ^ (2 : ℕ) * Complex.normSq lam) -
    2 * lam.im ^ (2 : ℕ)

private theorem pairedBarrier_resonance_eq (lam : ℂ) (ha : lam.re ≠ 0) :
    lam.re ^ (2 : ℕ) * pairedBarrier ((1 / lam.re : ℝ) : ℂ) lam =
      lam.im ^ (2 : ℕ) * (lam.im ^ (2 : ℕ) - lam.re ^ (2 : ℕ)) := by
  unfold pairedBarrier
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  field_simp [ha]
  ring

private theorem pairedBarrier_resonance_neg (lam : ℂ)
    (ha : 0 < lam.re) (hb : lam.im ≠ 0)
    (hphase : lam.im ^ (2 : ℕ) < lam.re ^ (2 : ℕ)) :
    pairedBarrier ((1 / lam.re : ℝ) : ℂ) lam < 0 := by
  have h := pairedBarrier_resonance_eq lam ha.ne'
  have hpos : 0 < lam.re ^ (2 : ℕ) := sq_pos_of_pos ha
  have hneg : lam.im ^ (2 : ℕ) *
      (lam.im ^ (2 : ℕ) - lam.re ^ (2 : ℕ)) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hb) (sub_neg.mpr hphase)
  nlinarith only [h, hpos, hneg]

private theorem pairedBarrier_continuous (lam : ℂ) :
    Continuous (fun w : ℂ => pairedBarrier w lam) := by
  unfold pairedBarrier
  fun_prop

private theorem paired_response_negative_near_resonance (lam : ℂ)
    (ha : 0 < lam.re) (hb : lam.im ≠ 0)
    (hphase : lam.im ^ (2 : ℕ) < lam.re ^ (2 : ℕ)) :
    ∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 ∧
      1 - z ^ (2 : ℕ) * lam ≠ 0 ∧
      1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 ∧
      (lam / (1 - z ^ (2 : ℕ) * lam) +
        (starRingEnd ℂ) lam /
          (1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam)).im < 0 := by
  let x : ℝ := Real.sqrt (1 / lam.re)
  let z : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * I
  have hxpos : 0 < x := Real.sqrt_pos.2 (one_div_pos.2 ha)
  have hx : x ^ (2 : ℕ) = 1 / lam.re := Real.sq_sqrt (one_div_pos.2 ha).le
  have hz0 : z 0 ^ (2 : ℕ) = ((1 / lam.re : ℝ) : ℂ) := by
    have hzero : z 0 = (x : ℂ) := by simp [z]
    rw [hzero, ← Complex.ofReal_pow, hx]
  have hbar0 : pairedBarrier (z 0 ^ (2 : ℕ)) lam < 0 := by
    rw [hz0]
    exact pairedBarrier_resonance_neg lam ha hb hphase
  have hden0 : 1 - z 0 ^ (2 : ℕ) * lam ≠ 0 := by
    rw [hz0]
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im] at hi
    have ha0 : 1 / lam.re ≠ 0 := (one_div_pos.2 ha).ne'
    have hmul : (1 / lam.re) * lam.im = 0 := by linarith only [hi]
    exact hb ((mul_eq_zero.mp hmul).resolve_left ha0)
  have hdenconj0 : 1 - z 0 ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 := by
    rw [hz0]
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, Complex.conj_im] at hi
    have ha0 : 1 / lam.re ≠ 0 := (one_div_pos.2 ha).ne'
    have hmul : (1 / lam.re) * -lam.im = 0 := by linarith only [hi]
    exact hb (neg_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha0))
  have hzcont : Continuous z := by
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hbarcont : ContinuousAt (fun y : ℝ => pairedBarrier (z y ^ (2 : ℕ)) lam) 0 :=
    ((pairedBarrier_continuous lam).comp (hzcont.pow 2)).continuousAt
  have hdencont : ContinuousAt (fun y : ℝ => 1 - z y ^ (2 : ℕ) * lam) 0 := by
    exact (continuous_const.sub ((hzcont.pow 2).mul continuous_const)).continuousAt
  have hdenconjcont : ContinuousAt
      (fun y : ℝ => 1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam) 0 := by
    exact (continuous_const.sub ((hzcont.pow 2).mul continuous_const)).continuousAt
  have hev : ∀ᶠ y : ℝ in 𝓝 0,
      pairedBarrier (z y ^ (2 : ℕ)) lam < 0 ∧
      1 - z y ^ (2 : ℕ) * lam ≠ 0 ∧
      1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 :=
    (hbarcont.eventually (eventually_lt_nhds hbar0)).and
      ((hdencont.eventually (eventually_ne_nhds hden0)).and
        (hdenconjcont.eventually (eventually_ne_nhds hdenconj0)))
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let y : ℝ := min (ε / 2) (1 / 4)
  have hypos : 0 < y := lt_min (half_pos hε) (by norm_num)
  have hyhalf : y < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hydist : dist y (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
    have hyle : y ≤ ε / 2 := min_le_left _ _
    linarith
  obtain ⟨hbar, hden, hdenconj⟩ := hnear hydist
  have hzre : (z y).re = x := by simp [z]
  have hzim : (z y).im = y := by simp [z]
  refine ⟨z y, ?_, ?_, ?_, hden, hdenconj, ?_⟩
  · simpa only [hzre] using hxpos
  · simpa only [hzim] using hypos
  · simpa only [hzim] using hyhalf
  have hwim : 0 < (z y ^ (2 : ℕ)).im := by
    rw [pow_two, Complex.mul_im, hzre, hzim]
    nlinarith [mul_pos hxpos hypos]
  have hdenpos : 0 < Complex.normSq (1 - z y ^ (2 : ℕ) * lam) :=
    Complex.normSq_pos.mpr hden
  have hdenconjpos : 0 < Complex.normSq
      (1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam) :=
    Complex.normSq_pos.mpr hdenconj
  rw [centralPaired_reciprocalSquare_lineConj_pair_im_formula
    (z y ^ (2 : ℕ)) lam hden hdenconj]
  change 2 * (z y ^ (2 : ℕ)).im * pairedBarrier (z y ^ (2 : ℕ)) lam /
    (Complex.normSq (1 - z y ^ (2 : ℕ) * lam) *
      Complex.normSq (1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam)) < 0
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hbar)
    (mul_pos hdenpos hdenconjpos)

private theorem paired_response_nonneg_of_real_parameter
    (lam z : ℂ) (hb : lam.im = 0)
    (hzre : 0 < z.re) (hzim : 0 < z.im)
    (hden : 1 - z ^ (2 : ℕ) * lam ≠ 0)
    (hdenconj : 1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0) :
    0 ≤ (lam / (1 - z ^ (2 : ℕ) * lam) +
      (starRingEnd ℂ) lam /
        (1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam)).im := by
  have hwim : 0 ≤ (z ^ (2 : ℕ)).im := by
    rw [pow_two, Complex.mul_im]
    nlinarith [mul_pos hzre hzim]
  have hbar : 0 ≤ pairedBarrier (z ^ (2 : ℕ)) lam := by
    unfold pairedBarrier
    rw [hb]
    simp only [show (0 : ℝ) ^ (2 : ℕ) = 0 by ring,
      mul_zero, add_zero, sub_zero]
    apply mul_nonneg (Complex.normSq_nonneg _)
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  exact centralPaired_lineConj_pair_im_nonneg_of_barrier
    (z ^ (2 : ℕ)) lam hden hdenconj hwim hbar

private theorem xiZeroCopyReciprocalSquare_im_ne_zero_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
  rw [xiZeroCopyReciprocalSquare_im_formula]
  have hd : (q.1 : ℂ).re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hoff
  have ht : (q.1 : ℂ).im ≠ 0 := xi_divisor_support_im_ne_zero q.1
  have hD : 0 <
      (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) +
        (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ) := by
    have ht2 : 0 < (q.1 : ℂ).im ^ (2 : ℕ) := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hd) ht) hD.ne'

theorem xiZeroCopy_offLine_iff_exists_negative_lineConj_pair_phase
    (q : XiZeroCopy) :
    ((q.1 : ℂ).re ≠ 1 / 2) ↔
      ∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 ∧
        1 - z ^ (2 : ℕ) * xiZeroCopyReciprocalSquare q ≠ 0 ∧
        1 - z ^ (2 : ℕ) *
          xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) ≠ 0 ∧
        (xiReciprocalSquareResolventTerm z q +
          xiReciprocalSquareResolventTerm z (xiZeroCopyLineConjEquiv q)).im < 0 := by
  constructor
  · intro hoff
    let lam := xiZeroCopyReciprocalSquare q
    have ha : 0 < lam.re := by
      simpa only [lam, xiThermalNode] using xiThermalNode_pos q
    have hb : lam.im ≠ 0 := by
      simpa only [lam] using xiZeroCopyReciprocalSquare_im_ne_zero_of_offLine q hoff
    have hphase : lam.im ^ (2 : ℕ) < lam.re ^ (2 : ℕ) := by
      have hr := xiZeroCopyReciprocalSquare_orderTwentyThree_orientation_sq_lt q hoff
      have ha2 : 0 < lam.re ^ (2 : ℕ) := sq_pos_of_pos ha
      change lam.im ^ (2 : ℕ) < (1 / 215 : ℝ) * lam.re ^ (2 : ℕ) at hr
      nlinarith [hr, ha2]
    obtain ⟨z, hzre, hzim, hzimUpper, hden, hdenconj, hneg⟩ :=
      paired_response_negative_near_resonance lam ha hb hphase
    refine ⟨z, hzre, hzim, hzimUpper, hden, ?_, ?_⟩
    · simpa only [lam, centralPaired_lineConj_reciprocalSquare] using hdenconj
    · simpa only [xiReciprocalSquareResolventTerm,
        centralPaired_lineConj_reciprocalSquare, lam] using hneg
  · rintro ⟨z, hzre, hzim, _hzimUpper, hden, hdenconj, hneg⟩
    intro hline
    let lam := xiZeroCopyReciprocalSquare q
    have hb : lam.im = 0 := by
      dsimp only [lam]
      rw [xiZeroCopyReciprocalSquare_im_formula, hline]
      ring
    have hnonneg := paired_response_nonneg_of_real_parameter lam z hb
      hzre hzim hden
      (by simpa only [lam, centralPaired_lineConj_reciprocalSquare] using hdenconj)
    have hneg' :
        (lam / (1 - z ^ (2 : ℕ) * lam) +
          (starRingEnd ℂ) lam /
            (1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam)).im < 0 := by
      simpa only [xiReciprocalSquareResolventTerm,
        centralPaired_lineConj_reciprocalSquare, lam] using hneg
    exact (not_lt_of_ge hnonneg) hneg'

end
end RHTower
