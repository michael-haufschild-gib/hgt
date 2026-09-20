import GaloisForLFunctions.RHTower.XiPositivePairedDiagonalSectorCollapse
import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.PrimeArchPositivePairedDiagonalExteriorOverlap
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw

/-!
# Central line-conjugate phase pairing for Route Q

The positive paired diagonal is a complex-phase statement.  Its previous exterior certificate
started at `701 / 100`.  Here each literal reciprocal-square atom is paired with its
line-conjugate copy before summation.  The pair has an exact imaginary-part formula.  The
unconditional off-line height and order-23 orientation bounds leave a positive scalar margin
for `0 < re z ≤ 218 / 25`; line atoms are positive directly.  Absolute summability then transfers
this cancellation-preserving atom law to the actual continued prime--Gamma trace.
-/

open Complex

namespace RHTower

noncomputable section

private theorem lineConj_reciprocalSquare (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  simp [xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj, map_inv₀]

/-- Exact imaginary part of a reciprocal-square atom and its line-conjugate partner. -/
private theorem reciprocalSquare_lineConj_pair_im_formula
    (w lam : ℂ) (h : 1 - w * lam ≠ 0)
    (hc : 1 - w * (starRingEnd ℂ) lam ≠ 0) :
    (lam / (1 - w * lam) + (starRingEnd ℂ) lam /
        (1 - w * (starRingEnd ℂ) lam)).im =
      (2 * w.im *
          (Complex.normSq lam *
              ((1 - w.re * lam.re) ^ 2 + (w.re * lam.im) ^ 2 +
                w.im ^ 2 * Complex.normSq lam) -
            2 * lam.im ^ 2)) /
        (Complex.normSq (1 - w * lam) *
          Complex.normSq (1 - w * (starRingEnd ℂ) lam)) := by
  have hn : Complex.normSq (1 - w * lam) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr h)
  have hnc : Complex.normSq (1 - w * (starRingEnd ℂ) lam) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr hc)
  rw [Complex.add_im, Complex.div_im, Complex.div_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  simp only [Complex.one_re, Complex.one_im, zero_sub]
  field_simp [hn, hnc]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, zero_sub]
  ring

private theorem reciprocalSquare_re_le_inv_ordinate_sq
    (q : XiZeroCopy) (ht : 0 < (q.1 : ℂ).im ^ 2) :
    (xiZeroCopyReciprocalSquare q).re ≤ 1 / (q.1 : ℂ).im ^ 2 := by
  rw [xiZeroCopyReciprocalSquare_re_formula]
  set d : ℝ := (q.1 : ℂ).re - 1 / 2
  set t : ℝ := (q.1 : ℂ).im
  have hD : 0 < (d ^ 2 + t ^ 2) ^ 2 := by
    have : 0 < d ^ 2 + t ^ 2 := by
      dsimp only [d, t]
      nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
    positivity
  have ht' : 0 < t ^ 2 := by simpa only [t] using ht
  change (t ^ 2 - d ^ 2) / (d ^ 2 + t ^ 2) ^ 2 ≤ 1 / t ^ 2
  apply (div_le_div_iff₀ hD ht').mpr
  nlinarith [sq_nonneg (d ^ 2), mul_nonneg (sq_nonneg d) (sq_nonneg t)]

/-- The certified off-line height and orientation corridor leave a uniform phase margin for
the paired reciprocal-square atom throughout the central Route-Q band. -/
private theorem reciprocalSquare_central_pair_gap
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (2 / 215 : ℝ) <
      (1 - (xiZeroCopyReciprocalSquare q).re * (z ^ 2).re) ^ 2 := by
  let a : ℝ := (xiZeroCopyReciprocalSquare q).re
  let t : ℝ := (q.1 : ℂ).im
  let u : ℝ := (z ^ 2).re
  have ha : 0 < a := by
    simpa only [a, xiThermalNode] using xiThermalNode_pos q
  have ht : (7907 / 93 : ℝ) < t ^ 2 := by
    simpa only [t] using
      xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq q hoff
  have ht0 : 0 < t ^ 2 := by linarith
  have hare : a ≤ 1 / t ^ 2 := by
    simpa only [a, t] using
      reciprocalSquare_re_le_inv_ordinate_sq q ht0
  have hu : u ≤ z.re ^ 2 := by
    dsimp only [u]
    rw [pow_two]
    simp only [Complex.mul_re]
    nlinarith [sq_nonneg z.im]
  have hau : a * u ≤ a * z.re ^ 2 :=
    mul_le_mul_of_nonneg_left hu ha.le
  have hzr : z.re ^ 2 ≤ (218 / 25 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (z.re + 218 / 25)]
  have haR : a * (218 / 25 : ℝ) ^ 2 <
      (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ) := by
    have hmul : a * t ^ 2 ≤ 1 := by
      calc
        a * t ^ 2 ≤ (1 / t ^ 2) * t ^ 2 :=
          mul_le_mul_of_nonneg_right hare ht0.le
        _ = 1 := by
          have htne : t ≠ 0 := by
            intro h
            subst t
            norm_num at ht0
          field_simp [htne]
    have hAt : a * (218 / 25 : ℝ) ^ 2 * t ^ 2 ≤
        (218 / 25 : ℝ) ^ 2 := by
      calc
        a * (218 / 25 : ℝ) ^ 2 * t ^ 2 =
            (218 / 25 : ℝ) ^ 2 * (a * t ^ 2) := by ring
        _ ≤ (218 / 25 : ℝ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hmul (sq_nonneg _)
        _ = (218 / 25 : ℝ) ^ 2 := by ring
    have hpos : 0 < a * (218 / 25 : ℝ) ^ 2 := by positivity
    have hprod : a * (218 / 25 : ℝ) ^ 2 * (7907 / 93 : ℝ) <
        a * (218 / 25 : ℝ) ^ 2 * t ^ 2 := by
      exact mul_lt_mul_of_pos_left ht hpos
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 7907 / 93)).mpr
    exact hprod.trans_le hAt
  have hauR : a * u < (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ) := by
    calc
      a * u ≤ a * z.re ^ 2 := hau
      _ ≤ a * (218 / 25 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hzr ha.le
      _ < (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ) := haR
  have hratio : (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ) < 1 := by norm_num
  have hmargin : (2 / 215 : ℝ) <
      (1 - (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ)) ^ 2 := by norm_num
  change (2 / 215 : ℝ) < (1 - a * u) ^ 2
  nlinarith [sq_nonneg ((1 - a * u) +
    (1 - (218 / 25 : ℝ) ^ 2 / (7907 / 93 : ℝ)))]

private theorem reciprocalSquare_pair_barrier_pos
    {a b u v : ℝ} (ha : 0 < a)
    (hphase : b ^ 2 < (1 / 215 : ℝ) * a ^ 2)
    (hgap : (2 / 215 : ℝ) < (1 - a * u) ^ 2) :
    0 < (a ^ 2 + b ^ 2) *
          ((1 - a * u) ^ 2 + (u * b) ^ 2 + v ^ 2 * (a ^ 2 + b ^ 2)) -
        2 * b ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hc : a ^ 2 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg b]
  have hD : (1 - a * u) ^ 2 ≤
      (1 - a * u) ^ 2 + (u * b) ^ 2 + v ^ 2 * (a ^ 2 + b ^ 2) := by
    have hmass : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    nlinarith [sq_nonneg (u * b), sq_nonneg v]
  have htwo : 2 * b ^ 2 < (2 / 215 : ℝ) * a ^ 2 := by
    nlinarith
  have hmid : (2 / 215 : ℝ) * a ^ 2 < (1 - a * u) ^ 2 * a ^ 2 :=
    mul_lt_mul_of_pos_right hgap ha2
  have hright : (1 - a * u) ^ 2 * a ^ 2 ≤
      (a ^ 2 + b ^ 2) *
        ((1 - a * u) ^ 2 + (u * b) ^ 2 + v ^ 2 * (a ^ 2 + b ^ 2)) := by
    calc
      (1 - a * u) ^ 2 * a ^ 2 ≤ (1 - a * u) ^ 2 * (a ^ 2 + b ^ 2) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = (a ^ 2 + b ^ 2) * (1 - a * u) ^ 2 := by ring
      _ ≤ (a ^ 2 + b ^ 2) *
          ((1 - a * u) ^ 2 + (u * b) ^ 2 + v ^ 2 * (a ^ 2 + b ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hD (by positivity)
  linarith

private theorem reciprocalSquare_lineConj_pair_im_nonneg_of_barrier
    (w lam : ℂ) (h : 1 - w * lam ≠ 0)
    (hc : 1 - w * (starRingEnd ℂ) lam ≠ 0)
    (hwim : 0 ≤ w.im)
    (hbarrier : 0 ≤
      Complex.normSq lam *
          ((1 - w.re * lam.re) ^ 2 + (w.re * lam.im) ^ 2 +
            w.im ^ 2 * Complex.normSq lam) -
        2 * lam.im ^ 2) :
    0 ≤ (lam / (1 - w * lam) + (starRingEnd ℂ) lam /
        (1 - w * (starRingEnd ℂ) lam)).im := by
  rw [reciprocalSquare_lineConj_pair_im_formula w lam h hc]
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hwim) hbarrier
  · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- Every literal line-conjugate pair has nonnegative Route-Q imaginary response in the central
band.  This is the cancellation law that is unavailable from individual complex atoms. -/
theorem xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_central
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (hzim : 0 < z.im) (q : XiZeroCopy) (hXi : XiC z ≠ 0) :
    0 ≤ (xiReciprocalSquareResolventTerm z q +
      xiReciprocalSquareResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let lam : ℂ := xiZeroCopyReciprocalSquare q
  have hden : 1 - z ^ 2 * lam ≠ 0 := by
    dsimp only [lam]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi q
  have hdenconj : 1 - z ^ 2 * (starRingEnd ℂ) lam ≠ 0 := by
    dsimp only [lam]
    rw [← lineConj_reciprocalSquare q]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi
      (xiZeroCopyLineConjEquiv q)
  have hwim : 0 ≤ (z ^ 2).im := by
    rw [pow_two]
    simp only [Complex.mul_im]
    exact (add_pos (mul_pos hzre hzim) (mul_pos hzim hzre)).le
  have hbarrier : 0 ≤
      Complex.normSq lam *
          ((1 - (z ^ 2).re * lam.re) ^ 2 + ((z ^ 2).re * lam.im) ^ 2 +
            (z ^ 2).im ^ 2 * Complex.normSq lam) -
        2 * lam.im ^ 2 := by
    by_cases hoff : (q.1 : ℂ).re = 1 / 2
    · have him : lam.im = 0 := by
        dsimp only [lam]
        rw [xiZeroCopyReciprocalSquare_im_formula, hoff]
        norm_num
      rw [him]
      have hnonneg : 0 ≤ Complex.normSq lam *
          ((1 - (z ^ 2).re * lam.re) ^ 2 +
            (z ^ 2).im ^ 2 * Complex.normSq lam) :=
        mul_nonneg (Complex.normSq_nonneg _)
          (add_nonneg (sq_nonneg _)
            (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)))
      nlinarith
    · have ha : 0 < lam.re := by
        simpa only [lam, xiThermalNode] using xiThermalNode_pos q
      have hphase : lam.im ^ 2 < (1 / 215 : ℝ) * lam.re ^ 2 := by
        simpa only [lam] using
          xiZeroCopyReciprocalSquare_orderTwentyThree_orientation_sq_lt q hoff
      have hgap : (2 / 215 : ℝ) <
          (1 - lam.re * (z ^ 2).re) ^ 2 := by
        simpa only [lam] using
          reciprocalSquare_central_pair_gap z hzre hzreUpper q hoff
      have hpositive := reciprocalSquare_pair_barrier_pos ha hphase hgap
      simpa only [Complex.normSq_apply] using hpositive.le
  rw [xiReciprocalSquareResolventTerm, xiReciprocalSquareResolventTerm,
    lineConj_reciprocalSquare q]
  exact reciprocalSquare_lineConj_pair_im_nonneg_of_barrier
    (z ^ 2) lam hden hdenconj hwim hbarrier

private theorem tsum_im_nonneg_of_lineConj_pairs
    (f : XiZeroCopy → ℂ) (hsum : Summable f)
    (hpair : ∀ q : XiZeroCopy,
      0 ≤ (f q + f (xiZeroCopyLineConjEquiv q)).im) :
    0 ≤ (∑' q : XiZeroCopy, f q).im := by
  have hsumJ : Summable (fun q : XiZeroCopy =>
      f (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hreindex :
      (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q)) =
        ∑' q : XiZeroCopy, f q :=
    xiZeroCopyLineConjEquiv.tsum_eq f
  have hpairsum :
      (∑' q : XiZeroCopy,
          (f q + f (xiZeroCopyLineConjEquiv q))) =
        2 * ∑' q : XiZeroCopy, f q := by
    rw [hsum.tsum_add hsumJ, hreindex]
    ring
  have hpairsumIm := congrArg Complex.im hpairsum
  rw [Complex.im_tsum hpairs] at hpairsumIm
  norm_num [mul_im] at hpairsumIm
  have hpairsumIm' :
      (∑' q : XiZeroCopy,
          (f q + f (xiZeroCopyLineConjEquiv q)).im) =
        2 * (∑' q : XiZeroCopy, f q).im := by
    simpa only [Complex.add_im] using hpairsumIm
  have hpairsign :
      0 ≤ ∑' q : XiZeroCopy,
        (f q + f (xiZeroCopyLineConjEquiv q)).im :=
    tsum_nonneg hpair
  rw [hpairsumIm'] at hpairsign
  linarith

/-- The actual continued prime--Gamma reciprocal-square trace has nonnegative sector phase on
the central Route-Q band. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_nonneg_central
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 ≤ (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 := by
    change xi (1 / 2 + z * I) ≠ 0
    exact (xi_eq_zero_iff hspos hs1).not.mpr hzeta
  rw [continuedPrimeArchReciprocalSquareTrace_eq_tsum hzim hzimUpper hzeta]
  exact tsum_im_nonneg_of_lineConj_pairs
    (xiReciprocalSquareResolventTerm z)
    (summable_xiReciprocalSquareResolventTerm hXi)
    (fun q =>
      xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_central
        z hzre hzreUpper hzim q hXi)

/-- Route Q is nonnegative on the central positive paired diagonal. -/
theorem ccmPositivePairedReducedKernel_self_nonneg_central
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 ≤ ccmPositivePairedReducedKernel z z := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  exact mul_nonneg
    (mul_nonneg (by norm_num) (div_nonneg hzre.le hzim.le))
    (continuedPrimeArchReciprocalSquareTrace_im_nonneg_central
      z hzre hzreUpper hzim hzimUpper hzeta)

/-- The central line-conjugate law and the order-23 exterior overlap certificate join without a
gap: Route Q is nonnegative from the origin through `1047 / 100`. -/
theorem ccmPositivePairedReducedKernel_self_nonneg_through_orderTwentyThreeOverlap
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 1047 / 100)
    (hzim : 0 < z.im) (hzimUpper : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 ≤ ccmPositivePairedReducedKernel z z := by
  by_cases hcentral : z.re ≤ 218 / 25
  · exact ccmPositivePairedReducedKernel_self_nonneg_central
      z hzre hcentral hzim hzimUpper hzeta
  · have hcentralStrict : (218 / 25 : ℝ) < z.re := lt_of_not_ge hcentral
    have hexterior : (701 / 100 : ℝ) < z.re := by linarith
    exact (ccmPositivePairedReducedKernel_self_pos_of_orderTwentyThreeExteriorOverlap
      z hexterior hzreUpper hzim hzimUpper hzeta).le

end

end RHTower
