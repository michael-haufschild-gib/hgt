import GaloisForLFunctions.RHTower.PrimeArchCentralPairedTrace
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance

open Complex

namespace RHTower

noncomputable section

/-- The order-23 source-height floor enlarges the literal line-conjugate reciprocal-square
phase margin to the rational Route-Q radius `279 / 20`. -/
theorem centralPaired_reciprocalSquare_orderTwentyThree_gap
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 279 / 20)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (2 / 215 : ℝ) <
      (1 - (xiZeroCopyReciprocalSquare q).re * (z ^ 2).re) ^ 2 := by
  let a : ℝ := (xiZeroCopyReciprocalSquare q).re
  let t : ℝ := (q.1 : ℂ).im
  let u : ℝ := (z ^ 2).re
  have ha : 0 < a := by
    simpa only [a, xiThermalNode] using xiThermalNode_pos q
  have ht : (431 / 2 : ℝ) ≤ t ^ 2 := by
    simpa only [t] using
      fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hoff
  have ht0 : 0 < t ^ 2 := by nlinarith
  have hare : a ≤ 1 / t ^ 2 := by
    simpa only [a, t] using
      centralPaired_reciprocalSquare_re_le_inv_ordinate_sq q ht0
  have hu : u ≤ z.re ^ 2 := by
    dsimp only [u]
    rw [pow_two]
    simp only [Complex.mul_re]
    nlinarith [sq_nonneg z.im]
  have hau : a * u ≤ a * z.re ^ 2 :=
    mul_le_mul_of_nonneg_left hu ha.le
  have hzr : z.re ^ 2 ≤ (279 / 20 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (z.re + 279 / 20)]
  have hat : a * t ^ 2 ≤ 1 := by
    calc
      a * t ^ 2 ≤ (1 / t ^ 2) * t ^ 2 :=
        mul_le_mul_of_nonneg_right hare ht0.le
      _ = 1 := by
        have htne : t ≠ 0 := by
          intro hzero
          have hsq : t ^ 2 = 0 := by rw [hzero]; norm_num
          nlinarith
        field_simp [htne]
  have hR0 : 0 ≤ (279 / 20 : ℝ) ^ 2 := sq_nonneg _
  have haR0 : 0 ≤ a * (279 / 20 : ℝ) ^ 2 :=
    mul_nonneg ha.le hR0
  have hprod :
      a * (279 / 20 : ℝ) ^ 2 * (431 / 2 : ℝ) ≤
        a * (279 / 20 : ℝ) ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_left ht haR0
  have hAt : a * (279 / 20 : ℝ) ^ 2 * t ^ 2 ≤ (279 / 20 : ℝ) ^ 2 := by
    calc
      a * (279 / 20 : ℝ) ^ 2 * t ^ 2 =
          (279 / 20 : ℝ) ^ 2 * (a * t ^ 2) := by ring
      _ ≤ (279 / 20 : ℝ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hat hR0
      _ = (279 / 20 : ℝ) ^ 2 := by ring
  have haR : a * (279 / 20 : ℝ) ^ 2 ≤
      (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 431 / 2)).mpr
    exact hprod.trans hAt
  have hauR : a * u ≤ (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ) := by
    calc
      a * u ≤ a * z.re ^ 2 := hau
      _ ≤ a * (279 / 20 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hzr ha.le
      _ ≤ (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ) := haR
  have hratio : (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ) < 1 := by norm_num
  have hmargin : (2 / 215 : ℝ) <
      (1 - (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ)) ^ 2 := by norm_num
  change (2 / 215 : ℝ) < (1 - a * u) ^ 2
  nlinarith [sq_nonneg ((1 - a * u) +
    (1 - (279 / 20 : ℝ) ^ 2 / (431 / 2 : ℝ)))]

/-- Every literal line-conjugate reciprocal-square pair has nonnegative Route-Q imaginary
response through the order-23 radius `279 / 20`. -/
theorem xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_orderTwentyThree
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 279 / 20)
    (hzim : 0 < z.im) (q : XiZeroCopy) (hXi : XiC z ≠ 0) :
    0 ≤ (xiReciprocalSquareResolventTerm z q +
      xiReciprocalSquareResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let lam : ℂ := xiZeroCopyReciprocalSquare q
  have hden : 1 - z ^ 2 * lam ≠ 0 := by
    dsimp only [lam]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi q
  have hdenconj : 1 - z ^ 2 * (starRingEnd ℂ) lam ≠ 0 := by
    dsimp only [lam]
    rw [← centralPaired_lineConj_reciprocalSquare q]
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
          centralPaired_reciprocalSquare_orderTwentyThree_gap z hzre hzreUpper q hoff
      have hpositive := centralPaired_reciprocalSquare_pair_barrier_pos
        (v := (z ^ 2).im) ha hphase hgap
      rw [Complex.normSq_apply]
      nlinarith [hpositive.le]
  rw [xiReciprocalSquareResolventTerm, xiReciprocalSquareResolventTerm,
    centralPaired_lineConj_reciprocalSquare q]
  exact centralPaired_lineConj_pair_im_nonneg_of_barrier
    (z ^ 2) lam hden hdenconj hwim hbarrier

/-- The actual continued prime--Gamma reciprocal-square trace has nonnegative sector phase
through the order-23 Route-Q band. -/
theorem continuedPrimeArchReciprocalSquareTrace_im_nonneg_orderTwentyThree
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 279 / 20)
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
  exact centralPaired_tsum_im_nonneg_of_lineConj_pairs
    (xiReciprocalSquareResolventTerm z)
    (summable_xiReciprocalSquareResolventTerm hXi)
    (fun q =>
      xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_orderTwentyThree
        z hzre hzreUpper hzim q hXi)

end

end RHTower
