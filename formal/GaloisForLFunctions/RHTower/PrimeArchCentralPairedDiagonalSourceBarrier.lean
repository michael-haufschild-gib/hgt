import GaloisForLFunctions.RHTower.PrimeArchCentralPairedDiagonalAlgebra
import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase
import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw

/-!
# Source-certified atom barrier for central Route Q

The exact line-conjugate algebra becomes positive on actual Xi zero copies because the
unconditional off-line ordinate gap and order-23 orientation corridor dominate the only
negative phase term.
-/

open Complex

namespace RHTower

noncomputable section

/-- The certified off-line height and orientation corridor leave a uniform phase margin for
the paired reciprocal-square atom throughout the central Route-Q band. -/
theorem centralPaired_reciprocalSquare_central_gap
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (2 / 215 : ℝ) <
      (1 - (xiZeroCopyReciprocalSquare q).re * (z ^ (2 : ℕ)).re) ^ (2 : ℕ) := by
  let a : ℝ := (xiZeroCopyReciprocalSquare q).re
  let t : ℝ := (q.1 : ℂ).im
  let u : ℝ := (z ^ (2 : ℕ)).re
  have ha : 0 < a := by
    simpa only [a, xiThermalNode] using xiThermalNode_pos q
  have ht : (7907 / 93 : ℝ) < t ^ (2 : ℕ) := by
    simpa only [t] using
      xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq q hoff
  have ht0 : 0 < t ^ (2 : ℕ) := by linarith
  have hare : a ≤ 1 / t ^ (2 : ℕ) := by
    simpa only [a, t] using
      centralPaired_reciprocalSquare_re_le_inv_ordinate_sq q ht0
  have hu : u ≤ z.re ^ (2 : ℕ) := by
    dsimp only [u]
    rw [pow_two]
    simp only [Complex.mul_re]
    nlinarith [sq_nonneg z.im]
  have hau : a * u ≤ a * z.re ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hu ha.le
  have hzr : z.re ^ (2 : ℕ) ≤ (218 / 25 : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (z.re + 218 / 25)]
  have haR : a * (218 / 25 : ℝ) ^ (2 : ℕ) <
      (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ) := by
    have hmul : a * t ^ (2 : ℕ) ≤ 1 := by
      calc
        a * t ^ (2 : ℕ) ≤ (1 / t ^ (2 : ℕ)) * t ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hare ht0.le
        _ = 1 := by
          have htne : t ≠ 0 := by
            intro h
            have hsq : t ^ (2 : ℕ) = 0 := by rw [h]; norm_num
            nlinarith
          field_simp [htne]
    have hAt : a * (218 / 25 : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) ≤
        (218 / 25 : ℝ) ^ (2 : ℕ) := by
      calc
        a * (218 / 25 : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) =
            (218 / 25 : ℝ) ^ (2 : ℕ) * (a * t ^ (2 : ℕ)) := by ring
        _ ≤ (218 / 25 : ℝ) ^ (2 : ℕ) * 1 :=
          mul_le_mul_of_nonneg_left hmul (sq_nonneg _)
        _ = (218 / 25 : ℝ) ^ (2 : ℕ) := by ring
    have hpos : 0 < a * (218 / 25 : ℝ) ^ (2 : ℕ) := by positivity
    have hprod : a * (218 / 25 : ℝ) ^ (2 : ℕ) * (7907 / 93 : ℝ) <
        a * (218 / 25 : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) := by
      exact mul_lt_mul_of_pos_left ht hpos
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 7907 / 93)).mpr
    exact hprod.trans_le hAt
  have hauR : a * u < (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ) := by
    calc
      a * u ≤ a * z.re ^ (2 : ℕ) := hau
      _ ≤ a * (218 / 25 : ℝ) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hzr ha.le
      _ < (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ) := haR
  have hratio : (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ) < 1 := by norm_num
  have hmargin : (2 / 215 : ℝ) <
      (1 - (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ)) ^ (2 : ℕ) := by norm_num
  change (2 / 215 : ℝ) < (1 - a * u) ^ (2 : ℕ)
  nlinarith [sq_nonneg ((1 - a * u) +
    (1 - (218 / 25 : ℝ) ^ (2 : ℕ) / (7907 / 93 : ℝ)))]

/-- Every literal line-conjugate pair has nonnegative Route-Q imaginary response in the central
band.  This is the cancellation law unavailable from individual complex atoms. -/
theorem xiReciprocalSquareResolventTerm_lineConj_pair_im_nonneg_central
    (z : ℂ) (hzre : 0 < z.re) (hzreUpper : z.re ≤ 218 / 25)
    (hzim : 0 < z.im) (q : XiZeroCopy) (hXi : XiC z ≠ 0) :
    0 ≤ (xiReciprocalSquareResolventTerm z q +
      xiReciprocalSquareResolventTerm z (xiZeroCopyLineConjEquiv q)).im := by
  let lam : ℂ := xiZeroCopyReciprocalSquare q
  have hden : 1 - z ^ (2 : ℕ) * lam ≠ 0 := by
    dsimp only [lam]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi q
  have hdenconj : 1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 := by
    dsimp only [lam]
    rw [← centralPaired_lineConj_reciprocalSquare q]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi
      (xiZeroCopyLineConjEquiv q)
  have hwim : 0 ≤ (z ^ (2 : ℕ)).im := by
    rw [pow_two]
    simp only [Complex.mul_im]
    exact (add_pos (mul_pos hzre hzim) (mul_pos hzim hzre)).le
  have hbarrier : 0 ≤
      Complex.normSq lam *
          ((1 - (z ^ (2 : ℕ)).re * lam.re) ^ (2 : ℕ) + ((z ^ (2 : ℕ)).re * lam.im) ^ (2 : ℕ) +
            (z ^ (2 : ℕ)).im ^ (2 : ℕ) * Complex.normSq lam) -
        2 * lam.im ^ (2 : ℕ) := by
    by_cases hoff : (q.1 : ℂ).re = 1 / 2
    · have him : lam.im = 0 := by
        dsimp only [lam]
        rw [xiZeroCopyReciprocalSquare_im_formula, hoff]
        norm_num
      rw [him]
      have hnonneg : 0 ≤ Complex.normSq lam *
          ((1 - (z ^ (2 : ℕ)).re * lam.re) ^ (2 : ℕ) +
            (z ^ (2 : ℕ)).im ^ (2 : ℕ) * Complex.normSq lam) :=
        mul_nonneg (Complex.normSq_nonneg _)
          (add_nonneg (sq_nonneg _)
            (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)))
      nlinarith
    · have ha : 0 < lam.re := by
        simpa only [lam, xiThermalNode] using xiThermalNode_pos q
      have hphase : lam.im ^ (2 : ℕ) < (1 / 215 : ℝ) * lam.re ^ (2 : ℕ) := by
        simpa only [lam] using
          xiZeroCopyReciprocalSquare_orderTwentyThree_orientation_sq_lt q hoff
      have hgap : (2 / 215 : ℝ) <
          (1 - lam.re * (z ^ (2 : ℕ)).re) ^ (2 : ℕ) := by
        simpa only [lam] using
          centralPaired_reciprocalSquare_central_gap z hzre hzreUpper q hoff
      have hpositive := centralPaired_reciprocalSquare_pair_barrier_pos
        (v := (z ^ (2 : ℕ)).im) ha hphase hgap
      rw [Complex.normSq_apply]
      nlinarith [hpositive.le]
  rw [xiReciprocalSquareResolventTerm, xiReciprocalSquareResolventTerm,
    centralPaired_lineConj_reciprocalSquare q]
  exact centralPaired_lineConj_pair_im_nonneg_of_barrier
    (z ^ (2 : ℕ)) lam hden hdenconj hwim hbarrier

end

end RHTower
