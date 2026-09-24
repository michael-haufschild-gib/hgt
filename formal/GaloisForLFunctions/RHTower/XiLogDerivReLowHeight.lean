import GaloisForLFunctions.RHTower.XiLogDerivReLocality
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance

/-!
# Unconditional positivity inside the strip at low height

The criterion `0 ≤ Re (ξ'/ξ)(s)` is local in the ordinate: only zeros whose ordinate lies within
`1/2` of `Im s` can obstruct.  The corpus's order-23 threshold says every **off-line** divisor copy
has ordinate square at least `431/2`, hence ordinate modulus at least `14.67…`.  A point of height
at most `14` therefore has no off-line zero within ordinate distance `1/2`, and the on-line zeros
never obstruct.

So the criterion holds unconditionally on the whole region `Re s > 1/2`, `|Im s| ≤ 14`, which lies
strictly inside the critical strip.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Unconditional positivity strictly inside the critical strip, at low height.**  Every
off-line divisor copy has ordinate square at least `431/2`, so no off-line zero has ordinate within
`1/2` of a point of height at most `14`.  By ordinate locality the criterion then holds there for
every abscissa to the right of the critical line. -/
theorem re_logDeriv_xi_nonneg_of_low_height {s : ℂ} (hs : 1 / 2 < s.re)
    (ht : |s.im| ≤ 14) : 0 ≤ (logDeriv xi s).re := by
  by_cases hxi : xi s = 0
  · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi]
    simp
  refine re_logDeriv_xi_nonneg_of_near_zeros hs hxi (fun q hy => ?_)
  by_cases hoff : ((q.1 : ℂ)).re = 1 / 2
  · rw [hoff]
    nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]
  · exfalso
    have hgamma := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hoff
    have h1 : |s.im - ((q.1 : ℂ)).im| < 1 / 2 := by
      nlinarith [sq_abs (s.im - ((q.1 : ℂ)).im), abs_nonneg (s.im - ((q.1 : ℂ)).im)]
    have h2 : |((q.1 : ℂ)).im| < 14 + 1 / 2 := by
      have hrw : ((q.1 : ℂ)).im = s.im - (s.im - ((q.1 : ℂ)).im) := by ring
      calc |((q.1 : ℂ)).im| = |s.im - (s.im - ((q.1 : ℂ)).im)| := by rw [← hrw]
        _ ≤ |s.im| + |s.im - ((q.1 : ℂ)).im| := abs_sub _ _
        _ < 14 + 1 / 2 := by linarith
    have h3 : ((q.1 : ℂ)).im ^ (2 : ℕ) < (14 + 1 / 2) ^ (2 : ℕ) := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (((q.1 : ℂ)).im)]
    nlinarith [hgamma, h3]

end

end RHTower
