import GaloisForLFunctions.RHTower.XiPositivePairedDiagonalSectorCollapse

/-!
# Exact algebra for central Route-Q line-conjugate pairs

This file isolates the literal complex algebra behind the central paired-diagonal phase law.
It has no source-side positivity conclusion: that requires the height and orientation bounds in
`PrimeArchCentralPairedDiagonalPhase`.
-/

open Complex

namespace RHTower

noncomputable section

theorem centralPaired_lineConj_reciprocalSquare (q : XiZeroCopy) :
    xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
  simp [xiZeroCopyReciprocalSquare, xiSpectralPoint_lineConj, map_inv₀]

/-- Exact imaginary part of a reciprocal-square atom and its line-conjugate partner. -/
theorem centralPaired_reciprocalSquare_lineConj_pair_im_formula
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

/-- A reciprocal-square atom's positive real part is bounded by inverse squared ordinate. -/
theorem centralPaired_reciprocalSquare_re_le_inv_ordinate_sq
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

/-- Phase and gap margins imply positivity of the paired-atom numerator. -/
theorem centralPaired_reciprocalSquare_pair_barrier_pos
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

theorem centralPaired_lineConj_pair_im_nonneg_of_barrier
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
  rw [centralPaired_reciprocalSquare_lineConj_pair_im_formula w lam h hc]
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hwim) hbarrier
  · exact mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

end

end RHTower
