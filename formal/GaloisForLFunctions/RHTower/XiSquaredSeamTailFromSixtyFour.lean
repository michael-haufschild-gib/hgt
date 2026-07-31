import GaloisForLFunctions.RHTower.XiSquaredSeamPowerThirtyTwoAnnulus

/-!
# Tail-from-64 squared-Xi phase collapse

The power-32 annulus is not a necessary predecessor of the squared-Xi dyadic endpoint.  If the
dyadic tail beginning at power `64` is nonnegative, dyadic rigidity first puts the sixty-fourth
power on the nonnegative real ray.  The already unconditional strict signs at powers
`16, 8, 4, 2, 1` then select the positive real root at every descent step.

Consequently the tail from `64` alone is equivalent to RH.  No annulus exclusion, estimate, or
divisor computation is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- A complex number in the open right half-plane whose fourth power is nonnegative real is
itself real.  This is the only non-square step in the tail-from-64 descent. -/
theorem complex_im_eq_zero_of_re_pos_of_pow_four_nonnegativeReal
    {z : ℂ} (hre : 0 < z.re)
    (hpowIm : (z ^ 4).im = 0) (hpowRe : 0 ≤ (z ^ 4).re) :
    z.im = 0 := by
  by_contra him
  have hfactor :
      4 * z.re * z.im * (z.re ^ 2 - z.im ^ 2) = 0 := by
    rw [← hpowIm]
    simp [pow_succ, Complex.mul_im]
    ring
  have hleft : 4 * z.re * z.im ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hre.ne') him
  have hsq : z.im ^ 2 = z.re ^ 2 := by
    have hdiff := (mul_eq_zero.mp hfactor).resolve_left hleft
    linarith
  have hformula :
      (z ^ 4).re =
        (z.re ^ 2) ^ 2 - 6 * z.re ^ 2 * z.im ^ 2 + (z.im ^ 2) ^ 2 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  rw [hformula, hsq] at hpowRe
  nlinarith [sq_pos_of_pos hre]

/-- If a square is real and the chosen square root lies in the open right half-plane, that root
is real. -/
theorem complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
    {z : ℂ} (hre : 0 < z.re) (hsq : (z ^ 2).im = 0) :
    z.im = 0 := by
  rw [pow_two, Complex.mul_im] at hsq
  have hprod : z.re * z.im = 0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left hre.ne'

/-- Tail signs beginning at power `64` already imply the complete dyadic half-plane condition.
The formerly separate power-32 annulus hypothesis is redundant. -/
theorem xiSquaredSeamDyadicHalfPlane_of_tailFromSix
    (h : XiSquaredSeamDyadicTailFromSix) :
    XiSquaredSeamDyadicHalfPlane := by
  intro q
  let z : ℂ := xiSquaredSeamOneCoordinate q
  have h64tail : GaloisForLFunctions.ComplexDyadicHalfPlane (z ^ 64) := by
    intro k
    have hk := h q (k + 6) (by omega)
    have hexp : 64 * 2 ^ k = 2 ^ (k + 6) := by
      rw [pow_add]
      norm_num
      ring
    simpa only [z, ← pow_mul, hexp] using hk
  have h64real :=
    (GaloisForLFunctions.complexDyadicHalfPlane_iff_nonnegativeReal
      (z ^ 64)).mp h64tail
  have h16re : 0 < (z ^ 16).re := by
    have hr := xiSquaredSeamDyadic_rung_four_pos q; norm_num at hr; simpa only [z] using hr
  have h16im : (z ^ 16).im = 0 := by
    apply complex_im_eq_zero_of_re_pos_of_pow_four_nonnegativeReal h16re
    · simpa only [show (z ^ 16) ^ 4 = z ^ 64 by ring] using h64real.1
    · simpa only [show (z ^ 16) ^ 4 = z ^ 64 by ring] using h64real.2
  have h8im : (z ^ 8).im = 0 := by
    apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
      (by have hr := xiSquaredSeamDyadic_rung_three_pos q; norm_num at hr; simpa only [z] using hr)
    simpa only [show (z ^ 8) ^ 2 = z ^ 16 by ring] using h16im
  have h4im : (z ^ 4).im = 0 := by
    apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
      (by have hr := xiSquaredSeamDyadic_rung_two_pos q; norm_num at hr; simpa only [z] using hr)
    simpa only [show (z ^ 4) ^ 2 = z ^ 8 by ring] using h8im
  have h2im : (z ^ 2).im = 0 := by
    apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
      (by have hr := xiSquaredSeamDyadic_rung_one_pos q; norm_num at hr; simpa only [z] using hr)
    simpa only [show (z ^ 2) ^ 2 = z ^ 4 by ring] using h4im
  have him : z.im = 0 := by
    apply complex_im_eq_zero_of_re_pos_of_sq_im_eq_zero
      (by simpa [z] using xiSquaredSeamDyadic_rung_zero_pos q)
    exact h2im
  exact (GaloisForLFunctions.complexDyadicHalfPlane_iff_nonnegativeReal z).mpr
    ⟨him, (by simpa only [z] using (xiSquaredSeamOneCoordinate_re_pos q).le)⟩

/-- **Tail-from-64 RH law.**  The single remaining dyadic tail is an exact RH predecessor; the
power-32 annulus interface drops out of the backward proof chain. -/
theorem xiSquaredSeamDyadicTailFromSix_iff_riemannHypothesis :
    XiSquaredSeamDyadicTailFromSix ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_xiSquaredSeamDyadicHalfPlane
      (xiSquaredSeamDyadicHalfPlane_of_tailFromSix h)
  · intro hRH q k _
    exact xiSquaredSeamDyadicHalfPlane_of_riemannHypothesis hRH q k

end

end RHTower
