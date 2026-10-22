import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewFullTilt
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEvenSectorSkewLineSign
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIngoingCoordinates

/-!
# The regularized skew cut on the critical line, and its cutoff as an ingoing-clock depth

**Sign on the line.** On `s = −3/2 + i t` the finite part `skewFinitePart` is purely imaginary,
its imaginary part being an odd polynomial of degree eleven in `t` over `−(9/4 + t²)`
(`skewFinitePart_line`); it is positive for `t ≥ 5` (`skewFinitePart_line_im_pos`), while the
logarithm coefficient is negative there (`skewLogCoeff_line_im_neg`). The sum of the two line
numerators has leading coefficient `75/4096 > 0` and is positive for `t² ≥ 25`
(`skewLineSumEven_pos`), so for every horizon cutoff `ε ≤ 4/e` the regularized cut
`skewCut s ε = skewFinitePart s + skewLogCoeff s·log(4/ε)` has real part zero and negative
imaginary part at every point of the line of height at least five (`skewCut_line_im_neg`,
`skewCut_line_re`). Together with `skewCut_re_eq_zero_iff` this is the complete elementary sign
law of the cut at the fundamental harmonic: on the line the cut is `−i` times a positive number,
off the line its real part is `(2σ − 1)` times a negative number.

**The cutoff is a clock reading.** The horizon cutoff `z = ε` sits at radius
`cutoffRadius ε = (1 − ε)^{−1/2}`, whose tortoise coordinate `tortoise r = ½ log((r−1)/(r+1))`
satisfies `log(4/ε) = −2·tortoise (cutoffRadius ε) + 2·log(2/(1 + √(1−ε)))`
(`log_cutoff_eq_tortoise`), the correction lying in `(0, 2 log 2)` and tending to zero. Since the
ingoing time of a point on the static slice `t = 0` is its tortoise coordinate, the cutoff scale
`log(4/ε)` is twice the ingoing-clock depth `−v_ε` of the cutoff, up to the vanishing correction:
`skewCut s ε = skewFinitePart s − 2·skewLogCoeff s·tortoise (cutoffRadius ε) + (correction)`
(`skewCut_eq_tortoise`). Every cutoff of ingoing depth at least one half is covered by the sign
law (`skewCut_re_eq_zero_iff_tortoise`, `skewCut_line_im_neg_tortoise`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The imaginary part of the numerator of `skewFinitePart` on the critical line, an odd polynomial. -/
noncomputable def skewFPLineNumerator (t : ℝ) : ℝ := (90069061 / 4194304 : ℝ) * t + (6532169 / 1048576 : ℝ) * t ^ (3 : ℕ) + (-310919 / 131072 : ℝ) * t ^ (5 : ℕ) + (-63255 / 32768 : ℝ) * t ^ (7 : ℕ) + (-7527 / 16384 : ℝ) * t ^ (9 : ℕ) + (-75 / 4096 : ℝ) * t ^ (11 : ℕ)

/-- The same polynomial in `u = t²`, without the factor `t`. -/
noncomputable def skewFPLineEven (u : ℝ) : ℝ := (90069061 / 4194304 : ℝ) + (6532169 / 1048576 : ℝ) * u + (-310919 / 131072 : ℝ) * u ^ (2 : ℕ) + (-63255 / 32768 : ℝ) * u ^ (3 : ℕ) + (-7527 / 16384 : ℝ) * u ^ (4 : ℕ) + (-75 / 4096 : ℝ) * u ^ (5 : ℕ)

theorem skewFPLineNumerator_eq (t : ℝ) : skewFPLineNumerator t = t * skewFPLineEven (t ^ (2 : ℕ)) := by
  unfold skewFPLineNumerator skewFPLineEven
  ring

/-- On the critical line the finite part is purely imaginary. -/
theorem skewFinitePart_line (t : ℝ) :
    skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (-(9 / 4 + (t : ℂ) ^ (2 : ℕ))) =
      Complex.I * (skewFPLineNumerator t : ℂ) := by
  have hne : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3) ≠ 0 := by
    rw [line_denominator]
    intro h
    rw [show (-(9 / 4 + (t : ℂ) ^ (2 : ℕ))) = ((-(9 / 4 + t ^ (2 : ℕ)) : ℝ) : ℂ) by push_cast; ring] at h
    have h' : -(9 / 4 + t ^ (2 : ℕ)) = (0 : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg t]
  have hs : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := left_ne_zero_of_mul hne
  have hs3 : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3 ≠ 0 := right_ne_zero_of_mul hne
  rw [← line_denominator, skewFinitePart_eq _ hs hs3, div_mul_cancel₀ _ hne]
  unfold skewFPLineNumerator
  push_cast
  linear_combination ((-6532169 / 1048576 : ℂ) * (t : ℂ) ^ (3 : ℕ) * Complex.I + (310919 / 131072 : ℂ) * (t : ℂ) ^ (5 : ℕ) * Complex.I + (-310919 / 131072 : ℂ) * (t : ℂ) ^ (5 : ℕ) * Complex.I ^ (3 : ℕ) + (63255 / 32768 : ℂ) * (t : ℂ) ^ (7 : ℕ) * Complex.I + (-63255 / 32768 : ℂ) * (t : ℂ) ^ (7 : ℕ) * Complex.I ^ (3 : ℕ) + (63255 / 32768 : ℂ) * (t : ℂ) ^ (7 : ℕ) * Complex.I ^ (5 : ℕ) + (7527 / 16384 : ℂ) * (t : ℂ) ^ (9 : ℕ) * Complex.I + (-7527 / 16384 : ℂ) * (t : ℂ) ^ (9 : ℕ) * Complex.I ^ (3 : ℕ) + (7527 / 16384 : ℂ) * (t : ℂ) ^ (9 : ℕ) * Complex.I ^ (5 : ℕ) + (-7527 / 16384 : ℂ) * (t : ℂ) ^ (9 : ℕ) * Complex.I ^ (7 : ℕ) + (75 / 4096 : ℂ) * (t : ℂ) ^ (11 : ℕ) * Complex.I + (-75 / 4096 : ℂ) * (t : ℂ) ^ (11 : ℕ) * Complex.I ^ (3 : ℕ) + (75 / 4096 : ℂ) * (t : ℂ) ^ (11 : ℕ) * Complex.I ^ (5 : ℕ) + (-75 / 4096 : ℂ) * (t : ℂ) ^ (11 : ℕ) * Complex.I ^ (7 : ℕ) + (75 / 4096 : ℂ) * (t : ℂ) ^ (11 : ℕ) * Complex.I ^ (9 : ℕ)) * Complex.I_sq

/-- The even factor of the sum of the two line numerators. -/
noncomputable def skewLineSumEven (u : ℝ) : ℝ := (23492155 / 4194304 : ℝ) + (2182583 / 1048576 : ℝ) * u + (-38393 / 131072 : ℝ) * u ^ (2 : ℕ) + (-35817 / 32768 : ℝ) * u ^ (3 : ℕ) + (-5145 / 16384 : ℝ) * u ^ (4 : ℕ) + (75 / 4096 : ℝ) * u ^ (5 : ℕ)

theorem skewLineSumEven_eq (u : ℝ) : skewLineSumEven u = skewFPLineEven u + skewLogLineEven u := by
  unfold skewLineSumEven skewFPLineEven skewLogLineEven
  ring

/-- For `u ≥ 25` the even factor of the sum is positive. -/
theorem skewLineSumEven_pos (u : ℝ) (hu : 25 ≤ u) : 0 < skewLineSumEven u := by
  unfold skewLineSumEven
  have h2 : 25 * u ≤ u ^ (2 : ℕ) := by nlinarith
  have h3 : 25 * u ^ (2 : ℕ) ≤ u ^ (3 : ℕ) := by nlinarith
  have h4 : 25 * u ^ (3 : ℕ) ≤ u ^ (4 : ℕ) := by nlinarith
  have h5 : 25 * u ^ (4 : ℕ) ≤ u ^ (5 : ℕ) := by nlinarith
  nlinarith

/-- For `u ≥ 25` the even factor of the finite part's line numerator is negative. -/
theorem skewFPLineEven_neg (u : ℝ) (hu : 25 ≤ u) : skewFPLineEven u < 0 := by
  unfold skewFPLineEven
  have h2 : 25 * u ≤ u ^ (2 : ℕ) := by nlinarith
  have h3 : 25 * u ^ (2 : ℕ) ≤ u ^ (3 : ℕ) := by nlinarith
  have h4 : 25 * u ^ (3 : ℕ) ≤ u ^ (4 : ℕ) := by nlinarith
  have h5 : 25 * u ^ (4 : ℕ) ≤ u ^ (5 : ℕ) := by nlinarith
  nlinarith

/-- For `t ≥ 5` the finite part has positive imaginary part on the line. -/
theorem skewFinitePart_line_im_pos (t : ℝ) (ht : 5 ≤ t) :
    0 < (skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im := by
  have h := congrArg Complex.im (skewFinitePart_line t)
  have hd : (0 : ℝ) < 9 / 4 + t ^ (2 : ℕ) := by positivity
  have h' : (skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im * (-(9 / 4 + t ^ (2 : ℕ))) = skewFPLineNumerator t := by
    have e1 : (-(9 / 4 + (t : ℂ) ^ (2 : ℕ))) = ((-(9 / 4 + t ^ (2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
    rw [e1] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
    exact h
  have hu : 25 ≤ t ^ (2 : ℕ) := by nlinarith
  have hN : skewFPLineNumerator t < 0 := by
    rw [skewFPLineNumerator_eq]
    have := skewFPLineEven_neg (t ^ (2 : ℕ)) hu
    nlinarith
  nlinarith

/-- On the critical line the finite part has zero real part. -/
theorem skewFinitePart_line_re (t : ℝ) : (skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by
  have h := congrArg Complex.re (skewFinitePart_line t)
  have hd : (9 / 4 + t ^ (2 : ℕ)) ≠ (0 : ℝ) := by positivity
  have e1 : (-(9 / 4 + (t : ℂ) ^ (2 : ℕ))) = ((-(9 / 4 + t ^ (2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp at h
  rcases h with h | h
  · exact h
  · nlinarith [sq_nonneg t]

/-- The regularized cut is purely imaginary on the line. -/
theorem skewCut_line_re (t ε : ℝ) : (skewCut ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ε).re = 0 := by
  unfold skewCut
  rw [Complex.add_re, skewFinitePart_line_re, Complex.mul_re, skewLogCoeff_line_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The line numerators of the finite part and of the logarithm coefficient have a positive sum for `t ≥ 5`. -/
theorem skewLineNumerators_sum_pos (t : ℝ) (ht : 5 ≤ t) :
    0 < skewFPLineNumerator t + skewLogLineNumerator t := by
  rw [skewFPLineNumerator_eq, skewLogLineNumerator_eq, ← mul_add, ← skewLineSumEven_eq]
  exact mul_pos (by linarith) (skewLineSumEven_pos _ (by nlinarith))

/-- For every cutoff `ε ≤ 4/e` and every height `t ≥ 5` the regularized cut has negative imaginary
part on the critical line. -/
theorem skewCut_line_im_neg (t ε : ℝ) (ht : 5 ≤ t) (hε : 1 ≤ Real.log (4 / ε)) :
    (skewCut ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ε).im < 0 := by
  unfold skewCut
  simp only [Complex.add_im, Complex.mul_im, skewLogCoeff_line_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add]
  have hd : (0 : ℝ) < 9 / 4 + t ^ (2 : ℕ) := by positivity
  have hF := congrArg Complex.im (skewFinitePart_line t)
  have hL := congrArg Complex.im (skewLogCoeff_line t)
  have e1 : (-(9 / 4 + (t : ℂ) ^ (2 : ℕ))) = ((-(9 / 4 + t ^ (2 : ℕ)) : ℝ) : ℂ) := by push_cast; ring
  rw [e1] at hF hL
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_add, one_mul] at hF hL
  have hLneg := skewLogCoeff_line_im_neg t (by nlinarith) (by linarith)
  have hsum := skewLineNumerators_sum_pos t ht
  have hmono : (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im * Real.log (4 / ε) ≤
      (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im := by
    have := mul_le_mul_of_nonpos_left hε hLneg.le
    linarith
  have hkey : (skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im +
      (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im < 0 := by
    have : ((skewFinitePart ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im +
        (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im) * (-(9 / 4 + t ^ (2 : ℕ))) =
        skewFPLineNumerator t + skewLogLineNumerator t := by rw [add_mul, hF, hL]
    nlinarith
  linarith

/-- The static radius of the horizon cutoff `z = ε`. -/
noncomputable def cutoffRadius (ε : ℝ) : ℝ := 1 / Real.sqrt (1 - ε)

/-- The correction between the cutoff scale and the tortoise depth, in `(0, 2 log 2)`. -/
noncomputable def tortoiseCorrection (ε : ℝ) : ℝ := 2 * Real.log (2 / (1 + Real.sqrt (1 - ε)))

/-- The cutoff scale is twice the tortoise depth of the cutoff radius, up to the correction. -/
theorem log_cutoff_eq_tortoise (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log (4 / ε) = -2 * D4BMIngoingCoordinates.tortoise (cutoffRadius ε) + tortoiseCorrection ε := by
  unfold D4BMIngoingCoordinates.tortoise cutoffRadius tortoiseCorrection
  have h1 : 0 < 1 - ε := by linarith
  have hq : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.mpr h1
  have hq1 : Real.sqrt (1 - ε) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  have hsq : Real.sqrt (1 - ε) ^ (2 : ℕ) = 1 - ε := Real.sq_sqrt h1.le
  set q := Real.sqrt (1 - ε) with hqdef
  have hm : 0 < 1 / q - 1 := by rw [one_div]; have := one_lt_inv_iff₀.mpr ⟨hq, hq1⟩; linarith
  have hp : 0 < 1 / q + 1 := by positivity
  have hA : 1 / q - 1 = (1 - q) / q := by field_simp
  have hB : 1 / q + 1 = (1 + q) / q := by field_simp
  have hC : 4 / ε = 4 / (1 - q ^ (2 : ℕ)) := by rw [hsq]; ring
  have h1q : 0 < 1 - q := by linarith
  have h1q' : 0 < 1 + q := by linarith
  rw [hA, hB, hC, Real.log_div (by positivity) hq.ne', Real.log_div (by positivity) hq.ne',
    show (1 - q ^ (2 : ℕ)) = (1 - q) * (1 + q) by ring, Real.log_div (by norm_num) (by positivity),
    Real.log_mul h1q.ne' h1q'.ne', Real.log_div (by norm_num) h1q'.ne',
    show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  push_cast
  ring

theorem tortoiseCorrection_pos (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : 0 < tortoiseCorrection ε := by
  unfold tortoiseCorrection
  have h1 : 0 < 1 - ε := by linarith
  have hq1 : Real.sqrt (1 - ε) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  have hq : 0 ≤ Real.sqrt (1 - ε) := Real.sqrt_nonneg _
  have : 1 < 2 / (1 + Real.sqrt (1 - ε)) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have := Real.log_pos this
  linarith

theorem tortoiseCorrection_lt (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : tortoiseCorrection ε < 2 * Real.log 2 := by
  unfold tortoiseCorrection
  have h1 : 0 < 1 - ε := by linarith
  have hq : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.mpr h1
  have : 2 / (1 + Real.sqrt (1 - ε)) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have := Real.log_lt_log (by positivity) this
  linarith

/-- The correction vanishes at the horizon. -/
theorem tortoiseCorrection_tendsto :
    Filter.Tendsto tortoiseCorrection (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hden : Continuous (fun ε : ℝ => 2 / (1 + Real.sqrt (1 - ε))) :=
    continuous_const.div (continuous_const.add (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)))
      (fun ε => by positivity)
  have hne : (2 : ℝ) / (1 + Real.sqrt (1 - (0 : ℝ))) ≠ 0 := by simp
  have hlog : ContinuousAt (fun ε : ℝ => Real.log (2 / (1 + Real.sqrt (1 - ε)))) 0 :=
    ContinuousAt.comp (f := fun ε : ℝ => 2 / (1 + Real.sqrt (1 - ε))) (g := Real.log)
      (Real.continuousAt_log hne) hden.continuousAt
  have ht := (hlog.tendsto).const_mul (2 : ℝ)
  have h0 : (2 : ℝ) * Real.log (2 / (1 + Real.sqrt (1 - (0 : ℝ)))) = 0 := by
    rw [sub_zero, Real.sqrt_one, show (2 : ℝ) / (1 + 1) = 1 by norm_num, Real.log_one, mul_zero]
  rw [h0] at ht
  unfold tortoiseCorrection
  exact ht.mono_left nhdsWithin_le_nhds

/-- The regularized cut in the ingoing clock: the finite part plus the logarithm coefficient times twice
the ingoing depth of the cutoff, plus the vanishing correction. -/
theorem skewCut_eq_tortoise (s : ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    skewCut s ε = skewFinitePart s + skewLogCoeff s * ((-2 * D4BMIngoingCoordinates.tortoise (cutoffRadius ε) : ℝ) : ℂ) +
      skewLogCoeff s * ((tortoiseCorrection ε : ℝ) : ℂ) := by
  unfold skewCut
  rw [log_cutoff_eq_tortoise ε hε hε1]
  push_cast
  ring

/-- Every cutoff of ingoing depth at least one half is covered by the tilt detection. -/
theorem skewCut_re_eq_zero_iff_tortoise (σ t ε : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (58 : ℝ) ≤ t)
    (hε : 0 < ε) (hε1 : ε < 1) (hdepth : D4BMIngoingCoordinates.tortoise (cutoffRadius ε) ≤ -1 / 2) :
    ((skewCut ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ε).re = 0 ↔ σ = 1 / 2) := by
  apply skewCut_re_eq_zero_iff σ t ε h0 h1 ht
  rw [log_cutoff_eq_tortoise ε hε hε1]
  have := tortoiseCorrection_pos ε hε hε1
  linarith

/-- Every cutoff of ingoing depth at least one half has the on-line sign. -/
theorem skewCut_line_im_neg_tortoise (t ε : ℝ) (ht : 5 ≤ t) (hε : 0 < ε) (hε1 : ε < 1)
    (hdepth : D4BMIngoingCoordinates.tortoise (cutoffRadius ε) ≤ -1 / 2) :
    (skewCut ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) ε).im < 0 := by
  apply skewCut_line_im_neg t ε ht
  rw [log_cutoff_eq_tortoise ε hε hε1]
  have := tortoiseCorrection_pos ε hε hε1
  linarith

end RHTower.D4BMScalarStream
