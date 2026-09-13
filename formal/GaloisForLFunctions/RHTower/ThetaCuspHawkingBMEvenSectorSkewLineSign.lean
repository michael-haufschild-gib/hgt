import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewTrace

/-!
# The horizon logarithm of the skew cut on the critical line

On the critical line `s = −3/2 + i t` the logarithm coefficient `skewLogCoeff` of the antisymmetrized
`++−−` pairing is purely imaginary (`skewLogCoeff_line`), its imaginary part being an odd polynomial
of degree eleven in `t` divided by `−(9/4 + t²)`. That polynomial is `t` times a polynomial in `t²`
with a single sign change in its coefficients, so it has exactly one positive root; for `t² ≥ 3` it
is positive (`skewLogLineNumerator_pos`), hence the imaginary part of the coefficient is negative
there (`skewLogCoeff_line_im_neg`): the leading large-cutoff term of the skew cut has one sign at
every zero of `Ξ` of height at least `√3`.
-/

set_option autoImplicit false

namespace RHTower.D4BMScalarStream

/-- The imaginary part of the numerator of `skewLogCoeff` on the critical line, an odd polynomial. -/
noncomputable def skewLogLineNumerator (t : ℝ) : ℝ := (-33288453 / 2097152 : ℝ) * t + (-2174793 / 524288 : ℝ) * t ^ 3 + (136263 / 65536 : ℝ) * t ^ 5 + (13719 / 16384 : ℝ) * t ^ 7 + (1191 / 8192 : ℝ) * t ^ 9 + (75 / 2048 : ℝ) * t ^ 11

/-- The same polynomial in `u = t²`, without the factor `t`. -/
noncomputable def skewLogLineEven (u : ℝ) : ℝ := (-33288453 / 2097152 : ℝ) + (-2174793 / 524288 : ℝ) * u + (136263 / 65536 : ℝ) * u ^ 2 + (13719 / 16384 : ℝ) * u ^ 3 + (1191 / 8192 : ℝ) * u ^ 4 + (75 / 2048 : ℝ) * u ^ 5

theorem skewLogLineNumerator_eq (t : ℝ) : skewLogLineNumerator t = t * skewLogLineEven (t ^ 2) := by
  unfold skewLogLineNumerator skewLogLineEven
  ring

theorem line_denominator (t : ℝ) :
    ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3) = -(9 / 4 + (t : ℂ) ^ 2) := by
  linear_combination ((t : ℂ) ^ 2) * Complex.I_sq

/-- On the critical line the logarithm coefficient is purely imaginary. -/
theorem skewLogCoeff_line (t : ℝ) :
    skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (-(9 / 4 + (t : ℂ) ^ 2)) =
      Complex.I * (skewLogLineNumerator t : ℂ) := by
  have hne : ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) * (((-3 / 2 : ℂ) + (t : ℂ) * Complex.I) + 3) ≠ 0 := by
    rw [line_denominator]
    intro h
    rw [show (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) by push_cast; ring] at h
    have h' : -(9 / 4 + t ^ 2) = (0 : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg t]
  rw [← line_denominator]
  unfold skewLogCoeff
  rw [div_mul_cancel₀ _ hne]
  unfold skewLogLineNumerator
  push_cast
  linear_combination ((2174793 / 524288 : ℂ) * (t : ℂ) ^ 3 * Complex.I + (-136263 / 65536 : ℂ) * (t : ℂ) ^ 5 * Complex.I + (136263 / 65536 : ℂ) * (t : ℂ) ^ 5 * Complex.I ^ 3 + (-13719 / 16384 : ℂ) * (t : ℂ) ^ 7 * Complex.I + (13719 / 16384 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 3 + (-13719 / 16384 : ℂ) * (t : ℂ) ^ 7 * Complex.I ^ 5 + (-1191 / 8192 : ℂ) * (t : ℂ) ^ 9 * Complex.I + (1191 / 8192 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 3 + (-1191 / 8192 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 5 + (1191 / 8192 : ℂ) * (t : ℂ) ^ 9 * Complex.I ^ 7 + (-75 / 2048 : ℂ) * (t : ℂ) ^ 11 * Complex.I + (75 / 2048 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 3 + (-75 / 2048 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 5 + (75 / 2048 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 7 + (-75 / 2048 : ℂ) * (t : ℂ) ^ 11 * Complex.I ^ 9) * Complex.I_sq

/-- For `u ≥ 3` the even factor is positive. -/
theorem skewLogLineEven_pos (u : ℝ) (hu : 3 ≤ u) : 0 < skewLogLineEven u := by
  unfold skewLogLineEven
  have h2 : 3 * u ≤ u ^ 2 := by nlinarith
  have h3 : 9 * u ≤ u ^ 3 := by nlinarith
  have h4 : 27 * u ≤ u ^ 4 := by nlinarith
  have h5 : 81 * u ≤ u ^ 5 := by nlinarith
  nlinarith

theorem skewLogLineNumerator_pos (t : ℝ) (ht : 3 ≤ t ^ 2) (ht0 : 0 < t) : 0 < skewLogLineNumerator t := by
  rw [skewLogLineNumerator_eq]
  exact mul_pos ht0 (skewLogLineEven_pos _ ht)

/-- On the critical line at height `t ≥ √3` the logarithm coefficient has negative imaginary part. -/
theorem skewLogCoeff_line_im_neg (t : ℝ) (ht : 3 ≤ t ^ 2) (ht0 : 0 < t) :
    (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im < 0 := by
  have h := congrArg Complex.im (skewLogCoeff_line t)
  have hd : (0 : ℝ) < 9 / 4 + t ^ 2 := by positivity
  have hP := skewLogLineNumerator_pos t ht ht0
  have h' : (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).im * (-(9 / 4 + t ^ 2)) = skewLogLineNumerator t := by
    have e1 : (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [e1] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
    exact h
  nlinarith

/-- On the critical line the logarithm coefficient has zero real part. -/
theorem skewLogCoeff_line_re (t : ℝ) : (skewLogCoeff ((-3 / 2 : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by
  have h := congrArg Complex.re (skewLogCoeff_line t)
  have hd : (9 / 4 + t ^ 2) ≠ (0 : ℝ) := by positivity
  have e1 : (-(9 / 4 + (t : ℂ) ^ 2)) = ((-(9 / 4 + t ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp at h
  rcases h with h | h
  · exact h
  · nlinarith [sq_nonneg t]

end RHTower.D4BMScalarStream
