import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The compact Fourier transform of a constant, and parity of a quotient

Two elementary facts used wherever a characteristic function is built by Fourier transforming a
response over a symmetric interval.

* The Fourier transform of a constant over `[-a, a]` is the sine kernel `2 sin (a z) / z`, and its
  removable value at the origin is `2 a`.
* If the denominator is odd, the odd part of a quotient is the even part of the numerator divided
  by that denominator — so an odd characteristic converts an even-part computation into an odd-part
  statement with no further analysis.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex intervalIntegral

noncomputable section

/-- **Compact Fourier transform of a constant.**  Integrating `c · exp (I z y)` over the symmetric
interval `[-a, a]` gives the sine kernel. -/
theorem integral_const_mul_exp_mul_I_symm (a : ℝ) (c z : ℂ) (hz : z ≠ 0) :
    (∫ y in (-a : ℝ)..a, c * Complex.exp (I * z * (y : ℝ))) =
      c * (2 * Complex.sin (a * z) / z) := by
  have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hIz]
  have hkey : Complex.exp (I * z * ((a : ℝ) : ℂ)) - Complex.exp (I * z * (((-a : ℝ)) : ℂ))
      = 2 * Complex.sin ((a : ℂ) * z) * I := by
    have h := Complex.two_sinh ((a : ℂ) * z * I)
    rw [Complex.sinh_mul_I] at h
    rw [show (I * z * ((a : ℝ) : ℂ)) = (a : ℂ) * z * I by ring,
      show (I * z * (((-a : ℝ)) : ℂ)) = -((a : ℂ) * z * I) by push_cast; ring]
    linear_combination -h
  rw [hkey]
  field_simp

/-- The sine kernel extends continuously through the origin with value `2 a`. -/
theorem tendsto_sineKernel_nhdsNE_zero (a : ℝ) :
    Filter.Tendsto (fun z : ℂ => 2 * Complex.sin ((a : ℂ) * z) / z)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (2 * (a : ℂ))) := by
  have hderiv : HasDerivAt (fun z : ℂ => 2 * Complex.sin ((a : ℂ) * z))
      (2 * ((a : ℂ) * Complex.cos ((a : ℂ) * 0))) 0 := by
    have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) * z) (a : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)
    have h2 := (Complex.hasDerivAt_sin ((a : ℂ) * 0)).comp 0 h1
    simpa [mul_comm] using h2.const_mul (2 : ℂ)
  have hzero : (fun z : ℂ => 2 * Complex.sin ((a : ℂ) * z)) 0 = 0 := by simp
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hval : 2 * ((a : ℂ) * Complex.cos ((a : ℂ) * 0)) = 2 * (a : ℂ) := by simp
  rw [hval] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [slope_def_field, hzero, sub_zero, div_eq_inv_mul]

/-- **Parity of a quotient with an odd denominator.**  The odd part of `F / W` is the even part of
`F` divided by `W`. -/
theorem oddPart_div_of_odd {F W : ℂ → ℂ} (hW : ∀ z, W (-z) = -W z) {z : ℂ} (hz : W z ≠ 0) :
    (F z / W z - F (-z) / W (-z)) / 2 = ((F z + F (-z)) / 2) / W z := by
  rw [hW z]
  field_simp
  ring

/-- The even part of a quotient with an odd denominator is the odd part of the numerator divided by
that denominator. -/
theorem evenPart_div_of_odd {F W : ℂ → ℂ} (hW : ∀ z, W (-z) = -W z) {z : ℂ} (hz : W z ≠ 0) :
    (F z / W z + F (-z) / W (-z)) / 2 = ((F z - F (-z)) / 2) / W z := by
  rw [hW z]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
