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

/-- **Assembly of the normalized reflection-odd response.**  If the numerator's even part is the
sine kernel carrying `mu1`, and the denominator is odd with central jet `d = I * mu1`, then the odd
part of the normalized quotient is `-d sin (a z) / (2 z W z)`.

This is the algebraic step that turns an even-part computation and a central-jet identification
into the response formula; no analysis enters beyond the two inputs. -/
theorem oddPart_normalizedResponse_eq {T W : ℂ → ℂ} {a mu1 d z : ℂ}
    (hW : ∀ w, W (-w) = -W w) (hWz : W z ≠ 0) (hz : z ≠ 0)
    (heven : (T z + T (-z)) / 2 = mu1 * Complex.sin (a * z) / (2 * z))
    (hjet : d = I * mu1) :
    ((-I * T z) / W z - (-I * T (-z)) / W (-z)) / 2
      = -d * Complex.sin (a * z) / (2 * z * W z) := by
  have hodd := oddPart_div_of_odd (F := fun w => -I * T w) hW hWz
  rw [hodd]
  have hnum : ((-I * T z) + (-I * T (-z))) / 2 = -I * ((T z + T (-z)) / 2) := by ring
  rw [hnum, heven, hjet]
  field_simp

/-- The compact Fourier transform of an exponential over `[-a, a]`. -/
theorem integral_exp_mul_exp_mul_I_symm (a : ℝ) {c z : ℂ} (h : c + I * z ≠ 0) :
    (∫ y in (-a : ℝ)..a, Complex.exp (c * (y : ℝ)) * Complex.exp (I * z * (y : ℝ)))
      = 2 * Complex.sinh ((c + I * z) * (a : ℂ)) / (c + I * z) := by
  have hcomb : (∫ y in (-a : ℝ)..a,
      Complex.exp (c * (y : ℝ)) * Complex.exp (I * z * (y : ℝ)))
      = ∫ y in (-a : ℝ)..a, Complex.exp ((c + I * z) * (y : ℝ)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [← Complex.exp_add]
    congr 1
    ring
  have hneg : ((c + I * z) * (((-a : ℝ)) : ℂ)) = -((c + I * z) * (a : ℂ)) := by
    push_cast
    ring
  rw [hcomb, integral_exp_mul_complex h, hneg, Complex.two_sinh]

/-- **The exponential edge pair.**  The two shifted exponential transforms combine into the sine
kernel scaled by `4 cosh a`; the shift factors `z ∓ I` cancel the poles of the two transforms. -/
theorem exponentialEdgePair_transform (a : ℝ) {z : ℂ} (hz1 : z ≠ I) (hz2 : z ≠ -I) :
    (z - I) * (∫ y in (-a : ℝ)..a,
        Complex.exp ((y : ℝ)) * Complex.exp (I * z * (y : ℝ)))
      + (z + I) * (∫ y in (-a : ℝ)..a,
        Complex.exp (-((y : ℝ) : ℂ)) * Complex.exp (I * z * (y : ℝ)))
      = 4 * Complex.cosh (a : ℂ) * Complex.sin ((a : ℂ) * z) := by
  have hI : I * I = -1 := Complex.I_mul_I
  have hc1 : (1 : ℂ) + I * z = I * (z - I) := by linear_combination hI
  have hc2 : (-1 : ℂ) + I * z = I * (z + I) := by linear_combination -hI
  have hz1' : z - I ≠ 0 := sub_ne_zero.mpr hz1
  have hz2' : z + I ≠ 0 := fun h => hz2 (by linear_combination h)
  have hne1 : (1 : ℂ) + I * z ≠ 0 := by rw [hc1]; exact mul_ne_zero I_ne_zero hz1'
  have hne2 : (-1 : ℂ) + I * z ≠ 0 := by rw [hc2]; exact mul_ne_zero I_ne_zero hz2'
  have e1 := integral_exp_mul_exp_mul_I_symm a (c := (1 : ℂ)) (z := z) hne1
  have e2 := integral_exp_mul_exp_mul_I_symm a (c := (-1 : ℂ)) (z := z) hne2
  simp only [one_mul] at e1
  have hnegexp : ∀ y : ℝ, Complex.exp ((-1 : ℂ) * (y : ℝ)) = Complex.exp (-((y : ℝ) : ℂ)) := by
    intro y
    congr 1
    ring
  rw [intervalIntegral.integral_congr (fun y _ => by rw [hnegexp y])] at e2
  rw [e1, e2, hc1, hc2]
  set E : ℂ := Complex.exp ((a : ℂ) * z * I) with hE
  set E' : ℂ := Complex.exp (-((a : ℂ) * z * I)) with hE'
  have hexp1 : Complex.exp (I * (z - I) * (a : ℂ)) = Complex.exp ((a : ℂ)) * E := by
    rw [hE, ← Complex.exp_add]
    congr 1
    linear_combination -(a : ℂ) * hI
  have hexp2 : Complex.exp (-(I * (z - I) * (a : ℂ))) = Complex.exp (-(a : ℂ)) * E' := by
    rw [hE', ← Complex.exp_add]
    congr 1
    linear_combination (a : ℂ) * hI
  have hexp3 : Complex.exp (I * (z + I) * (a : ℂ)) = Complex.exp (-(a : ℂ)) * E := by
    rw [hE, ← Complex.exp_add]
    congr 1
    linear_combination (a : ℂ) * hI
  have hexp4 : Complex.exp (-(I * (z + I) * (a : ℂ))) = Complex.exp ((a : ℂ)) * E' := by
    rw [hE', ← Complex.exp_add]
    congr 1
    linear_combination -(a : ℂ) * hI
  have hs1 := Complex.two_sinh (I * (z - I) * (a : ℂ))
  have hs2 := Complex.two_sinh (I * (z + I) * (a : ℂ))
  rw [hexp1, hexp2] at hs1
  rw [hexp3, hexp4] at hs2
  have hcosh := Complex.two_cosh (a : ℂ)
  have hsin := Complex.two_sinh ((a : ℂ) * z * I)
  rw [Complex.sinh_mul_I, ← hE, ← hE'] at hsin
  have hsum : 2 * Complex.sinh (I * (z - I) * (a : ℂ))
      + 2 * Complex.sinh (I * (z + I) * (a : ℂ))
      = 4 * I * Complex.cosh (a : ℂ) * Complex.sin ((a : ℂ) * z) := by
    rw [hs1, hs2]
    linear_combination (-(E - E')) * hcosh + (-2 * Complex.cosh (a : ℂ)) * hsin
  have hstep : (z - I) * (2 * Complex.sinh (I * (z - I) * (a : ℂ)) / (I * (z - I)))
      + (z + I) * (2 * Complex.sinh (I * (z + I) * (a : ℂ)) / (I * (z + I)))
      = (2 * Complex.sinh (I * (z - I) * (a : ℂ))
          + 2 * Complex.sinh (I * (z + I) * (a : ℂ))) / I := by
    field_simp
  rw [hstep, hsum]
  field_simp

/-- **Central jet of the edge-pair transform.**  Differentiating the limit kernel at the origin
returns the aperture-weighted edge mass `4 a cosh a`. -/
theorem deriv_edgePairKernel_zero (a : ℝ) :
    deriv (fun z : ℂ => 4 * Complex.cosh (a : ℂ) * Complex.sin ((a : ℂ) * z)) 0
      = 4 * (a : ℂ) * Complex.cosh (a : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) * z) (a : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (a : ℂ)
  have h2 := (Complex.hasDerivAt_sin ((a : ℂ) * 0)).comp 0 h1
  have h3 := h2.const_mul (4 * Complex.cosh (a : ℂ))
  have h3' : HasDerivAt (fun z : ℂ => 4 * Complex.cosh (a : ℂ) * Complex.sin ((a : ℂ) * z))
      (4 * Complex.cosh (a : ℂ) * (Complex.cos ((a : ℂ) * 0) * (a : ℂ))) 0 := h3
  rw [h3'.deriv]
  simp
  ring

/-- **Modulus of the Fourier kernel.**  `‖exp (I z t)‖ = exp (-(Im z) t)` for real `t`: the real
part of `I z t` is `-(Im z) t`.  This is the factor every domination argument for a compact Fourier
transform needs, since on a bounded interval it is bounded by `exp (|Im z| * A)`. -/
theorem norm_fourierKernel (z : ℂ) (t : ℝ) :
    ‖Complex.exp (I * z * (t : ℝ))‖ = Real.exp (-z.im * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- On a symmetric interval the Fourier kernel is bounded by `exp (|Im z| * a)`. -/
theorem norm_fourierKernel_le (z : ℂ) {a t : ℝ} (ht : |t| ≤ a) :
    ‖Complex.exp (I * z * (t : ℝ))‖ ≤ Real.exp (|z.im| * a) := by
  rw [norm_fourierKernel]
  apply Real.exp_le_exp.mpr
  have h1 : -z.im * t ≤ |(-z.im) * t| := le_abs_self _
  have h2 : |(-z.im) * t| = |z.im| * |t| := by
    rw [abs_mul, abs_neg]
  nlinarith [abs_nonneg z.im, abs_nonneg t, le_trans (abs_nonneg t) ht]

/-- **Domination transfer through the Fourier kernel.**  A dominating bound for the amplitude on a
symmetric interval transfers to one for the amplitude times the kernel, at the cost of the constant
`exp (|Im z| a)`.

This is the step that reduces the domination hypothesis of parametric differentiation under a
compact Fourier transform to a bound on the amplitude family alone. -/
theorem norm_mul_fourierKernel_le {f : ℝ → ℂ} {bound : ℝ → ℝ} {z : ℂ} {a t : ℝ}
    (ht : |t| ≤ a) (hf : ‖f t‖ ≤ bound t) :
    ‖f t * Complex.exp (I * z * (t : ℝ))‖ ≤ Real.exp (|z.im| * a) * bound t := by
  rw [norm_mul]
  have hk := norm_fourierKernel_le z ht
  have hb : 0 ≤ bound t := le_trans (norm_nonneg _) hf
  calc ‖f t‖ * ‖Complex.exp (I * z * (t : ℝ))‖
      ≤ bound t * Real.exp (|z.im| * a) :=
        mul_le_mul hf hk (norm_nonneg _) hb
    _ = Real.exp (|z.im| * a) * bound t := by ring

end

end GaloisForLFunctions.HTGeometry
