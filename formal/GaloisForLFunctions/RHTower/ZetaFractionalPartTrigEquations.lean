import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar

/-!
# Cosine and sine halves of the fractional-part representation of zeta

On the right half-plane the zeta function is

`ζ(s) = s/(s-1) - s ∫_1^∞ {x} x^(-s-1) dx`,

with `{x} = x - ⌊x⌋`.  Writing `s = a + i b` and splitting `x^(-s-1)` into its polar coordinates
turns the single complex integral into the two real integrals

`∫_1^∞ {x} x^(-a-1) cos (b log x) dx`,  `∫_1^∞ {x} x^(-a-1) sin (b log x) dx`,

whose values are the real and the negated imaginary part of `1/(s-1) - ζ(s)/s`.

At a zero of `ζ` inside the critical strip the two integrals — and the two obtained by reflecting
`s ↦ 1 - s`, where `ζ` also vanishes — take the four explicit rational values

`(a-1)/((a-1)²+b²)`, `b/((a-1)²+b²)`, `-a/(a²+b²)`, `b/(a²+b²)`.
-/

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The representation in multiplied form -/

/-- **The fractional-part representation of `ζ`.**  On `Re s > 0`, off the pole. -/
theorem riemannZeta_eq_sub_mul_integral_fract {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s =
      s / (s - 1) - s * ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hsne : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [integral_Ioi_one_fract_cpow_of_re_pos hs hs1]
  field_simp
  ring

/-- **The reflected fractional-part representation.**  Equation `(1)` read at `1 - s`. -/
theorem riemannZeta_one_sub_eq_sub_mul_integral_fract {s : ℂ} (hs : s.re < 1) (hs0 : s ≠ 0) :
    riemannZeta (1 - s) =
      (1 - s) / (-s) -
        (1 - s) * ∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((1 - s) + 1)) := by
  have hre : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hne : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have h := riemannZeta_eq_sub_mul_integral_fract hre hne
  rw [show (1 : ℂ) - s - 1 = -s by ring] at h
  exact h

/-- **At a zero the Mellin integral of the fractional part is a pure pole term.**  Equation `(1)`
with `ζ(s) = 0` and `s ≠ 0` reduces to `∫_1^∞ {x} x^(-s-1) dx = 1/(s-1)`. -/
theorem integral_Ioi_one_fract_cpow_of_zeta_eq_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∫ x in Ioi (1 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) = 1 / (s - 1) := by
  rw [integral_Ioi_one_fract_cpow_of_re_pos hs hs1, hz, zero_div, sub_zero]

/-! ## Polar split of the kernel -/

theorem fract_cpow_re {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).re
      = Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x) := by
  rw [Complex.re_ofReal_mul, ofReal_cpow_re hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.neg_im, Complex.add_im,
    Complex.one_im, add_zero, neg_mul, Real.cos_neg]
  ring

theorem fract_cpow_im {s : ℂ} {x : ℝ} (hx : 0 < x) :
    (((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).im
      = -(Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x)) := by
  have h : (((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).im
      = Int.fract x * ((x : ℂ) ^ (-(s + 1))).im := by
    simp [Complex.mul_im]
  rw [h, ofReal_cpow_im hx]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.neg_im, Complex.add_im,
    Complex.one_im, add_zero, neg_mul, Real.sin_neg]
  ring

/-! ## The two real integrals -/

theorem integrableOn_Ioi_one_fract_rpow_cos {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ => Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x)) (Ioi 1) := by
  have h : IntegrableOn
      (fun x : ℝ => (((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).re) (Ioi 1) := by
    have h0 := (integrableOn_Ioi_one_fract_cpow hs).re
    simp only [RCLike.re_to_complex] at h0
    exact h0
  exact h.congr_fun (fun x hx => fract_cpow_re (lt_trans one_pos (mem_Ioi.mp hx)))
    measurableSet_Ioi

theorem integrableOn_Ioi_one_fract_rpow_sin {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun x : ℝ => Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x)) (Ioi 1) := by
  have h : IntegrableOn
      (fun x : ℝ => -(((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).im) (Ioi 1) := by
    have h0 := ((integrableOn_Ioi_one_fract_cpow hs).im).neg
    simp only [RCLike.im_to_complex, Pi.neg_def] at h0
    exact h0
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show -((((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))).im) = _
  rw [fract_cpow_im (lt_trans one_pos (mem_Ioi.mp hx)), neg_neg]

/-- **The cosine half.**  Unconditional on the punctured right half-plane. -/
theorem integral_Ioi_one_fract_rpow_cos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x))
      = (1 / (s - 1) - riemannZeta s / s).re := by
  have hI := _root_.integral_re (integrableOn_Ioi_one_fract_cpow hs)
  simp only [RCLike.re_to_complex] at hI
  rw [← integral_Ioi_one_fract_cpow_of_re_pos hs hs1, ← hI]
  exact setIntegral_congr_fun measurableSet_Ioi
    fun x hx => (fract_cpow_re (lt_trans one_pos (mem_Ioi.mp hx))).symm

/-- **The sine half.**  Unconditional on the punctured right half-plane. -/
theorem integral_Ioi_one_fract_rpow_sin {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x))
      = -(1 / (s - 1) - riemannZeta s / s).im := by
  have hI := _root_.integral_im (integrableOn_Ioi_one_fract_cpow hs)
  simp only [RCLike.im_to_complex] at hI
  rw [← integral_Ioi_one_fract_cpow_of_re_pos hs hs1, ← hI, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [fract_cpow_im (lt_trans one_pos (mem_Ioi.mp hx)), neg_neg]

/-! ## The four equations at a zero in the critical strip -/

theorem re_one_div_sub_one (s : ℂ) :
    (1 / (s - 1)).re = (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring_nf

theorem im_one_div_sub_one (s : ℂ) :
    (1 / (s - 1)).im = -s.im / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  rw [one_div, Complex.inv_im, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring_nf

theorem ne_one_of_re_lt_one {s : ℂ} (h1 : s.re < 1) : s ≠ 1 := by
  intro h
  rw [h, Complex.one_re] at h1
  exact lt_irrefl 1 h1

/-- **The cosine equation at a zero.** -/
theorem integral_Ioi_one_fract_rpow_cos_of_zeta_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) * Real.cos (s.im * Real.log x))
      = (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  rw [integral_Ioi_one_fract_rpow_cos h0 (ne_one_of_re_lt_one h1), hz, zero_div, sub_zero,
    re_one_div_sub_one s]

/-- **The sine equation at a zero.** -/
theorem integral_Ioi_one_fract_rpow_sin_of_zeta_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (-(s.re + 1)) * Real.sin (s.im * Real.log x))
      = s.im / ((s.re - 1) ^ 2 + s.im ^ 2) := by
  rw [integral_Ioi_one_fract_rpow_sin h0 (ne_one_of_re_lt_one h1), hz, zero_div, sub_zero,
    im_one_div_sub_one s]
  ring

/-! ## The reflected pair -/

/-- **The reflected cosine equation at a zero.** -/
theorem integral_Ioi_one_fract_rpow_cos_reflected_of_zeta_eq_zero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (s.re - 2) * Real.cos (s.im * Real.log x))
      = -s.re / (s.re ^ 2 + s.im ^ 2) := by
  have hw0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 - s).re < 1 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hzw : riemannZeta (1 - s) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).mpr hz
  have h := integral_Ioi_one_fract_rpow_cos_of_zeta_eq_zero hw0 hw1 hzw
  have hexp : -((1 - s).re + 1) = s.re - 2 := by rw [Complex.sub_re, Complex.one_re]; ring
  have him : (1 - s).im = -s.im := by rw [Complex.sub_im, Complex.one_im]; ring
  rw [hexp, him] at h
  have hL : (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (s.re - 2) * Real.cos (-s.im * Real.log x))
      = ∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (s.re - 2) * Real.cos (s.im * Real.log x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [neg_mul, Real.cos_neg]
  rw [hL, Complex.sub_re, Complex.one_re] at h
  rw [h]
  ring_nf

/-- **The reflected sine equation at a zero.** -/
theorem integral_Ioi_one_fract_rpow_sin_reflected_of_zeta_eq_zero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    (∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (s.re - 2) * Real.sin (s.im * Real.log x))
      = s.im / (s.re ^ 2 + s.im ^ 2) := by
  have hw0 : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hw1 : (1 - s).re < 1 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hzw : riemannZeta (1 - s) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).mpr hz
  have h := integral_Ioi_one_fract_rpow_sin_of_zeta_eq_zero hw0 hw1 hzw
  have hexp : -((1 - s).re + 1) = s.re - 2 := by rw [Complex.sub_re, Complex.one_re]; ring
  have him : (1 - s).im = -s.im := by rw [Complex.sub_im, Complex.one_im]; ring
  rw [hexp, him] at h
  have hneg : (∫ x in Ioi (1 : ℝ),
      Int.fract x * x ^ (s.re - 2) * Real.sin (-s.im * Real.log x))
      = -∫ x in Ioi (1 : ℝ), Int.fract x * x ^ (s.re - 2) * Real.sin (s.im * Real.log x) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [neg_mul, Real.sin_neg]
    ring
  rw [hneg, Complex.sub_re, Complex.one_re] at h
  have hden : (1 - s.re - 1) ^ 2 + (-s.im) ^ 2 = s.re ^ 2 + s.im ^ 2 := by ring
  rw [hden, neg_div] at h
  linarith [h]

end RHTower
