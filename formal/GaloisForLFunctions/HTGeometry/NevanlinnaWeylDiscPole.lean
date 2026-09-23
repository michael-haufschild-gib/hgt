import GaloisForLFunctions.HTGeometry.NevanlinnaCarrierDenominatorRow

/-!
# The pole of the Weyl-disc Möbius map lies in the lower half-plane

For `Im z > 0` the map `τ ↦ −(A(z)τ − C(z))/(B(z)τ − D(z))` sends every real parameter to the
Cauchy transform of a probability measure, hence into the open upper half-plane.  Writing the
imaginary part of that fraction as `Q(τ)/‖B(z)τ − D(z)‖²` with

`Q(t) = Im((−A t + C) · conj(B t − D)) = α·normSq t + p·Re t + r·Im t + c`,

the pole `q = D(z)/B(z)` satisfies `Q(q) = 0` because the second factor vanishes there, while
`Q > 0` on the real axis.  Subtracting `Q(Re q)` gives

`α·(Im q)² + r·(Im q) = −Q(Re q) < 0`.

Here `α > 0` because the parameter at infinity already has positive imaginary part, and
`r = Re(A·conj D − C·conj B)` is continuous, equal to `1` on the real axis by the determinant
identity, and nonvanishing on the upper half-plane by the displayed inequality; the upper
half-plane is connected, so `r > 0` there.  Both coefficients being positive forces `Im q < 0`.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## Positivity of the Cauchy transform -/

/-- **The Cauchy transform of a probability measure lands in the upper half-plane.** -/
theorem im_cauchyTransform_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] {z : ℂ}
    (hz : 0 < z.im) : 0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hint : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := integrable_cauchy_kernel μ hz'
  have hIm : (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im = ∫ x, (((x : ℂ) - z)⁻¹).im ∂μ := by
    simpa using (Complex.imCLM.integral_comp_comm hint).symm
  have hpos : ∀ x : ℝ, 0 < (((x : ℂ) - z)⁻¹).im := by
    intro x
    have hne : ((x : ℂ) - z) ≠ 0 := by
      intro hc
      apply hz'
      have hzx : z = ((x : ℝ) : ℂ) := by linear_combination -hc
      rw [hzx]
      simp
    have h1 : ((x : ℂ) - z).im = -z.im := by simp
    rw [Complex.inv_im, h1, neg_neg]
    exact div_pos hz (Complex.normSq_pos.mpr hne)
  rw [hIm]
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hint.im]
  have hsupp : Function.support (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos x).ne'
  rw [hsupp, measure_univ]
  exact zero_lt_one

/-! ## The quadratic form behind the Weyl disc -/

/-- The numerator of the imaginary part of the Möbius image, as a function of the parameter. -/
noncomputable def weylForm (s : ℕ → ℝ) (z t : ℂ) : ℝ :=
  ((-nevAinf s z * t + nevCinf s z) *
    (starRingEnd ℂ) (nevBinf s z * t - nevDinf s z)).im

/-- The coefficient of `normSq t` in the Weyl form. -/
noncomputable def weylLead (s : ℕ → ℝ) (z : ℂ) : ℝ :=
  (-nevAinf s z * (starRingEnd ℂ) (nevBinf s z)).im

/-- The coefficient of `Im t` in the Weyl form. -/
noncomputable def weylTilt (s : ℕ → ℝ) (z : ℂ) : ℝ :=
  (nevAinf s z * (starRingEnd ℂ) (nevDinf s z)).re -
    (nevCinf s z * (starRingEnd ℂ) (nevBinf s z)).re

/-- **The Weyl form is the displayed real quadratic.** -/
theorem weylForm_expand (s : ℕ → ℝ) (z t : ℂ) :
    weylForm s z t
      = weylLead s z * Complex.normSq t
        + ((nevAinf s z * (starRingEnd ℂ) (nevDinf s z)).im
            + (nevCinf s z * (starRingEnd ℂ) (nevBinf s z)).im) * t.re
        + weylTilt s z * t.im
        + (-(nevCinf s z * (starRingEnd ℂ) (nevDinf s z))).im := by
  simp only [weylForm, weylLead, weylTilt, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.sub_im, Complex.sub_re, Complex.neg_im,
    Complex.neg_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The Weyl form vanishes where the denominator does. -/
theorem weylForm_eq_zero_of_denominator (s : ℕ → ℝ) (z t : ℂ)
    (ht : nevBinf s z * t - nevDinf s z = 0) : weylForm s z t = 0 := by
  simp [weylForm, ht]

/-- The Weyl form is the imaginary part of the Möbius image, scaled by the squared denominator. -/
theorem weylForm_eq_im_mul_normSq (s : ℕ → ℝ) (z t : ℂ)
    (ht : nevBinf s z * t - nevDinf s z ≠ 0) :
    weylForm s z t
      = (-(nevAinf s z * t - nevCinf s z) / (nevBinf s z * t - nevDinf s z)).im *
          Complex.normSq (nevBinf s z * t - nevDinf s z) := by
  set N : ℂ := -nevAinf s z * t + nevCinf s z with hN
  set Dn : ℂ := nevBinf s z * t - nevDinf s z with hDn
  have hfrac : -(nevAinf s z * t - nevCinf s z) / Dn = N / Dn := by
    rw [hN]
    ring_nf
  have hkey : N * (starRingEnd ℂ) Dn = ((Complex.normSq Dn : ℝ) : ℂ) * (N / Dn) := by
    rw [← Complex.mul_conj]
    field_simp
  rw [hfrac, weylForm, ← hN, ← hDn, hkey]
  simp [Complex.mul_im, mul_comm]

/-! ## Positivity on the real axis and at infinity -/

/-- **The Weyl form is positive at every real parameter.** -/
theorem weylForm_pos_ofReal (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {z : ℂ} (hz : 0 < z.im) (tau : ℝ) : 0 < weylForm s z (tau : ℂ) := by
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hden := nevInf_denominator_ne_zero h h0b h0 tau hz'
  have hpos := im_cauchyTransform_pos (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) hz
  rw [cauchyTransform_nevLeaf_eq_moebius h h0b h0 tau hz'] at hpos
  rw [weylForm_eq_im_mul_normSq s z (tau : ℂ) hden]
  exact mul_pos hpos (Complex.normSq_pos.mpr hden)

/-- **The leading coefficient of the Weyl form is positive**, because the parameter at infinity
already has positive imaginary part. -/
theorem weylLead_pos (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {z : ℂ} (hz : 0 < z.im) : 0 < weylLead s z := by
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hB := nevBinf_ne_zero h h0b h0 hz'
  have hpos := im_cauchyTransform_pos (nevLeaf h h0b h0 ∞ : Measure ℝ) hz
  rw [cauchyTransform_nevLeafInf_eq_ratio h h0b h0 hz'] at hpos
  have hkey : -nevAinf s z * (starRingEnd ℂ) (nevBinf s z)
      = ((Complex.normSq (nevBinf s z) : ℝ) : ℂ) * (-nevAinf s z / nevBinf s z) := by
    rw [← Complex.mul_conj]
    field_simp
  have hval : weylLead s z
      = (-nevAinf s z / nevBinf s z).im * Complex.normSq (nevBinf s z) := by
    rw [weylLead, hkey]
    simp [Complex.mul_im, mul_comm]
  rw [hval]
  exact mul_pos hpos (Complex.normSq_pos.mpr hB)

/-! ## The tilt coefficient -/

/-- The tilt coefficient is continuous. -/
theorem continuous_weylTilt (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) :
    Continuous (weylTilt s) := by
  obtain ⟨hA, hB, hC, hD, _⟩ := nevanlinna_entire_unimodular h h0b
  have hcA : Continuous (nevAinf s) := hA.continuous
  have hcB : Continuous (nevBinf s) := hB.continuous
  have hcC : Continuous (nevCinf s) := hC.continuous
  have hcD : Continuous (nevDinf s) := hD.continuous
  have hstar : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  exact (Complex.continuous_re.comp (hcA.mul (hstar.comp hcD))).sub
    (Complex.continuous_re.comp (hcC.mul (hstar.comp hcB)))

/-- On the real axis the tilt coefficient is the determinant, namely `1`. -/
theorem weylTilt_ofReal (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (x : ℝ) :
    weylTilt s ((x : ℝ) : ℂ) = 1 := by
  have hdet := nev_realInf_det_one h h0b x
  rw [weylTilt, nevAinf_ofReal, nevBinf_ofReal, nevCinf_ofReal, nevDinf_ofReal]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith [hdet]

/-- **The tilt coefficient does not vanish on the upper half-plane.**  A vanishing tilt would leave
`α·(Im q)² = −Q(Re q) < 0` with `α > 0`. -/
theorem weylTilt_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {z : ℂ} (hz : 0 < z.im) : weylTilt s z ≠ 0 := by
  intro htilt
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hB := nevBinf_ne_zero h h0b h0 hz'
  set q : ℂ := nevDinf s z / nevBinf s z with hq
  have hqden : nevBinf s z * q - nevDinf s z = 0 := by
    rw [hq]
    field_simp
    ring
  have hQq : weylForm s z q = 0 := weylForm_eq_zero_of_denominator s z q hqden
  have hQre : 0 < weylForm s z ((q.re : ℝ) : ℂ) := weylForm_pos_ofReal h h0b h0 hz q.re
  have hdiff : weylForm s z q - weylForm s z ((q.re : ℝ) : ℂ)
      = weylLead s z * q.im ^ (2 : ℕ) + weylTilt s z * q.im := by
    rw [weylForm_expand, weylForm_expand]
    simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hQq, htilt] at hdiff
  have hlead := weylLead_pos h h0b h0 hz
  nlinarith [sq_nonneg q.im, hQre, hlead, hdiff]

/-- **The tilt coefficient is positive on the upper half-plane.**  It is continuous, equal to `1`
on the real axis, and nonvanishing above it, and the upper half-plane is connected. -/
theorem weylTilt_pos (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {z : ℂ} (hz : 0 < z.im) : 0 < weylTilt s z := by
  have hcont := continuous_weylTilt h h0b
  set S : Set ℂ := {w : ℂ | (0 : ℝ) < w.im} with hS
  have hpre : IsPreconnected S := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  -- a point of `S` where the tilt is positive, found near the real axis
  have hzero : weylTilt s ((0 : ℝ) : ℂ) = 1 := weylTilt_ofReal h h0b 0
  have hopen : IsOpen {w : ℂ | 0 < weylTilt s w} :=
    isOpen_lt continuous_const hcont
  have hmem : ((0 : ℝ) : ℂ) ∈ {w : ℂ | 0 < weylTilt s w} := by
    simp only [Set.mem_setOf_eq, hzero]
    exact zero_lt_one
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  set w : ℂ := Complex.I * ((δ / 2 : ℝ) : ℂ) with hw
  have hwmem : w ∈ Metric.ball (((0 : ℝ) : ℂ)) δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simp only [hw, Complex.ofReal_zero, sub_zero]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hwpos : 0 < weylTilt s w := hball hwmem
  have hwS : w ∈ S := by
    simp only [hS, Set.mem_setOf_eq, hw]
    rw [Complex.mul_im]
    simp
    linarith
  have hzS : z ∈ S := hz
  by_contra hneg
  have hneg' : weylTilt s z < 0 :=
    lt_of_le_of_ne (not_lt.mp hneg) (weylTilt_ne_zero h h0b h0 hz)
  have hsub := hpre.intermediate_value hzS hwS hcont.continuousOn
  have hmem0 : (0 : ℝ) ∈ Set.Icc (weylTilt s z) (weylTilt s w) :=
    ⟨hneg'.le, hwpos.le⟩
  obtain ⟨v, hvS, hv⟩ := hsub hmem0
  exact weylTilt_ne_zero h h0b h0 hvS hv

/-! ## The pole -/

/-- **The pole of the Weyl-disc Möbius map lies strictly below the real axis.** -/
theorem nevInf_quotient_im_neg (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {z : ℂ} (hz : 0 < z.im) :
    (nevDinf s z / nevBinf s z).im < 0 := by
  have hz' : z.im ≠ 0 := ne_of_gt hz
  have hB := nevBinf_ne_zero h h0b h0 hz'
  set q : ℂ := nevDinf s z / nevBinf s z with hq
  have hqden : nevBinf s z * q - nevDinf s z = 0 := by
    rw [hq]
    field_simp
    ring
  have hQq : weylForm s z q = 0 := weylForm_eq_zero_of_denominator s z q hqden
  have hQre : 0 < weylForm s z ((q.re : ℝ) : ℂ) := weylForm_pos_ofReal h h0b h0 hz q.re
  have hdiff : weylForm s z q - weylForm s z ((q.re : ℝ) : ℂ)
      = weylLead s z * q.im ^ (2 : ℕ) + weylTilt s z * q.im := by
    rw [weylForm_expand, weylForm_expand]
    simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hQq] at hdiff
  have hlead := weylLead_pos h h0b h0 hz
  have htilt := weylTilt_pos h h0b h0 hz
  by_contra hge
  have hge' : 0 ≤ q.im := not_lt.mp hge
  nlinarith [mul_nonneg hlead.le (mul_nonneg hge' hge'), mul_nonneg htilt.le hge']

/-- **The quotient of the constructed carrier family lands in the lower half-plane.**  This is the
sign the `upperMap` field of `MaximalTranslationInputs` gets backwards. -/
theorem analyticNevCarrierFamily_quotient_im_neg (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {z : ℂ} (hz : 0 < z.im) :
    ((analyticNevCarrierFamily h h0b h0).quotient z).im < 0 := by
  rw [analyticNevCarrierFamily_quotient h h0b h0 z]
  exact nevInf_quotient_im_neg h h0b h0 hz

end HTGeometry
