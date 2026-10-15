import GaloisForLFunctions.RHTower.ThetaRenewalFeedbackLoop

/-!
# The physical renewal charge on the full upper critical strip

The antisymmetric channel `C = (A - B)/(2i)` extends the positive boundary
charge `v(y)` from `iy` to the whole upper critical strip. Its real part is
strictly positive there, by the two denominator quadrant laws. Consequently
`F/C`, with `F(lambda) = XiC(2i lambda)`, retains every zero and its exact
analytic order, without selecting critical-line or simple zeros.

This is a divisor-preserving normalization, not a proof of divisor orientation.
At simple critical zeros its real boundary slope is `-d(y)`; both slope signs
remain. No positivity of the resulting quotient is asserted.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Analytic extension of the physical imaginary boundary charge. -/
def thetaRenewalFullCharge (lam : ℂ) : ℂ :=
  (thetaLoopA lam - thetaLoopB lam) / (2 * I)

/-- Normalize the two-ended function by its physical charge. -/
def thetaRenewalChargedQuotient (lam : ℂ) : ℂ :=
  XiC (2 * I * lam) / thetaRenewalFullCharge lam

theorem differentiable_thetaRenewalFullCharge :
    Differentiable ℂ thetaRenewalFullCharge :=
  (differentiable_thetaLoopA.sub differentiable_thetaLoopB).div_const _

/-- The forward channel is in the upper half-plane throughout the upper strip. -/
theorem im_thetaLoopA_pos {lam : ℂ} (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    0 < (thetaLoopA lam).im := by
  obtain ⟨hDr, hDi, -, -⟩ := thetaRenewalDenominator_quadrant hs hy
  have hx : 0 < 1 / 4 + lam.re := by linarith [abs_lt.mp hs]
  change 0 < ((1 / 4 + lam) * thetaRenewalDenominator lam).im
  simp only [mul_im, add_re, add_im, div_ofNat_re, div_ofNat_im, one_re, one_im,
    zero_div, zero_add]
  exact add_pos (mul_pos hx hDi) (mul_pos hy hDr)

/-- The reflected channel is in the lower half-plane throughout the upper strip. -/
theorem im_thetaLoopB_neg {lam : ℂ} (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    (thetaLoopB lam).im < 0 := by
  obtain ⟨-, -, hDr, hDi⟩ := thetaRenewalDenominator_quadrant hs hy
  have hx : 0 < 1 / 4 - lam.re := by linarith [abs_lt.mp hs]
  change ((1 / 4 - lam) * thetaRenewalDenominator (-lam)).im < 0
  simp only [mul_im, sub_re, sub_im, div_ofNat_re, div_ofNat_im, one_re, one_im,
    zero_div, zero_sub]
  exact add_neg (mul_neg_of_pos_of_neg hx hDi)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hy) hDr)

theorem re_thetaRenewalFullCharge (lam : ℂ) :
    (thetaRenewalFullCharge lam).re =
      ((thetaLoopA lam).im - (thetaLoopB lam).im) / 2 := by
  simp [thetaRenewalFullCharge, Complex.div_re, Complex.normSq_apply]
  ring

/-- Strict positivity uses the source quadrant law, with no zero-location premise. -/
theorem re_thetaRenewalFullCharge_pos {lam : ℂ}
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    0 < (thetaRenewalFullCharge lam).re := by
  rw [re_thetaRenewalFullCharge]
  linarith [im_thetaLoopA_pos hs hy, im_thetaLoopB_neg hs hy]

theorem thetaRenewalFullCharge_ne_zero {lam : ℂ}
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    thetaRenewalFullCharge lam ≠ 0 := by
  intro h
  have hp := re_thetaRenewalFullCharge_pos hs hy
  rw [h, zero_re] at hp
  exact (lt_irrefl 0) hp

/-- The extension agrees exactly with the original boundary charge. -/
theorem thetaRenewalFullCharge_I_mul (y : ℝ) :
    thetaRenewalFullCharge (y * I) = (thetaLoopCharge y : ℂ) := by
  rw [thetaRenewalFullCharge, thetaLoopB_I_mul]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, thetaLoopCharge]
  ring

theorem thetaRenewalFullCharge_neg (lam : ℂ) :
    thetaRenewalFullCharge (-lam) = -thetaRenewalFullCharge lam := by
  simp only [thetaRenewalFullCharge, thetaLoopA, thetaLoopB, neg_neg]
  ring

/-- Reflection across the critical axis is ordinary conjugation after charge normalization. -/
theorem thetaRenewalFullCharge_reflect (x y : ℝ) :
    thetaRenewalFullCharge (-x + y * I) = conj (thetaRenewalFullCharge (x + y * I)) := by
  have hA : thetaLoopA (-x + y * I) = conj (thetaLoopB (x + y * I)) := by
    simp only [thetaLoopB_eq_conj, starRingEnd_self_apply]
  have hB : thetaLoopB (-x + y * I) = conj (thetaLoopA (x + y * I)) := by
    simpa using thetaLoopB_eq_conj (-x) y
  rw [thetaRenewalFullCharge, hA, hB, thetaRenewalFullCharge, map_div₀, map_sub]
  simp only [map_mul, map_ofNat, conj_I]
  ring

theorem analyticAt_thetaRenewalChargedQuotient {lam : ℂ}
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    AnalyticAt ℂ thetaRenewalChargedQuotient lam := by
  exact ((XiC_differentiable.comp (differentiable_id.const_mul (2 * I))).analyticAt lam).div
    (differentiable_thetaRenewalFullCharge.analyticAt lam)
    (thetaRenewalFullCharge_ne_zero hs hy)

theorem thetaRenewalChargedQuotient_eq_zero_iff {lam : ℂ}
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    thetaRenewalChargedQuotient lam = 0 ↔ XiC (2 * I * lam) = 0 := by
  simp only [thetaRenewalChargedQuotient, div_eq_zero_iff,
    thetaRenewalFullCharge_ne_zero hs hy, or_false]

/-- Every multiplicity is preserved, including nonreal and multiple zeros. -/
theorem analyticOrderAt_thetaRenewalChargedQuotient {lam : ℂ}
    (hs : |lam.re| < 1 / 4) (hy : 0 < lam.im) :
    analyticOrderAt thetaRenewalChargedQuotient lam =
      analyticOrderAt (fun z => XiC (2 * I * z)) lam := by
  have hF : AnalyticAt ℂ (fun z => XiC (2 * I * z)) lam :=
    (XiC_differentiable.comp (differentiable_id.const_mul (2 * I))).analyticAt lam
  have hC : AnalyticAt ℂ (fun z => (thetaRenewalFullCharge z)⁻¹) lam :=
    (differentiable_thetaRenewalFullCharge.analyticAt lam).inv
    (thetaRenewalFullCharge_ne_zero hs hy)
  have horder : analyticOrderAt (fun z => (thetaRenewalFullCharge z)⁻¹) lam = 0 :=
    hC.analyticOrderAt_eq_zero.mpr (inv_ne_zero (thetaRenewalFullCharge_ne_zero hs hy))
  change analyticOrderAt ((fun z => XiC (2 * I * z)) *
    (fun z => (thetaRenewalFullCharge z)⁻¹)) lam = _
  rw [analyticOrderAt_mul hF hC, horder, add_zero]

theorem thetaRenewalChargedQuotient_I_mul (y : ℝ) :
    thetaRenewalChargedQuotient (y * I) = ((Xi (2 * y) / thetaLoopCharge y : ℝ) : ℂ) := by
  rw [thetaRenewalChargedQuotient, thetaRenewalFullCharge_I_mul,
    show 2 * I * ((y : ℂ) * I) = -((2 * y : ℝ) : ℂ) by
      push_cast; linear_combination (2 * (y : ℂ)) * I_sq,
    XiC_even, XiC_ofReal, ofReal_div]

/-- Normalization preserves the alternating boundary crossing orientations. -/
theorem hasDerivAt_thetaRenewalChargedBoundary_at_zero {y : ℝ}
    (hy : 0 < y) (hzero : Xi (2 * y) = 0) :
    HasDerivAt (fun t => Xi (2 * t) / thetaLoopCharge t)
      (-thetaLoopBoundaryValue y) y := by
  have hX := (hasDerivAt_Xi_deriv (2 * y)).comp y ((hasDerivAt_id y).const_mul 2)
  have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
    simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).comp_ofReal
  have hA := (differentiable_thetaLoopA (y * I)).hasDerivAt.comp y hl
  have hv : HasDerivAt thetaLoopCharge (deriv thetaLoopA (y * I) * I).im y :=
    hasDerivAt_im_comp hA
  have h := hX.div hv (thetaLoopCharge_pos hy).ne'
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, thetaLoopBoundaryValue, thetaLoopSlope_eq_deriv,
    hzero, zero_mul, sub_zero, neg_div, neg_neg, mul_one]
  field_simp [(thetaLoopCharge_pos hy).ne']

/-- The signed cross flux of the two physical renewal channels. -/
def thetaRenewalCrossFlux (lam : ℂ) : ℝ :=
  (thetaLoopA lam * conj (thetaLoopB lam)).im

/-- A zero-safe complex identity keeps both independent channel quadratures. -/
theorem XiC_mul_conj_thetaLoopDifference (lam : ℂ) :
    XiC (2 * I * lam) * conj (thetaLoopA lam - thetaLoopB lam) =
      ((Complex.normSq (thetaLoopA lam) - Complex.normSq (thetaLoopB lam) : ℝ) : ℂ) -
        2 * I * (thetaRenewalCrossFlux lam : ℂ) := by
  rw [XiC_two_I_mul_eq_thetaLoop]
  apply Complex.ext <;>
    simp [thetaRenewalCrossFlux, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring

/-- Full-divisor membership is exactly simultaneous vanishing of energy imbalance
and cross flux. The nonzero charge excludes the constructive channel branch. -/
theorem XiC_eq_zero_iff_thetaRenewal_joint_node {x y : ℝ}
    (hx : |x| < 1 / 4) (hy : 0 < y) :
    XiC (2 * I * (x + y * I)) = 0 ↔
      thetaLoopEnergy x y = 0 ∧ thetaRenewalCrossFlux (x + y * I) = 0 := by
  have h := XiC_mul_conj_thetaLoopDifference (x + y * I)
  have he : ((Complex.normSq (thetaLoopA (x + y * I)) -
      Complex.normSq (thetaLoopB (x + y * I)) : ℝ) : ℂ) =
      (thetaLoopEnergy x y : ℂ) := rfl
  rw [he] at h
  constructor
  · intro hz
    rw [hz, zero_mul] at h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
      re_ofNat, im_ofNat, I_re, I_im, zero_re, zero_im] at hr hi
    constructor <;> nlinarith
  · rintro ⟨hG, hH⟩
    rw [hG, hH, ofReal_zero, mul_zero, sub_zero] at h
    rcases mul_eq_zero.mp h with hF | hD
    · exact hF
    · have hdiff : thetaLoopA (x + y * I) - thetaLoopB (x + y * I) = 0 := by
        simpa using congrArg conj hD
      have hC := thetaRenewalFullCharge_ne_zero
        (lam := x + y * I) (by simpa using hx) (by simpa using hy)
      exact False.elim (hC (by simp [thetaRenewalFullCharge, hdiff]))

end

end RHTower
