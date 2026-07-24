import GaloisForLFunctions.RHTower.XiWeilCriterionConverse
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Unconditional positivity of the Weil form outside the critical strip

Every Gram term of the diagonal Weil form factors as

`K z (pt) · K (conj z) (pt) = normSq z / (pt² · ((pt − x)² + y²))`,  `z = x + iy`,

so its sign is the sign of the real part of `D = pt² · ((pt − x)² + y²)`, namely

`Re D = (u² − v²)((u − x)² + y² − v²) − 4uv²(u − x)`,  `pt = u + iv`.

The divisor obeys `|v| < 1/2`, so the bracket is positive as soon as `y² > 1/4`,
and the certified height floor `u² > 32` makes the leading product dominate the
correction.  Hence the Weil form is unconditionally positive off the closed strip
`|Im z| ≤ 1/2` — the sign of the Weil quadratic form is decided everywhere except
in the thin strip where the zeros themselves live.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## §1 The real-variable sign condition -/

/-- **The Gram sign condition.**  With the divisor constraints `u² ≥ 32` and
`v² ≤ 1/4`, a base point with `y² ≥ 27/100` forces the real part of the Gram
denominator to be positive, uniformly in the height `u` and the abscissa `x`. -/
theorem weilGram_denom_re_pos {u v x y : ℝ} (hu : 32 ≤ u ^ 2)
    (hv : v ^ 2 ≤ 1 / 4) (hy : 27 / 100 ≤ y ^ 2) :
    0 < (u ^ 2 - v ^ 2) * ((u - x) ^ 2 + y ^ 2 - v ^ 2) -
      4 * u * v ^ 2 * (u - x) := by
  set b := u - x with hbdef
  set X := (u ^ 2 - v ^ 2) * (b ^ 2 + y ^ 2 - v ^ 2) - 4 * u * v ^ 2 * b with hX
  have hv0 : 0 ≤ v ^ 2 := sq_nonneg v
  have hP : 0 < u ^ 2 - v ^ 2 := by nlinarith
  have hc : 1 / 50 ≤ y ^ 2 - v ^ 2 := by linarith
  have hv4 : v ^ 4 ≤ 1 / 16 := by nlinarith
  have hbig : 4 * u ^ 2 * v ^ 4 < (u ^ 2 - v ^ 2) ^ 2 * (1 / 50) := by
    nlinarith [hv4, hv0, hu, hv, sq_nonneg (u ^ 2 - 32)]
  have hsq : 0 ≤ ((u ^ 2 - v ^ 2) * b - 2 * u * v ^ 2) ^ 2 := sq_nonneg _
  have hmain : 0 < (u ^ 2 - v ^ 2) * X := by
    have hexp : (u ^ 2 - v ^ 2) * X =
        ((u ^ 2 - v ^ 2) * b - 2 * u * v ^ 2) ^ 2 - 4 * u ^ 2 * v ^ 4 +
          (u ^ 2 - v ^ 2) ^ 2 * (y ^ 2 - v ^ 2) := by
      rw [hX]
      ring
    rw [hexp]
    nlinarith [hsq, hbig, hc, mul_le_mul_of_nonneg_left hc
      (sq_nonneg (u ^ 2 - v ^ 2))]
  by_contra hcon
  push Not at hcon
  have hnp : (u ^ 2 - v ^ 2) * X ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP.le hcon
  linarith [hmain, hnp]

/-! ## §2 The Gram term off the strip -/

/-- The regularized Cauchy kernel in closed form. -/
theorem xiCauchyRegularizedKernel_eq_div {z w : ℂ} (hw : w ≠ 0) (hwz : w ≠ z) :
    xiCauchyRegularizedKernel z w = -z / (w * (w - z)) := by
  have hwz0 : w - z ≠ 0 := sub_ne_zero.mpr hwz
  unfold xiCauchyRegularizedKernel
  field_simp
  ring

/-- The product of the two kernels of a diagonal Gram term, in closed form. -/
theorem weilGram_term_eq_div {z w : ℂ} (hw : w ≠ 0) (hwz : w ≠ z)
    (hwzc : w ≠ (starRingEnd ℂ) z) :
    xiCauchyRegularizedKernel z w *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) z) w =
      ((Complex.normSq z : ℝ) : ℂ) /
        (w ^ 2 * ((w - (z.re : ℂ)) ^ 2 + ((z.im : ℂ)) ^ 2)) := by
  have hwz0 : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hwzc0 : w - (starRingEnd ℂ) z ≠ 0 := sub_ne_zero.mpr hwzc
  rw [xiCauchyRegularizedKernel_eq_div hw hwz,
    xiCauchyRegularizedKernel_eq_div hw hwzc]
  have hfac : (w - (z.re : ℂ)) ^ 2 + ((z.im : ℂ)) ^ 2 =
      (w - z) * (w - (starRingEnd ℂ) z) := by
    have h1 : (w - z) * (w - (starRingEnd ℂ) z) =
        w ^ 2 - (z + (starRingEnd ℂ) z) * w + z * (starRingEnd ℂ) z := by
      ring
    rw [h1, Complex.add_conj, Complex.mul_conj, Complex.normSq_apply]
    push_cast
    ring
  rw [hfac]
  have hnorm : ((Complex.normSq z : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    rw [Complex.mul_conj]
  rw [hnorm]
  field_simp

/-- **Positivity of a Gram term off the strip.**  Every divisor copy contributes
a term of positive real part whenever the base point stays clear of the strip. -/
theorem weilGram_term_re_nonneg {z : ℂ} (hy : 27 / 100 ≤ z.im ^ 2)
    (q : XiZeroCopy) :
    0 ≤ (xiCauchyRegularizedKernel z (xiSpectralPoint q) *
      xiCauchyRegularizedKernel ((starRingEnd ℂ) z)
        (xiSpectralPoint q)).re := by
  set w := xiSpectralPoint q with hw
  have hu : 32 ≤ w.re ^ 2 := le_of_lt (xiSpectral_re_sq_gt_thirtytwo q)
  have hvlt : |w.im| < 1 / 2 := abs_im_xiSpectralPoint_lt_half q
  have hv : w.im ^ 2 ≤ 1 / 4 := by
    have h := abs_lt.mp hvlt
    nlinarith [h.1, h.2]
  have hw0 : w ≠ 0 := xiSpectralPoint_ne_zero q
  have hwz : w ≠ z := by
    intro h
    rw [h] at hv
    nlinarith [hv, hy]
  have hwzc : w ≠ (starRingEnd ℂ) z := by
    intro h
    have him : w.im = -z.im := by rw [h]; simp
    rw [him] at hv
    nlinarith [hv, hy]
  rw [weilGram_term_eq_div hw0 hwz hwzc]
  set D : ℂ := w ^ 2 * ((w - (z.re : ℂ)) ^ 2 + ((z.im : ℂ)) ^ 2) with hD
  have hDre : D.re =
      (w.re ^ 2 - w.im ^ 2) *
          ((w.re - z.re) ^ 2 + z.im ^ 2 - w.im ^ 2) -
        4 * w.re * w.im ^ 2 * (w.re - z.re) := by
    rw [hD]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      pow_two]
    ring
  have hDpos : 0 < D.re := by
    rw [hDre]
    exact weilGram_denom_re_pos hu hv hy
  have hDne : D ≠ 0 := by
    intro h
    rw [h] at hDpos
    simp at hDpos
  rw [Complex.div_re]
  have hns : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hnsD : 0 < Complex.normSq D := Complex.normSq_pos.mpr hDne
  have h1 : 0 ≤ (Complex.normSq z : ℝ) * D.re / Complex.normSq D := by
    apply div_nonneg (mul_nonneg hns hDpos.le) hnsD.le
  simpa [Complex.ofReal_im] using h1

/-! ## §3 The decided region -/

/-- Base points off the strip avoid the divisor. -/
theorem XiC_ne_zero_of_im_sq_ge {z : ℂ} (hy : 27 / 100 ≤ z.im ^ 2) :
    XiC z ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
  have hvlt : |(xiSpectralPoint q).im| < 1 / 2 :=
    abs_im_xiSpectralPoint_lt_half q
  rw [hq] at hvlt
  have h2 := abs_lt.mp hvlt
  nlinarith [h2.1, h2.2, hy]

/-- **The Weil form is unconditionally positive off the strip.**  For every base
point with `(Im z)² ≥ 27/100` the diagonal Weil value is nonnegative — the sign
of the Weil quadratic form is decided, with no hypothesis on the zeros, outside
the thin strip `|Im z| < 0.52` in which the divisor is confined. -/
theorem weilDiagonal_re_nonneg_of_im_sq_ge {z : ℂ}
    (hy : 27 / 100 ≤ z.im ^ 2) (hz0 : z ≠ 0) :
    0 ≤ (xiWeilPolarization (xiCauchyRegularizedKernel z)
      (xiCauchyRegularizedKernel z)).re := by
  have hz : XiC z ≠ 0 := XiC_ne_zero_of_im_sq_ge hy
  have hzcim : 27 / 100 ≤ ((starRingEnd ℂ) z).im ^ 2 := by
    simpa using hy
  have hzc : XiC ((starRingEnd ℂ) z) ≠ 0 := XiC_ne_zero_of_im_sq_ge hzcim
  have hzc0 : (starRingEnd ℂ) z ≠ 0 := by simpa using hz0
  have hne : z ≠ (starRingEnd ℂ) z := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    nlinarith [hy, this]
  rw [xiWeilPolarization_cauchyKernel, xiWeilGramEntry_eq hz hzc hz0 hzc0 hne]
  rw [← xiWeilGramEntry_eq hz hzc hz0 hzc0 hne, xiWeilGramEntry]
  have hsummand : Summable (fun q : XiZeroCopy =>
      xiCauchyRegularizedKernel z (xiSpectralPoint q) *
        xiCauchyRegularizedKernel ((starRingEnd ℂ) z) (xiSpectralPoint q)) := by
    have hsq := summable_xiSpectralPoint_inv_sq
    have hK := summable_xiRelativeResolventTerm hz
    have hK' := summable_xiRelativeResolventTerm hzc
    apply ((hsq.sub (hK.mul_left _)).add (hK'.mul_left _)).congr
    intro q
    have hne0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hnez : xiSpectralPoint q ≠ z := by
      intro hcon
      exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, hcon⟩)
    have hnez' : xiSpectralPoint q ≠ (starRingEnd ℂ) z := by
      intro hcon
      exact hzc ((XiC_eq_zero_iff_exists_xiZeroCopy _).mpr ⟨q, hcon⟩)
    rw [xiCauchyRegularizedKernel_mul hz0 hzc0 hne hne0 hnez hnez', ← sq,
      xiCauchyRegularizedKernel_apply_spectralPoint,
      xiCauchyRegularizedKernel_apply_spectralPoint]
  rw [Complex.re_tsum hsummand]
  exact tsum_nonneg fun q => weilGram_term_re_nonneg hy q

end

end RHTower
