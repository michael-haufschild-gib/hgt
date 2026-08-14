import GaloisForLFunctions.RHTower.CCMCompletedPrimeGammaAccretivityCriterion
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.XiHeatShellMinimum
import GaloisForLFunctions.HTGeometry.HerglotzRepresentationDisc
import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# The Xi Carathéodory germ on the unit disc

The centered Xi source trace is `H_Ξ = -Ξ'/Ξ` in the coordinate `s = 1/2 + z i`.  The Cayley map
`χ(w) = i(1+w)/(1-w)` carries the unit disc onto the upper half plane, so `-i H_Ξ(χ(w))/b` is the
disc germ whose real part is the normalized imaginary part of the source trace.

Two facts are proved here.  The already checked anti-Herglotz gate for the Riemann hypothesis is
*exactly* the statement that `H_Ξ` has nonnegative imaginary part on the centered upper half strip.
And under the Riemann hypothesis `H_Ξ` is in fact Herglotz on the whole upper half plane, because
its centered relative-resolvent expansion then has only real spectral points.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The centered Xi source trace `H_Ξ = -Ξ'/Ξ`. -/
def xiSourceHerglotz (z : ℂ) : ℂ := -logDeriv XiC z

/-- The Cayley map from the unit disc onto the upper half plane. -/
def cayleyDisc (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

@[simp]
theorem cayleyDisc_zero : cayleyDisc 0 = Complex.I := by
  simp [cayleyDisc]

theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hw
  exact absurd hw (lt_irrefl 1)

/-- The Cayley image of the unit disc has imaginary part `(1 - |w|²)/|1 - w|²`. -/
theorem cayleyDisc_im (w : ℂ) :
    (cayleyDisc w).im = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  have hmulI : (cayleyDisc w).im = ((1 + w) / (1 - w)).re := by
    rw [cayleyDisc, mul_div_assoc, Complex.mul_im]
    simp
  rw [hmulI, Complex.div_re, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

/-- The Cayley map sends the unit disc into the open upper half plane. -/
theorem cayleyDisc_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyDisc w).im := by
  rw [cayleyDisc_im w]
  have hne : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  have hnum : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hden : 0 < ‖1 - w‖ ^ 2 := by
    have := norm_pos_iff.mpr hne
    positivity
  exact div_pos hnum hden

/-- The centered abscissa in the upper half strip is a nonzero point of the critical strip. -/
theorem centeredAbscissa_ne_zero {z : ℂ} (hzHalf : z.im < 1 / 2) :
    (1 : ℂ) / 2 + z * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.mul_re] at hre
  linarith

/-- Away from the zeta zeros the centered Xi value is nonzero on the upper half strip. -/
theorem XiC_ne_zero_of_strip {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) : XiC z ≠ 0 := by
  have hspos : 0 < ((1 : ℂ) / 2 + z * Complex.I).re := centeredAbscissa_re_pos hzhalf
  have hs0 : (1 : ℂ) / 2 + z * Complex.I ≠ 0 := centeredAbscissa_ne_zero hzhalf
  have hs1 : (1 : ℂ) / 2 + z * Complex.I ≠ 1 := centeredAbscissa_ne_one hzpos
  have hG := Gammaℝ_ne_zero_of_re_pos hspos
  change xi ((1 : ℂ) / 2 + z * Complex.I) ≠ 0
  rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG]
  exact mul_ne_zero (archFactor_ne_zero hs0 hs1 hG) hzeta

/-- The source trace is the negative of the continued prime--archimedean relative trace. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_neg_xiSourceHerglotz
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace z = -xiSourceHerglotz z := by
  have hspos : 0 < ((1 : ℂ) / 2 + z * Complex.I).re := centeredAbscissa_re_pos hzhalf
  have hs1 : (1 : ℂ) / 2 + z * Complex.I ≠ 1 := centeredAbscissa_ne_one hzpos
  have hXi : XiC z ≠ 0 := XiC_ne_zero_of_strip hzpos hzhalf hzeta
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace hspos hs1 hzeta,
    ← logDeriv_XiC_eq_relativeResolventTrace hXi, xiSourceHerglotz, neg_neg]

/-- **The anti-Herglotz gate is the Herglotz sign of the Xi source trace on the strip.** -/
theorem continuedPrimeArchUpperAntiHerglotz_iff_xiSourceHerglotz_im_nonneg :
    ContinuedPrimeArchUpperAntiHerglotz ↔
      ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
        riemannZeta (1 / 2 + z * Complex.I) ≠ 0 → 0 ≤ (xiSourceHerglotz z).im := by
  constructor
  · intro h z hzpos hzhalf hzeta
    have hz := h z hzpos hzhalf hzeta
    rw [continuedPrimeArchSourceRelativeTrace_eq_neg_xiSourceHerglotz hzpos hzhalf hzeta,
      Complex.neg_im] at hz
    linarith
  · intro h z hzpos hzhalf hzeta
    have hz := h z hzpos hzhalf hzeta
    rw [continuedPrimeArchSourceRelativeTrace_eq_neg_xiSourceHerglotz hzpos hzhalf hzeta,
      Complex.neg_im]
    linarith

/-- **RH is exactly the Herglotz sign of the Xi source trace on the centered upper half strip.** -/
theorem riemannHypothesis_iff_xiSourceHerglotz_im_nonneg_strip :
    RiemannHypothesis ↔
      ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
        riemannZeta (1 / 2 + z * Complex.I) ≠ 0 → 0 ≤ (xiSourceHerglotz z).im := by
  rw [← continuedPrimeArchUpperAntiHerglotz_iff_xiSourceHerglotz_im_nonneg]
  exact continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.symm

/-- Each centered relative-resolvent term with a real spectral point has nonpositive imaginary
part in the upper half plane. -/
theorem xiRelativeResolventTerm_im_nonpos {z : ℂ} (hz : 0 < z.im) {q : XiZeroCopy} {t : ℝ}
    (ht : xiSpectralPoint q = (t : ℂ)) :
    (xiRelativeResolventTerm z q).im ≤ 0 := by
  have hN : (0 : ℝ) ≤ Complex.normSq ((t : ℂ) - z) := Complex.normSq_nonneg _
  have hquot : (0 : ℝ) ≤ z.im / Complex.normSq ((t : ℂ) - z) := div_nonneg hz.le hN
  rw [xiRelativeResolventTerm, ht, Complex.sub_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg, neg_zero, zero_div]
  linarith

/-- **Under the Riemann hypothesis the Xi source trace is Herglotz on the whole upper half
plane.**  Every centered spectral point is then real, so every relative-resolvent term has
nonpositive imaginary part above the axis. -/
theorem xiSourceHerglotz_im_nonneg_of_rh (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (xiSourceHerglotz z).im := by
  have hXi : XiC z ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht] at hq
    rw [← hq] at hz
    simp at hz
  have hsum : Summable (xiRelativeResolventTerm z) := summable_xiRelativeResolventTerm hXi
  have himsum : (xiRelativeResolventTrace z).im
      = ∑' q : XiZeroCopy, (xiRelativeResolventTerm z q).im := by
    rw [xiRelativeResolventTrace]
    exact Complex.imCLM.map_tsum hsum
  have hnonpos : (xiRelativeResolventTrace z).im ≤ 0 := by
    rw [himsum]
    refine tsum_nonpos fun q => ?_
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    exact xiRelativeResolventTerm_im_nonpos hz ht
  have heq : xiSourceHerglotz z = -xiRelativeResolventTrace z := by
    rw [xiSourceHerglotz, logDeriv_XiC_eq_relativeResolventTrace hXi]
  rw [heq, Complex.neg_im]
  linarith

/-- The logarithmic derivative of `xi` is real on the real axis. -/
theorem logDeriv_xi_ofReal_im (sigma : ℝ) : (logDeriv xi ((sigma : ℝ) : ℂ)).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [logDeriv_apply, map_div₀, ← xi_deriv_conj, ← xi_conj, Complex.conj_ofReal]

/-- The centered logarithmic derivative at the basepoint is purely imaginary. -/
theorem logDeriv_XiC_I_re : (logDeriv XiC Complex.I).re = 0 := by
  have hval : (logDeriv xi ((1 : ℂ) / 2 + Complex.I * Complex.I)).im = 0 := by
    have hs : (1 : ℂ) / 2 + Complex.I * Complex.I = (((-1 / 2 : ℝ)) : ℂ) := by
      rw [Complex.I_mul_I]
      norm_num
    rw [hs]
    simpa using logDeriv_xi_ofReal_im (-1 / 2)
  rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, Complex.mul_re, Complex.I_re, Complex.I_im, hval]
  ring

/-- The basepoint normalization `b = -i H_Ξ(i) = ξ'(3/2)/ξ(3/2)`. -/
def xiBasepointSlope : ℂ := -Complex.I * xiSourceHerglotz Complex.I

/-- The Xi Carathéodory germ on the unit disc. -/
def xiCaratheodory (w : ℂ) : ℂ :=
  -Complex.I * xiSourceHerglotz (cayleyDisc w) / xiBasepointSlope

theorem xiBasepointSlope_re : xiBasepointSlope.re = (xiSourceHerglotz Complex.I).im := by
  rw [xiBasepointSlope]
  simp [Complex.mul_re]

/-- **The basepoint normalization is real.** -/
theorem xiBasepointSlope_im : xiBasepointSlope.im = 0 := by
  have h : xiBasepointSlope.im = -(xiSourceHerglotz Complex.I).re := by
    rw [xiBasepointSlope]
    simp [Complex.mul_im]
  rw [h, xiSourceHerglotz, Complex.neg_re, logDeriv_XiC_I_re]
  ring

/-- **The basepoint normalization is strictly positive under the Riemann hypothesis.**  Its value
is the convergent positive sum `∑ 1/(t² + 1)` over the centered Xi spectrum. -/
theorem xiBasepointSlope_re_pos_of_rh (hRH : RiemannHypothesis) :
    0 < xiBasepointSlope.re := by
  have hz : (0 : ℝ) < (Complex.I).im := by simp
  have hXi : XiC Complex.I ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy Complex.I).mp h
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht] at hq
    have := congrArg Complex.im hq
    simp at this
  have hsum : Summable (xiRelativeResolventTerm Complex.I) :=
    summable_xiRelativeResolventTerm hXi
  have hsumim : Summable fun q : XiZeroCopy => -(xiRelativeResolventTerm Complex.I q).im :=
    ((hsum.map Complex.imCLM Complex.imCLM.continuous)).neg
  have hnonneg : ∀ q : XiZeroCopy, 0 ≤ -(xiRelativeResolventTerm Complex.I q).im := by
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have := xiRelativeResolventTerm_im_nonpos hz ht
    linarith
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  obtain ⟨t0, ht0⟩ := xiSpectralPoint_real_of_rh hRH q0
  have hpos : 0 < -(xiRelativeResolventTerm Complex.I q0).im := by
    have hden : Complex.normSq ((t0 : ℂ) - Complex.I) = t0 ^ 2 + 1 := by
      rw [Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im]
      ring
    have hdenpos : (0 : ℝ) < t0 ^ 2 + 1 := by positivity
    rw [xiRelativeResolventTerm, ht0, Complex.sub_im, Complex.inv_im, Complex.inv_im]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, neg_neg,
      neg_zero, zero_div]
    rw [hden]
    have : (0 : ℝ) < 1 / (t0 ^ 2 + 1) := by positivity
    linarith
  have hle : -(xiRelativeResolventTerm Complex.I q0).im
      ≤ ∑' q : XiZeroCopy, -(xiRelativeResolventTerm Complex.I q).im :=
    hsumim.le_tsum q0 fun j _ => hnonneg j
  have heq : xiSourceHerglotz Complex.I = -xiRelativeResolventTrace Complex.I := by
    rw [xiSourceHerglotz, logDeriv_XiC_eq_relativeResolventTrace hXi]
  have himsum : (xiRelativeResolventTrace Complex.I).im
      = ∑' q : XiZeroCopy, (xiRelativeResolventTerm Complex.I q).im := by
    rw [xiRelativeResolventTrace]
    exact Complex.imCLM.map_tsum hsum
  have hneg : ∑' q : XiZeroCopy, -(xiRelativeResolventTerm Complex.I q).im
      = -(xiRelativeResolventTrace Complex.I).im := by
    rw [himsum, ← tsum_neg]
  rw [xiBasepointSlope_re, heq, Complex.neg_im, ← hneg]
  linarith

theorem xiCaratheodory_zero_of_rh (hRH : RiemannHypothesis) : xiCaratheodory 0 = 1 := by
  have hb : xiBasepointSlope ≠ 0 := by
    intro h
    have := xiBasepointSlope_re_pos_of_rh hRH
    rw [h] at this
    simp at this
  rw [xiCaratheodory, cayleyDisc_zero, ← xiBasepointSlope, div_self hb]

/-- **The disc germ has nonnegative real part under the Riemann hypothesis.**  This is the
Carathéodory property of `F_Ξ`. -/
theorem xiCaratheodory_re_nonneg_of_rh (hRH : RiemannHypothesis) {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (xiCaratheodory w).re := by
  have hbre : 0 < xiBasepointSlope.re := xiBasepointSlope_re_pos_of_rh hRH
  have hbim : xiBasepointSlope.im = 0 := xiBasepointSlope_im
  have hnum : 0 ≤ (-Complex.I * xiSourceHerglotz (cayleyDisc w)).re := by
    have := xiSourceHerglotz_im_nonneg_of_rh hRH (cayleyDisc_im_pos hw)
    simpa [Complex.mul_re] using this
  rw [xiCaratheodory, Complex.div_re, hbim]
  have hns : Complex.normSq xiBasepointSlope = xiBasepointSlope.re ^ 2 := by
    rw [Complex.normSq_apply, hbim]
    ring
  rw [hns]
  have hpos : 0 < xiBasepointSlope.re ^ 2 := by positivity
  have h1 : 0 ≤ (-Complex.I * xiSourceHerglotz (cayleyDisc w)).re * xiBasepointSlope.re
      / xiBasepointSlope.re ^ 2 :=
    div_nonneg (mul_nonneg hnum hbre.le) hpos.le
  simpa using h1

/-- Under the Riemann hypothesis the centered Xi function has no zero above the real axis. -/
theorem XiC_ne_zero_of_rh_of_im_pos (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) :
    XiC z ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [ht] at hq
  rw [← hq] at hz
  simp at hz

/-- The Cayley map is differentiable on the open unit disc. -/
theorem differentiableAt_cayleyDisc {w : ℂ} (hw : ‖w‖ < 1) :
    DifferentiableAt ℂ cayleyDisc w := by
  have hne : (1 : ℂ) - w ≠ 0 := one_sub_ne_zero_of_norm_lt_one hw
  unfold cayleyDisc
  exact ((differentiableAt_const Complex.I).mul
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)).div
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) hne

/-- Under the Riemann hypothesis the Xi disc germ is holomorphic on the open unit disc. -/
theorem differentiableOn_xiCaratheodory_of_rh (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ xiCaratheodory (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hcay : DifferentiableAt ℂ cayleyDisc w := differentiableAt_cayleyDisc hw
  have hXi : XiC (cayleyDisc w) ≠ 0 :=
    XiC_ne_zero_of_rh_of_im_pos hRH (cayleyDisc_im_pos hw)
  have hlog : DifferentiableAt ℂ (fun z => logDeriv XiC z) (cayleyDisc w) := by
    simp only [logDeriv_apply]
    exact (XiC_differentiable.deriv.differentiableAt).div
      XiC_differentiable.differentiableAt hXi
  have hsrc : DifferentiableAt ℂ xiSourceHerglotz (cayleyDisc w) := by
    unfold xiSourceHerglotz
    exact hlog.neg
  exact (((hsrc.comp w hcay).const_mul (-Complex.I)).div_const
    xiBasepointSlope).differentiableWithinAt

/-- **The canonical Xi circle probability measure.**  Under the Riemann hypothesis the Xi disc germ
is a normalized Carathéodory function, so the Herglotz representation supplies a probability measure
on the circle whose Poisson integral is the real part of the germ. -/
theorem exists_xiCircleMeasure_of_rh (hRH : RiemannHypothesis) :
    ∃ mu : MeasureTheory.ProbabilityMeasure Circle,
      ∀ w ∈ Metric.ball (0 : ℂ) 1,
        (xiCaratheodory w).re
          = ∫ zeta : Circle, poissonKernel 0 w (zeta : ℂ) ∂(mu : MeasureTheory.Measure Circle) := by
  refine GaloisForLFunctions.HTGeometry.exists_herglotz_representation
    (differentiableOn_xiCaratheodory_of_rh hRH) (fun z hz => ?_)
    (xiCaratheodory_zero_of_rh hRH)
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact xiCaratheodory_re_nonneg_of_rh hRH hz

/-- Under the Riemann hypothesis each basepoint resolvent term contributes the Cauchy weight
`1/(t² + 1)`. -/
theorem neg_xiRelativeResolventTerm_I_im_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    -(xiRelativeResolventTerm Complex.I q).im = 1 / (xiRealSpectralPoint q ^ 2 + 1) := by
  have ht := xiSpectralPoint_eq_ofReal_of_rh hRH q
  set t := xiRealSpectralPoint q with htdef
  have hden : Complex.normSq ((t : ℂ) - Complex.I) = t ^ 2 + 1 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  rw [xiRelativeResolventTerm, ht, Complex.sub_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, neg_neg,
    neg_zero, zero_div]
  rw [hden]

/-- **The basepoint normalization is the total Cauchy weight of the centered Xi spectrum.** -/
theorem xiBasepointSlope_re_eq_tsum_of_rh (hRH : RiemannHypothesis) :
    xiBasepointSlope.re = ∑' q : XiZeroCopy, 1 / (xiRealSpectralPoint q ^ 2 + 1) := by
  have hz : (0 : ℝ) < (Complex.I).im := by simp
  have hXi : XiC Complex.I ≠ 0 := XiC_ne_zero_of_rh_of_im_pos hRH hz
  have hsum : Summable (xiRelativeResolventTerm Complex.I) :=
    summable_xiRelativeResolventTerm hXi
  have heq : xiSourceHerglotz Complex.I = -xiRelativeResolventTrace Complex.I := by
    rw [xiSourceHerglotz, logDeriv_XiC_eq_relativeResolventTrace hXi]
  have himsum : (xiRelativeResolventTrace Complex.I).im
      = ∑' q : XiZeroCopy, (xiRelativeResolventTerm Complex.I q).im := by
    rw [xiRelativeResolventTrace]
    exact Complex.imCLM.map_tsum hsum
  have hneg : ∑' q : XiZeroCopy, -(xiRelativeResolventTerm Complex.I q).im
      = -(xiRelativeResolventTrace Complex.I).im := by
    rw [himsum, ← tsum_neg]
  rw [xiBasepointSlope_re, heq, Complex.neg_im, ← hneg]
  exact tsum_congr fun q => neg_xiRelativeResolventTerm_I_im_of_rh hRH q

/-- The Cauchy weights of the centered Xi spectrum are summable. -/
theorem summable_xiCauchyWeight_of_rh (hRH : RiemannHypothesis) :
    Summable fun q : XiZeroCopy => 1 / (xiRealSpectralPoint q ^ 2 + 1) := by
  have hz : (0 : ℝ) < (Complex.I).im := by simp
  have hXi : XiC Complex.I ≠ 0 := XiC_ne_zero_of_rh_of_im_pos hRH hz
  have hsum : Summable (xiRelativeResolventTerm Complex.I) :=
    summable_xiRelativeResolventTerm hXi
  have hsumim : Summable fun q : XiZeroCopy => -(xiRelativeResolventTerm Complex.I q).im :=
    ((hsum.map Complex.imCLM Complex.imCLM.continuous)).neg
  exact hsumim.congr fun q => neg_xiRelativeResolventTerm_I_im_of_rh hRH q

end

end RHTower
