import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerFourLegHodgeCompletion

/-!
# Route P primitive Burnol / Deninger four-leg collapse rigidity

P-G202 constructs the positive four-leg Hodge completion of an upper squared-Cauchy graph vector.
This file determines whether that positive completion can be collapsed back onto the original
holomorphic upper graph.

The coordinate defect factors into the critical-line displacement, a resonance factor, and a
nonvanishing Cauchy denominator.  The resonance is impossible for every upper Deninger pole because
its imaginary part lies strictly above `1 / 2`, whereas a spectral point plus its conjugate is real.
Thus, at any fixed nonzero amplitude and any upper pole, one coordinate collapses exactly when the
corresponding Xi spectral point is real.  Equality of the two graph vectors is therefore equivalent
to the Riemann hypothesis.

This is a sharp no-go theorem: replacing P-G202's fourth leg by the original upper leg is not an
unconditional positivity transport; it already contains all of RH.  Any surviving construction
must preserve the nonholomorphic four-leg distinction until an independently coercive source
operation controls it.

No zero-location, positivity, simplicity, or RH hypothesis is used in the equivalence proof.
-/

open Complex

namespace RHTower

noncomputable section

/-- Coordinate defect incurred by collapsing the conjugate-lower fourth leg back onto the original
upper squared-Cauchy graph leg. -/
def routePDeningerFourLegCollapseDefect
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) : ℂ :=
  routePDeningerUpperFourLegHodgeMate A w q -
    routePDeningerUpperSquaredCauchyJet A w q

theorem routePDeningerUpperCollapseResonanceFactor_ne_zero
    (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    xiSpectralPoint q + (starRingEnd ℂ) (xiSpectralPoint q) - 2 * (w : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hw := deningerPrimeGammaUpperPoint_im_gt w
  norm_num [Complex.sub_im, Complex.add_im, conj_im, Complex.mul_im] at him
  linarith

/-- Exact factorization of the four-leg collapse defect. The two numerator factors are the
critical-line displacement and an impossible upper-pole resonance. -/
theorem routePDeningerFourLegCollapseDefect_factorization
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    routePDeningerFourLegCollapseDefect A w q =
      A *
        ((xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q)) *
          (xiSpectralPoint q + (starRingEnd ℂ) (xiSpectralPoint q) -
            2 * (w : ℂ))) *
        (((starRingEnd ℂ) (xiSpectralPoint q) - (w : ℂ)) ^ 2 *
          (xiSpectralPoint q - (w : ℂ)) ^ 2)⁻¹ := by
  have hq := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w
  have hL := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint
    (xiZeroCopyLineConjEquiv q) w
  have hconj : (starRingEnd ℂ) (xiSpectralPoint q) ≠ (w : ℂ) := by
    simpa [xiSpectralPoint_lineConj] using hL
  rw [routePDeningerFourLegCollapseDefect,
    routePDeningerUpperFourLegHodgeMate_eq_lineConj]
  change
    A * xiWeilCauchyTest (w : ℂ)
          (xiSpectralPoint (xiZeroCopyLineConjEquiv q)) ^ 2 -
        A * xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q) ^ 2 = _
  rw [xiSpectralPoint_lineConj]
  unfold xiWeilCauchyTest
  field_simp [sub_ne_zero.mpr hq, sub_ne_zero.mpr hconj]
  ring

/-- At a nonzero amplitude, one collapse coordinate vanishes exactly when that Xi spectral point
is fixed by critical-line conjugation. -/
theorem routePDeningerFourLegCollapseDefect_eq_zero_iff
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    routePDeningerFourLegCollapseDefect A w q = 0 ↔
      xiSpectralPoint q = (starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [routePDeningerFourLegCollapseDefect_factorization]
  have hres := routePDeningerUpperCollapseResonanceFactor_ne_zero w q
  have hq := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w
  have hL := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint
    (xiZeroCopyLineConjEquiv q) w
  have hconj : (starRingEnd ℂ) (xiSpectralPoint q) ≠ (w : ℂ) := by
    simpa [xiSpectralPoint_lineConj] using hL
  have hden :
      ((starRingEnd ℂ) (xiSpectralPoint q) - (w : ℂ)) ^ 2 *
          (xiSpectralPoint q - (w : ℂ)) ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr hconj))
      (pow_ne_zero 2 (sub_ne_zero.mpr hq))
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hleft | hinv
    · rcases mul_eq_zero.mp hleft with hA0 | hnum
      · exact absurd hA0 hA
      · rcases mul_eq_zero.mp hnum with hline | hres0
        · exact sub_eq_zero.mp hline
        · exact absurd hres0 hres
    · exact absurd hinv (inv_ne_zero hden)
  · intro hline
    have hdiff :
        xiSpectralPoint q - (starRingEnd ℂ) (xiSpectralPoint q) = 0 :=
      sub_eq_zero.mpr hline
    rw [hdiff, zero_mul, mul_zero, zero_mul]

theorem routePDeningerFourLegCollapseDefect_eq_zero_iff_im
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    routePDeningerFourLegCollapseDefect A w q = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [routePDeningerFourLegCollapseDefect_eq_zero_iff hA]
  constructor
  · intro h
    exact Complex.conj_eq_iff_im.mp h.symm
  · intro h
    exact (Complex.conj_eq_iff_im.mpr h).symm

/-- Collapsing the positive fourth leg onto the original upper graph, even for one fixed nonzero
upper squared-Cauchy amplitude, is exactly RH. -/
theorem routePDeningerUpperFourLegHodgeMate_eq_upperSquaredCauchyJet_iff_riemannHypothesis
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    routePDeningerUpperFourLegHodgeMate A w =
        routePDeningerUpperSquaredCauchyJet A w ↔
      RiemannHypothesis := by
  constructor
  · intro hcollapse
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hq : routePDeningerFourLegCollapseDefect A w q = 0 := by
      rw [routePDeningerFourLegCollapseDefect, hcollapse, sub_self]
    have him :=
      (routePDeningerFourLegCollapseDefect_eq_zero_iff_im hA w q).mp hq
    exact ⟨(xiSpectralPoint q).re,
      Complex.ext (by simp) (by simpa using him)⟩
  · intro hRH
    apply Subtype.ext
    funext (q : XiZeroCopy)
    have him : (xiSpectralPoint q).im = 0 := by
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [ht]
      simp
    have hzero :=
      (routePDeningerFourLegCollapseDefect_eq_zero_iff_im hA w q).mpr him
    exact sub_eq_zero.mp hzero

end

end RHTower
