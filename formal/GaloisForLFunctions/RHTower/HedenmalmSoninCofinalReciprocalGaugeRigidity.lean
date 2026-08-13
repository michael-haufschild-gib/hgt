import GaloisForLFunctions.RHTower.HedenmalmSoninFiniteDivisorAnalyticGaugeFlexibility
import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion

/-!
# Cofinal reciprocal Sonin-gauge rigidity

Functional-equation reflection makes the Weyl lower gain even on the full Xi divisor.  A scalar
determinant-one source gauge would instead be reciprocal under centered reflection.  These laws
are compatible with exact Sonin cancellation only at the critical wall: their reflected product
is `exp (-2 c |distance|)`.

This supplies a cofinal rigidity law requiring no growth estimate.  Existence of one entire
reciprocal scalar gauge with the exact positive-rate Sonin cancellation modulus on every Xi
support point is equivalent to RH.  The theorem does not assert that source geometry supplies
such a scalarization; it identifies that exact remaining producer.
-/

open Complex Real Set

noncomputable section

namespace RHTower

def burnolSoninWeylLowerGain (r : ℝ) (rho : XiDivisorSupport) : ℝ :=
  min ‖(burnolSoninMellinOrientationPair r (rho : ℂ)).1‖
    ‖(burnolSoninMellinOrientationPair r (rho : ℂ)).2‖

def burnolSoninWeylReciprocityDefect (r : ℝ)
    (rho : XiDivisorSupport) : ℝ :=
  burnolSoninWeylLowerGain r (xiZeroReflectEquiv rho) *
    burnolSoninWeylLowerGain r rho

theorem burnolSoninWeylLowerGain_eq
    {r : ℝ} (hr : 1 < r) (rho : XiDivisorSupport) :
    burnolSoninWeylLowerGain r rho =
      soninEscapeCancellingGaugeModulus (Real.log r)
        ((rho : ℂ).re - 1 / 2) := by
  exact burnolSoninMellinOrientationPair_lower_gain hr (rho : ℂ)

theorem burnolSoninWeylLowerGain_reflect
    {r : ℝ} (hr : 1 < r) (rho : XiDivisorSupport) :
    burnolSoninWeylLowerGain r (xiZeroReflectEquiv rho) =
      burnolSoninWeylLowerGain r rho := by
  rw [burnolSoninWeylLowerGain_eq hr, burnolSoninWeylLowerGain_eq hr]
  simp only [soninEscapeCancellingGaugeModulus, xiZeroReflectEquiv_apply,
    Complex.sub_re, Complex.one_re]
  congr 2
  rw [show 1 - (rho : ℂ).re - 1 / 2 =
    -((rho : ℂ).re - 1 / 2) by ring, abs_neg]

theorem burnolSoninWeylReciprocityDefect_eq
    {r : ℝ} (hr : 1 < r) (rho : XiDivisorSupport) :
    burnolSoninWeylReciprocityDefect r rho =
      Real.exp (-2 * Real.log r * |(rho : ℂ).re - 1 / 2|) := by
  rw [burnolSoninWeylReciprocityDefect,
    burnolSoninWeylLowerGain_reflect hr,
    burnolSoninWeylLowerGain_eq hr,
    soninEscapeCancellingGaugeModulus, ← Real.exp_add]
  congr 1
  ring

theorem burnolSoninWeylReciprocityDefect_eq_one_iff
    {r : ℝ} (hr : 1 < r) (rho : XiDivisorSupport) :
    burnolSoninWeylReciprocityDefect r rho = 1 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [burnolSoninWeylReciprocityDefect_eq hr,
    Real.exp_eq_one_iff]
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  constructor
  · intro h
    have habs : |(rho : ℂ).re - 1 / 2| = 0 := by
      rcases mul_eq_zero.mp h with hcoeff | habs
      · have : Real.log r = 0 := by nlinarith
        exact (hlog this).elim
      · exact habs
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    rw [h, sub_self, abs_zero, mul_zero]

theorem burnolSoninWeylReciprocityDefect_lt_one_iff
    {r : ℝ} (hr : 1 < r) (rho : XiDivisorSupport) :
    burnolSoninWeylReciprocityDefect r rho < 1 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [burnolSoninWeylReciprocityDefect_eq hr, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log r := Real.log_pos hr
  constructor
  · intro h hline
    rw [hline, sub_self, abs_zero, mul_zero] at h
    exact lt_irrefl 0 h
  · intro hline
    have habs : 0 < |(rho : ℂ).re - 1 / 2| :=
      abs_pos.mpr (sub_ne_zero.mpr hline)
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) hlog) habs

theorem all_burnolSoninWeylReciprocityDefect_eq_one_iff_rh
    {r : ℝ} (hr : 1 < r) :
    (∀ rho : XiDivisorSupport,
      burnolSoninWeylReciprocityDefect r rho = 1) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
    intro rho
    have hline := (burnolSoninWeylReciprocityDefect_eq_one_iff hr rho).1 (h rho)
    rw [xiSpectralPointSupport_im, hline]
    norm_num
  · intro hRH rho
    apply (burnolSoninWeylReciprocityDefect_eq_one_iff hr rho).2
    have hreal := xiSpectralPointSupport_eq_ofReal_of_rh hRH rho
    have him := congrArg Complex.im hreal
    rw [Complex.ofReal_im, xiSpectralPointSupport_im] at him
    linarith

def XiCofinalReciprocalSoninGauge (c : ℝ) : Prop :=
  ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g Set.univ ∧
    (∀ z : ℂ, g (-z) * g z = 1) ∧
    ∀ rho : XiDivisorSupport,
      ‖g (xiSpectralPointSupport rho)‖ =
        soninEscapeCancellingGaugeModulus c
          (xiSpectralPointSupport rho).im

theorem xiSpectralPointSupport_im_eq_zero_of_reciprocal_sonin_cancellation
    {c : ℝ} (hc : 0 < c) {g : ℂ → ℂ}
    (hrec : ∀ z : ℂ, g (-z) * g z = 1)
    (hmod : ∀ rho : XiDivisorSupport,
      ‖g (xiSpectralPointSupport rho)‖ =
        soninEscapeCancellingGaugeModulus c
          (xiSpectralPointSupport rho).im)
    (rho : XiDivisorSupport) :
    (xiSpectralPointSupport rho).im = 0 := by
  have hnorm := congrArg norm (hrec (xiSpectralPointSupport rho))
  rw [norm_mul, norm_one, ← xiSpectralPointSupport_reflect rho,
    hmod (xiZeroReflectEquiv rho), hmod rho,
    soninEscapeCancellingGaugeModulus,
    soninEscapeCancellingGaugeModulus,
    xiSpectralPointSupport_reflect, Complex.neg_im, abs_neg] at hnorm
  have hexp :
      Real.exp
          (-c * |(xiSpectralPointSupport rho).im| +
            -c * |(xiSpectralPointSupport rho).im|) =
        Real.exp 0 := by
    rw [Real.exp_add]
    simpa using hnorm
  have harg := Real.exp_injective hexp
  have habs : |(xiSpectralPointSupport rho).im| = 0 := by
    nlinarith [abs_nonneg (xiSpectralPointSupport rho).im]
  exact abs_eq_zero.mp habs

theorem xiCofinalReciprocalSoninGauge_iff_rh
    {c : ℝ} (hc : 0 < c) :
    XiCofinalReciprocalSoninGauge c ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨g, _, hrec, hmod⟩
    exact riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
      (xiSpectralPointSupport_im_eq_zero_of_reciprocal_sonin_cancellation
        hc hrec hmod)
  · intro hRH
    refine ⟨fun _ => 1, analyticOnNhd_const, by simp, ?_⟩
    intro rho
    have hreal := xiSpectralPointSupport_eq_ofReal_of_rh hRH rho
    have him := congrArg Complex.im hreal
    rw [Complex.ofReal_im] at him
    simp [him, soninEscapeCancellingGaugeModulus]

end RHTower
