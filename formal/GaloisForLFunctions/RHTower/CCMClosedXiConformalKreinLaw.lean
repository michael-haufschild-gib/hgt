import GaloisForLFunctions.RHTower.CCMClosedXiHaarMellinRealization

/-!
# Weight-one conformal law and sharp Krein positivity sectors

Critical-line reflection and Haar--Mellin covariance force simultaneous literal CCM Lefschetz
translation to scale the multiplicity-exact Weil pairing by the positive scalar `|c|⁻¹`.
Consequently class-space flow preserves Krein sign.  Independently, the reflection-even channel
is unconditionally positive and the reflection-odd channel unconditionally negative.  These
statements use no zero-location or Weil-positivity premise.
-/

noncomputable section

open CategoryTheory Complex

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule

/-- Support-level formula for critical-line reflection on a multiplicity copy. -/
theorem xiZeroCopyLineConj_support (q : _root_.RHTower.XiZeroCopy) :
    (((_root_.RHTower.xiZeroCopyLineConjEquiv q).1 :
        _root_.RHTower.XiDivisorSupport) : ℂ) =
      1 - (starRingEnd ℂ) (q.1 : ℂ) := by
  change
    ((_root_.RHTower.xiZeroReflectEquiv
      (_root_.RHTower.xiZeroConjEquiv q.1) :
        _root_.RHTower.XiDivisorSupport) : ℂ) = _
  rw [_root_.RHTower.xiZeroReflectEquiv_apply]
  rfl

/-- Universal weight-one character identity.  A Mellin character and the conjugate of its
critical-line-reflected character multiply to `exp (-log |c|)`, independently of the zero. -/
theorem ccmClosedXiLefschetzMultiplier_mul_conj_lineConj
    (c : Section) (q : _root_.RHTower.XiZeroCopy) :
    ccmClosedXiLefschetzMultiplier c q.1 *
        (starRingEnd ℂ)
          (ccmClosedXiLefschetzMultiplier c
            (_root_.RHTower.xiZeroCopyLineConjEquiv q).1) =
      Complex.exp (-(ccmRationalPositiveUnitLog c.2) : ℂ) := by
  rw [ccmClosedXiLefschetzMultiplier,
    ccmClosedXiLefschetzMultiplier,
    ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal,
    xiZeroCopyLineConj_support]
  rw [← Complex.exp_add]
  congr 1
  simp only [map_sub, map_one, Complex.conj_conj]
  ring

/-- **Weight-one conformal law.**  Simultaneous Lefschetz translation on both entries scales the
literal closed-CCM Weil pairing by the zero-independent factor `exp (-log |c|)`. -/
theorem ccmClosedXiWeilPairing_lefschetz_conformal
    (c : Section) (x y : Relative.simplicial.degree 0) :
    ccmClosedXiWeilPairing
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x)
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) y) =
      Complex.exp (-(ccmRationalPositiveUnitLog c.2) : ℂ) *
        ccmClosedXiWeilPairing x y := by
  unfold ccmClosedXiWeilPairing
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [ccmClosedXiSpectralEvaluation_lefschetz,
    ccmClosedXiSpectralEvaluation_lefschetz,
    map_mul]
  calc
    _ = (ccmClosedXiLefschetzMultiplier c q.1 *
          (starRingEnd ℂ)
            (ccmClosedXiLefschetzMultiplier c
              (_root_.RHTower.xiZeroCopyLineConjEquiv q).1)) *
        (ccmClosedXiSpectralEvaluation x q *
          (starRingEnd ℂ)
            (ccmClosedXiSpectralEvaluation y
              (_root_.RHTower.xiZeroCopyLineConjEquiv q))) := by ring
    _ = _ := by rw [ccmClosedXiLefschetzMultiplier_mul_conj_lineConj]

/-- Real form of the conformal law: the scaling factor is the strictly positive real exponential. -/
theorem ccmClosedXiWeilPairing_lefschetz_conformal_re
    (c : Section) (x y : Relative.simplicial.degree 0) :
    (ccmClosedXiWeilPairing
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x)
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) y)).re =
      Real.exp (-ccmRationalPositiveUnitLog c.2) *
        (ccmClosedXiWeilPairing x y).re := by
  have hre :
      (Complex.exp (-(ccmRationalPositiveUnitLog c.2) : ℂ)).re =
        Real.exp (-ccmRationalPositiveUnitLog c.2) := by
    simpa only [Complex.ofReal_neg] using
      Complex.exp_ofReal_re (-ccmRationalPositiveUnitLog c.2)
  have him :
      (Complex.exp (-(ccmRationalPositiveUnitLog c.2) : ℂ)).im = 0 := by
    simpa only [Complex.ofReal_neg] using
      Complex.exp_ofReal_im (-ccmRationalPositiveUnitLog c.2)
  rw [ccmClosedXiWeilPairing_lefschetz_conformal,
    Complex.mul_re, hre, him]
  ring

/-- Simultaneous Lefschetz flow preserves the sign of every diagonal closed-CCM Weil value. -/
theorem ccmClosedXiWeilPairing_lefschetz_nonneg_iff
    (c : Section) (x : Relative.simplicial.degree 0) :
    0 ≤ (ccmClosedXiWeilPairing
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x)
        ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk 0)) x)).re ↔
      0 ≤ (ccmClosedXiWeilPairing x x).re := by
  rw [ccmClosedXiWeilPairing_lefschetz_conformal_re]
  exact mul_nonneg_iff_of_pos_left (Real.exp_pos _)

end GaloisForLFunctions.RHTower

namespace CliffordWeil

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The reflection-even channel has Weil/Krein coefficient exactly its Hilbert norm square. -/
theorem quadratic_evenPart_eq_normSq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    quadratic J (a + J a) = ‖a + J a‖ ^ (2 : ℕ) := by
  have hfix : J (a + J a) = a + J a := by
    rw [map_add, hJ]
    abel
  rw [quadratic, hfix, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Non-circular scalar positivity on the full reflection-even channel. -/
theorem quadratic_evenPart_nonneg
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    0 ≤ quadratic J (a + J a) := by
  rw [quadratic_evenPart_eq_normSq J hJ]
  positivity

/-- The reflection-odd channel has coefficient exactly the negative of its Hilbert norm square. -/
theorem quadratic_oddPart_eq_neg_normSq
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    quadratic J (a - J a) = -‖a - J a‖ ^ (2 : ℕ) := by
  have hanti : J (a - J a) = -(a - J a) := by
    rw [map_sub, hJ]
    abel
  rw [quadratic, hanti, inner_neg_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Sharpness: every reflection-odd vector is nonpositive. -/
theorem quadratic_oddPart_nonpos
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    quadratic J (a - J a) ≤ 0 := by
  rw [quadratic_oddPart_eq_neg_normSq J hJ]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Exact Krein energy balance: Weil coefficient is even energy minus odd energy. -/
theorem four_mul_quadratic_eq_even_sub_odd
    (J : H →ₗᵢ[ℂ] H) (hJ : Function.Involutive J) (a : H) :
    4 * quadratic J a = ‖a + J a‖ ^ (2 : ℕ) - ‖a - J a‖ ^ (2 : ℕ) := by
  have hplus := plus_channel_energy_eq J hJ a
  have hminus := minus_channel_energy_eq J hJ a
  nlinarith

end CliffordWeil

namespace RHTower

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Reflection-evenization of a Weil test function in centered spectral coordinates. -/
def xiWeilReflectionEvenTest (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z + F ((starRingEnd ℂ) z)

/-- Reflection-evenization preserves square summability on the actual Xi divisor. -/
theorem xiWeilReflectionEvenTest_squareSummable
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    XiWeilSquareSummable (xiWeilReflectionEvenTest F) := by
  let v : XiWeilCarrier := xiWeilEvaluationLp F hF
  have hsum := HilbertSchmidt.summable_coe_sq
    (v + xiWeilLineConjLinearIsometry v)
  apply hsum.congr
  intro q
  congr 2
  simp [v, xiWeilReflectionEvenTest, xiSpectralPoint_lineConj]

/-- The evaluation packet of an evenized test is exactly the reflection-even Hilbert channel. -/
theorem xiWeilEvaluationLp_reflectionEvenTest
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp (xiWeilReflectionEvenTest F)
        (xiWeilReflectionEvenTest_squareSummable F hF) =
      xiWeilEvaluationLp F hF +
        xiWeilLineConjLinearIsometry (xiWeilEvaluationLp F hF) := by
  apply Subtype.ext
  funext q
  simp [xiWeilReflectionEvenTest, xiSpectralPoint_lineConj]

/-- On the actual multiplicity-exact Xi carrier, the reflected pairing of an even packet is its
Hilbert norm square. -/
theorem xiWeilCliffordPairing_evenPart_eq_normSq (v : XiWeilCarrier) :
    xiWeilCliffordPairing
        (v + xiWeilLineConjLinearIsometry v)
        (v + xiWeilLineConjLinearIsometry v) =
      ((‖v + xiWeilLineConjLinearIsometry v‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold xiWeilCliffordPairing
  have hfix : xiWeilLineConjLinearIsometry
      (v + xiWeilLineConjLinearIsometry v) =
        v + xiWeilLineConjLinearIsometry v := by
    rw [map_add, xiWeilLineConjLinearIsometry_involutive]
    abel
  rw [hfix, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Genuine non-circular Weil positivity on the actual reflection-even Xi sector. -/
theorem xiWeilCliffordPairing_evenPart_re_nonneg (v : XiWeilCarrier) :
    0 ≤ (xiWeilCliffordPairing
        (v + xiWeilLineConjLinearIsometry v)
        (v + xiWeilLineConjLinearIsometry v)).re := by
  rw [xiWeilCliffordPairing_evenPart_eq_normSq]
  norm_cast
  positivity

/-- Sharp negative companion on the actual reflection-odd Xi sector. -/
theorem xiWeilCliffordPairing_oddPart_eq_neg_normSq (v : XiWeilCarrier) :
    xiWeilCliffordPairing
        (v - xiWeilLineConjLinearIsometry v)
        (v - xiWeilLineConjLinearIsometry v) =
      -((‖v - xiWeilLineConjLinearIsometry v‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold xiWeilCliffordPairing
  have hanti : xiWeilLineConjLinearIsometry
      (v - xiWeilLineConjLinearIsometry v) =
        -(v - xiWeilLineConjLinearIsometry v) := by
    rw [map_sub, xiWeilLineConjLinearIsometry_involutive]
    abel
  rw [hanti, inner_neg_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Exact non-circular positivity identity stated directly for the multiplicity-exact Weil form:
the Weil square of every reflection-evenized square-summable test is a Hilbert norm square. -/
theorem xiWeilPolarization_reflectionEvenTest_eq_normSq
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    xiWeilPolarization (xiWeilReflectionEvenTest F)
        (xiWeilReflectionEvenTest F) =
      ((‖xiWeilEvaluationLp F hF +
          xiWeilLineConjLinearIsometry (xiWeilEvaluationLp F hF)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  let hEven := xiWeilReflectionEvenTest_squareSummable F hF
  rw [← xiWeilCliffordPairing_evaluation_eq_polarization
      (xiWeilReflectionEvenTest F) (xiWeilReflectionEvenTest F) hEven hEven,
    xiWeilEvaluationLp_reflectionEvenTest F hF]
  exact xiWeilCliffordPairing_evenPart_eq_normSq (xiWeilEvaluationLp F hF)

/-- Non-circular scalar Weil positivity on the explicit reflection-even test sector. -/
theorem xiWeilPolarization_reflectionEvenTest_re_nonneg
    (F : ℂ → ℂ) (hF : XiWeilSquareSummable F) :
    0 ≤ (xiWeilPolarization (xiWeilReflectionEvenTest F)
      (xiWeilReflectionEvenTest F)).re := by
  rw [xiWeilPolarization_reflectionEvenTest_eq_normSq F hF]
  norm_cast
  positivity

/-- Exact energy target for any full positivity proof: RH is equivalent to reflection-even energy
dominating reflection-odd energy on every realized square-summable Xi evaluation packet. -/
theorem riemannHypothesis_iff_xiWeil_even_energy_dominates_odd :
    RiemannHypothesis ↔
      ∀ (F : ℂ → ℂ) (hF : XiWeilSquareSummable F),
        ‖xiWeilEvaluationLp F hF -
            xiWeilLineConjLinearIsometry (xiWeilEvaluationLp F hF)‖ ^ (2 : ℕ) ≤
          ‖xiWeilEvaluationLp F hF +
            xiWeilLineConjLinearIsometry (xiWeilEvaluationLp F hF)‖ ^ (2 : ℕ) := by
  rw [riemannHypothesis_iff_xiWeilPolarization_nonneg]
  constructor
  · intro h F hF
    let v : XiWeilCarrier := xiWeilEvaluationLp F hF
    have hq : 0 ≤ CliffordWeil.quadratic xiWeilLineConjLinearIsometry v := by
      change 0 ≤ xiWeilHilbertQuadratic v
      rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re F hF]
      exact h F hF
    have hbalance := CliffordWeil.four_mul_quadratic_eq_even_sub_odd
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive v
    nlinarith
  · intro h F hF
    let v : XiWeilCarrier := xiWeilEvaluationLp F hF
    have hdom := h F hF
    have hbalance := CliffordWeil.four_mul_quadratic_eq_even_sub_odd
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive v
    have hq : 0 ≤ CliffordWeil.quadratic xiWeilLineConjLinearIsometry v := by
      nlinarith
    change 0 ≤ xiWeilHilbertQuadratic v at hq
    rw [xiWeilHilbertQuadratic_evaluation_eq_polarization_re F hF] at hq
    exact hq

end RHTower
