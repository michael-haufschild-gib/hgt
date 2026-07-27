import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetRankTwoCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetHaarLayerSum
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedCanonicalCurrentBound
import GaloisForLFunctions.RHTower.TentMellinFactor

/-!
# Integrated cancellation of the phase-adapted reflected Haar current

This file identifies the actual integrated signed reflected Haar-prefix current with one half of
the canonical returned theta-tail/seam cross current.  The identification keeps the rank-two
source intact: no positive/negative part, density, seam, or translated row is estimated
separately.
-/

open Complex Real Polynomial MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private theorem integrableOn_id_mul_cexp_Ioi
    {c : ℂ} (hc : c.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * Complex.exp (c * (x : ℂ))) (Ioi 0) := by
  let a : ℝ := -c.re
  have ha : 0 < a := by dsimp only [a]; linarith
  have hmajor : IntegrableOn
      (fun x : ℝ => x ^ 1 * Real.exp (-a * x)) (Ioi 0) :=
    integrableOn_pow_mul_exp_neg_real 1 ha
  change Integrable (fun x : ℝ =>
    (x : ℂ) * Complex.exp (c * (x : ℂ)))
      (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · exact (Complex.continuous_ofReal.mul
      ((Complex.continuous_ofReal.const_mul c).cexp)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
      Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, pow_one]
    dsimp only [a]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hx0 (Real.exp_pos _).le)]
    ring_nf
    exact le_rfl

private theorem tendsto_id_mul_cexp_atTop_zero
    {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) * Complex.exp (c * (x : ℂ)))
      atTop (nhds 0) := by
  let a : ℝ := -c.re
  have ha : 0 < a := by dsimp only [a]; linarith
  have hscale : Tendsto (fun x : ℝ => a * x) atTop atTop :=
    tendsto_id.const_mul_atTop ha
  have hrealScaled :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hreal : Tendsto (fun x : ℝ => x * Real.exp (-a * x))
      atTop (nhds 0) := by
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℝ => a⁻¹)
      atTop (nhds a⁻¹)).mul hrealScaled
    convert hmul using 1
    · funext x
      simp only [Function.comp_apply, pow_one]
      rw [mul_assoc a x (Real.exp (-(a * x))),
        ← mul_assoc a⁻¹ a (x * Real.exp (-(a * x))),
        inv_mul_cancel₀ ha.ne', one_mul]
      congr 1
      ring
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hreal.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
    Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  dsimp only [a]
  congr 1
  ring

private theorem integral_id_mul_cexp_Ioi
    {c : ℂ} (hc : c.re < 0) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) * Complex.exp (c * (x : ℂ))) =
      1 / c ^ 2 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    norm_num at hc
  have hint := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_id_mul_cexp_Ioi hc) tendsto_id
  have hexp : Tendsto (fun x : ℝ => Complex.exp (c * (x : ℂ)))
      atTop (nhds 0) := by
    simpa [Complex.tendsto_exp_nhds_zero_iff] using
      tendsto_const_nhds.neg_mul_atTop hc tendsto_id
  have hid := tendsto_id_mul_cexp_atTop_zero hc
  have hboundary : Tendsto (fun x : ℝ =>
      (c * (x : ℂ) - 1) * Complex.exp (c * (x : ℂ))) atTop (nhds 0) := by
    have hlin := (hid.const_mul c).sub hexp
    convert hlin using 1
    · funext x
      ring
    · simp
  have hrhs : Tendsto (fun b : ℝ =>
      ((c * b - 1) * Complex.exp (c * b)) / c ^ 2 -
        ((c * (0 : ℝ) - 1) * Complex.exp (c * (0 : ℝ))) / c ^ 2)
      atTop (nhds (1 / c ^ 2)) := by
    have h := (hboundary.div_const (c ^ 2)).sub_const
      (((c * (0 : ℝ) - 1) * Complex.exp (c * (0 : ℝ))) / c ^ 2)
    simpa only [Complex.ofReal_zero, mul_zero, zero_sub, Complex.exp_zero,
      one_mul, neg_div, zero_div, sub_neg_eq_add, zero_add, neg_one_mul,
      neg_neg] using h
  apply tendsto_nhds_unique hint
  convert hrhs using 1
  funext b
  exact integral_id_mul_cexp c hc0 0 b

private lemma thetaHalfExponential_mul_phase_eq_cexp
    (z : ℂ) (x : ℝ) :
    (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z =
      Complex.exp ((-(1 / 2 : ℂ) + I * z) * (x : ℂ)) := by
  unfold spectralTranslationPhase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrableOn_thetaHalfExponential_mul_phase
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z) (Ioi 0) := by
  let c : ℂ := -(1 / 2 : ℂ) + I * z
  have hc : c.re < 0 := by
    dsimp only [c]
    simp [Complex.mul_re]
    linarith
  have h := integrableOn_exp_mul_complex_Ioi hc 0
  apply h.congr_fun
  · intro x _hx
    exact (thetaHalfExponential_mul_phase_eq_cexp z x).symm
  · exact measurableSet_Ioi

theorem integrableOn_thetaHalfExponential_mul_phaseDerivative
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  let c : ℂ := -(1 / 2 : ℂ) + I * z
  have hc : c.re < 0 := by
    dsimp only [c]
    simp [Complex.mul_re]
    linarith
  have h := (integrableOn_id_mul_cexp_Ioi hc).const_mul I
  apply h.congr
  filter_upwards with x
  calc
    I * ((x : ℂ) * Complex.exp (c * (x : ℂ))) =
        I * ((x : ℂ) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z)) := by
      rw [thetaHalfExponential_mul_phase_eq_cexp]
    _ = (Real.exp (-x / 2) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z) := by ring

theorem integral_Ioi_thetaHalfExponential_mul_phase
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z) =
      thetaHalfExponentialPhaseValue z := by
  let c : ℂ := -(1 / 2 : ℂ) + I * z
  have hc : c.re < 0 := by
    dsimp only [c]
    simp [Complex.mul_re]
    linarith
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun x _hx => thetaHalfExponential_mul_phase_eq_cexp z x),
    integral_exp_mul_complex_Ioi hc 0]
  unfold thetaHalfExponentialPhaseValue
  dsimp only [c]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (-(1 / 2 : ℂ) + I * z) =
      -((1 / 2 : ℂ) - I * z) by ring]
  rw [div_eq_mul_inv, inv_neg]
  ring

theorem integral_Ioi_thetaHalfExponential_mul_phaseDerivative
    {z : ℂ} (hz : -(1 / 2 : ℝ) < z.im) :
    (∫ x : ℝ in Ioi 0,
      (Real.exp (-x / 2) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) =
      thetaHalfExponentialPhaseDerivative z := by
  let c : ℂ := -(1 / 2 : ℂ) + I * z
  have hc : c.re < 0 := by
    dsimp only [c]
    simp [Complex.mul_re]
    linarith
  rw [show (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) =
      fun x : ℝ => I * ((x : ℂ) * Complex.exp (c * (x : ℂ))) by
    funext x
    calc
      (Real.exp (-x / 2) : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z) =
        I * ((x : ℂ) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z)) := by ring
      _ = I * ((x : ℂ) * Complex.exp (c * (x : ℂ))) := by
        rw [thetaHalfExponential_mul_phase_eq_cexp],
    MeasureTheory.integral_const_mul,
    integral_id_mul_cexp_Ioi hc]
  unfold thetaHalfExponentialPhaseDerivative
  dsimp only [c]
  congr 1
  field_simp
  ring

private theorem integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phase
    (a : ℝ) {z : ℂ} (hz0 : 0 ≤ z.im) (hzHalf : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
        spectralTranslationPhase x z) (Ioi 0) := by
  let f : ℝ → ℂ := fun y =>
    (thetaCuspTailSecondEvenRemainder y : ℂ) * spectralTranslationPhase y z
  have hf : Integrable f := by
    simpa only [f] using
      integrable_thetaCuspTailSecondEvenRemainder_mul_phase hz0 hzHalf
  have hshift : Integrable (fun x : ℝ => f (x - a)) :=
    (measurePreserving_sub_right (volume : Measure ℝ) a).integrable_comp_of_integrable hf
  have hscaled := hshift.const_mul (spectralTranslationPhase a z)
  apply hscaled.integrableOn.congr_fun
  · intro x _hx
    dsimp only [f]
    rw [show spectralTranslationPhase a z *
        ((thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
          spectralTranslationPhase (x - a) z) =
        (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
          (spectralTranslationPhase (x - a) z *
            spectralTranslationPhase a z) by ring,
      ← spectralTranslationPhase_add]
    congr 2
    ring
  · exact measurableSet_Ioi

private theorem
    integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phaseDerivative
    (a : ℝ) {z : ℂ} (hz0 : 0 ≤ z.im) (hzHalf : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  let fV : ℝ → ℂ := fun y =>
    (thetaCuspTailSecondEvenRemainder y : ℂ) * spectralTranslationPhase y z
  let fD : ℝ → ℂ := fun y =>
    (thetaCuspTailSecondEvenRemainder y : ℂ) *
      ((y : ℂ) * I * spectralTranslationPhase y z)
  have hfV : Integrable fV := by
    simpa only [fV] using
      integrable_thetaCuspTailSecondEvenRemainder_mul_phase hz0 hzHalf
  have hfD : Integrable fD := by
    simpa only [fD] using
      integrable_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative hz0 hzHalf
  have hshiftV : Integrable (fun x : ℝ => fV (x - a)) :=
    (measurePreserving_sub_right (volume : Measure ℝ) a).integrable_comp_of_integrable hfV
  have hshiftD : Integrable (fun x : ℝ => fD (x - a)) :=
    (measurePreserving_sub_right (volume : Measure ℝ) a).integrable_comp_of_integrable hfD
  have hcombined :=
    (hshiftD.add (hshiftV.const_mul ((a : ℂ) * I))).const_mul
      (spectralTranslationPhase a z)
  apply hcombined.integrableOn.congr_fun
  · intro x _hx
    dsimp only [fV, fD]
    change spectralTranslationPhase a z *
        ((thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
            (((x - a : ℝ) : ℂ) * I * spectralTranslationPhase (x - a) z) +
          (a : ℂ) * I *
            ((thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
              spectralTranslationPhase (x - a) z)) =
      (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)
    rw [show spectralTranslationPhase a z *
        ((thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
            (((x - a : ℝ) : ℂ) * I * spectralTranslationPhase (x - a) z) +
          (a : ℂ) * I *
            ((thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
              spectralTranslationPhase (x - a) z)) =
        (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
          ((x : ℂ) * I *
            (spectralTranslationPhase (x - a) z *
              spectralTranslationPhase a z)) by
      push_cast
      ring,
      ← spectralTranslationPhase_add]
    congr 3
    ring
  · exact measurableSet_Ioi

theorem integrableOn_thetaCuspTailSecondDensity_mul_phase
    {z : ℂ} (hz0 : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z) (Ioi 0) := by
  have hrem := integrableOn_thetaCuspTailSecondEvenRemainder_mul_phase hz0
  have hseam := integrableOn_thetaHalfExponential_mul_phase (z := z) (by linarith)
  have hsum := hrem.add (hseam.const_mul (1 / 2 : ℂ))
  apply hsum.congr_fun
  · intro x _hx
    change (thetaCuspTailSecondEvenRemainder x : ℂ) *
          spectralTranslationPhase x z +
        (1 / 2 : ℂ) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z) =
      (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z
    unfold thetaCuspTailSecondEvenRemainder
    push_cast
    ring
  · exact measurableSet_Ioi

theorem integrableOn_thetaCuspTailSecondDensity_mul_phaseDerivative
    {z : ℂ} (hz0 : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  have hrem := integrableOn_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative hz0
  have hseam := integrableOn_thetaHalfExponential_mul_phaseDerivative (z := z) (by linarith)
  have hsum := hrem.add (hseam.const_mul (1 / 2 : ℂ))
  apply hsum.congr_fun
  · intro x _hx
    change (thetaCuspTailSecondEvenRemainder x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z) +
        (1 / 2 : ℂ) *
          ((Real.exp (-x / 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z)) =
      (thetaCuspTailSecondDensity x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)
    unfold thetaCuspTailSecondEvenRemainder
    push_cast
    ring
  · exact measurableSet_Ioi

private theorem real_weighted_finset_sum_mul_complex_kernel
    {I : Type*} (s : Finset I) (a b : I → ℝ) (K : ℂ) :
    ∑ i ∈ s, (a i : ℂ) * ((b i : ℂ) * K) =
      (((∑ i ∈ s, a i * b i : ℝ) : ℝ) : ℂ) * K := by
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem integrableOn_phaseAdaptedWeightedHaarResidualSource_mul_phase
    (P : ℝ[X]) (tau : ℝ) (N : ℕ) {z : ℂ}
    (hz0 : 0 ≤ z.im) (hzHalf : z.im < 1 / 2)
    (hq : P.eval dyadicProuhetDecayCharacter = 1)
    (hr : P.eval dyadicProuhetGrowthCharacter = tau) :
    IntegrableOn (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          spectralTranslationPhase x z) (Ioi 0) := by
  have hrows : IntegrableOn (fun x : ℝ =>
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            spectralTranslationPhase x z)) (Ioi 0) :=
    MeasureTheory.integrable_finsetSum P.support fun j _hj =>
      (integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phase
        (((N + j : ℕ) : ℝ) * Real.log 2) hz0 hzHalf).const_mul
          (P.coeff j : ℂ)
  have hdensity := integrableOn_thetaCuspTailSecondDensity_mul_phase hz0
  have hseam := integrableOn_thetaHalfExponential_mul_phase (z := z) (by linarith)
  have htotal :=
    ((hrows.const_mul (dyadicEvenRemoteAmplitude N : ℂ)).sub hdensity).add
      (hseam.const_mul (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)))
  apply htotal.congr
  filter_upwards with x
  ·
    have hrowsPoint := real_weighted_finset_sum_mul_complex_kernel
      P.support P.coeff
        (fun j => thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2))
        (spectralTranslationPhase x z)
    rw [phaseAdaptedWeightedHaarResidualSource_eq_source P tau N x hq hr]
    change (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                spectralTranslationPhase x z)) -
        (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z) =
      ((dyadicEvenRemoteAmplitude N *
            (∑ j ∈ P.support, P.coeff j *
              thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
          thetaCuspTailSecondDensity x +
          (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) : ℝ) : ℂ) *
            spectralTranslationPhase x z
    rw [hrowsPoint]
    push_cast
    ring

private theorem
    integrableOn_phaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative
    (P : ℝ[X]) (tau : ℝ) (N : ℕ) {z : ℂ}
    (hz0 : 0 ≤ z.im) (hzHalf : z.im < 1 / 2)
    (hq : P.eval dyadicProuhetDecayCharacter = 1)
    (hr : P.eval dyadicProuhetGrowthCharacter = tau) :
    IntegrableOn (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  have hrows : IntegrableOn (fun x : ℝ =>
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z))) (Ioi 0) :=
    MeasureTheory.integrable_finsetSum P.support fun j _hj =>
      (integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phaseDerivative
        (((N + j : ℕ) : ℝ) * Real.log 2) hz0 hzHalf).const_mul
          (P.coeff j : ℂ)
  have hdensity := integrableOn_thetaCuspTailSecondDensity_mul_phaseDerivative hz0
  have hseam := integrableOn_thetaHalfExponential_mul_phaseDerivative (z := z) (by linarith)
  have htotal :=
    ((hrows.const_mul (dyadicEvenRemoteAmplitude N : ℂ)).sub hdensity).add
      (hseam.const_mul (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)))
  apply htotal.congr
  filter_upwards with x
  ·
    have hrowsPoint := real_weighted_finset_sum_mul_complex_kernel
      P.support P.coeff
        (fun j => thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2))
        ((x : ℂ) * I * spectralTranslationPhase x z)
    rw [phaseAdaptedWeightedHaarResidualSource_eq_source P tau N x hq hr]
    change (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                ((x : ℂ) * I * spectralTranslationPhase x z))) -
        (thetaCuspTailSecondDensity x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z) +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          ((Real.exp (-x / 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z)) =
      ((dyadicEvenRemoteAmplitude N *
            (∑ j ∈ P.support, P.coeff j *
              thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
          thetaCuspTailSecondDensity x +
          (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) : ℝ) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z)
    rw [hrowsPoint]
    push_cast
    ring

/-- The coefficient polynomial used by the canonical weighted reflected Haar prefix. -/
def canonicalPhaseAdaptedWeightedHaarPolynomial
    (m : ℕ) (z : ℂ) (tau : ℝ) : ℝ[X] :=
  phaseAdaptedTwoEndpointProuhetPolynomial m
    (spectralTranslationPhase (Real.log 2) z)
    dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau

theorem canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay
    (m : ℕ) {z : ℂ} (hzHalf : z.im < 1 / 2) (tau : ℝ) :
    (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau).eval
      dyadicProuhetDecayCharacter = 1 := by
  unfold canonicalPhaseAdaptedWeightedHaarPolynomial
  exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_left m
    (spectralTranslationPhase (Real.log 2) z)
    (phaseAdaptedProuhetBase_eval_dyadicDecay_ne_zero m hzHalf)

theorem canonicalPhaseAdaptedWeightedHaarPolynomial_eval_growth
    (m : ℕ) {z : ℂ} (hz0 : 0 < z.im) (tau : ℝ) :
    (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau).eval
      dyadicProuhetGrowthCharacter = tau := by
  unfold canonicalPhaseAdaptedWeightedHaarPolynomial
  exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_right m
    (spectralTranslationPhase (Real.log 2) z)
    (phaseAdaptedProuhetBase_eval_dyadicGrowth_ne_zero m hz0)
    (sub_ne_zero.mpr dyadicProuhetDecayCharacter_ne_growthCharacter.symm)

theorem integrableOn_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phase
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau)
        dyadicProuhetDecayCharacter N x : ℂ) *
          spectralTranslationPhase x z) (Ioi 0) :=
  integrableOn_phaseAdaptedWeightedHaarResidualSource_mul_phase
    (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau) tau N hz0.le hzHalf
    (canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay m hzHalf tau)
    (canonicalPhaseAdaptedWeightedHaarPolynomial_eval_growth m hz0 tau)

theorem
    integrableOn_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    IntegrableOn (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau)
        dyadicProuhetDecayCharacter N x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) :=
  integrableOn_phaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative
    (canonicalPhaseAdaptedWeightedHaarPolynomial m z tau) tau N hz0.le hzHalf
    (canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay m hzHalf tau)
    (canonicalPhaseAdaptedWeightedHaarPolynomial_eval_growth m hz0 tau)

/-- Exact positive-half-line value transform of the canonical weighted Haar residual.  The
double phase root removes the full-line translate packet before any estimate is made. -/
theorem integral_Ioi_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phase_eq
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    (∫ x : ℝ in Ioi 0,
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          spectralTranslationPhase x z) =
      -phaseAdaptedCriticalReturnedValuePairing P N z -
        thetaCuspTailSecondDensityPhaseValue z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          thetaHalfExponentialPhaseValue z := by
  dsimp only
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  have hq : P.eval dyadicProuhetDecayCharacter = 1 := by
    exact canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay m hzHalf tau
  have hr : P.eval dyadicProuhetGrowthCharacter = tau := by
    exact canonicalPhaseAdaptedWeightedHaarPolynomial_eval_growth m hz0 tau
  have hrow (j : ℕ) : IntegrableOn (fun x : ℝ =>
      (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            spectralTranslationPhase x z)) (Ioi 0) :=
    (integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phase
      (((N + j : ℕ) : ℝ) * Real.log 2) hz0.le hzHalf).const_mul
        (P.coeff j : ℂ)
  have hrows : IntegrableOn (fun x : ℝ =>
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            spectralTranslationPhase x z)) (Ioi 0) :=
    MeasureTheory.integrable_finsetSum P.support fun j _hj => hrow j
  have hremote := hrows.const_mul (dyadicEvenRemoteAmplitude N : ℂ)
  have hdensity := integrableOn_thetaCuspTailSecondDensity_mul_phase hz0.le
  have hseam := integrableOn_thetaHalfExponential_mul_phase (z := z) (by linarith)
  have hpoint : (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          spectralTranslationPhase x z) = fun x : ℝ =>
      (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                spectralTranslationPhase x z)) -
        (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z) := by
    funext x
    have hrowsPoint := real_weighted_finset_sum_mul_complex_kernel
      P.support P.coeff
        (fun j => thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2))
        (spectralTranslationPhase x z)
    rw [phaseAdaptedWeightedHaarResidualSource_eq_source P tau N x hq hr]
    change ((dyadicEvenRemoteAmplitude N *
            (∑ j ∈ P.support, P.coeff j *
              thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
          thetaCuspTailSecondDensity x +
          (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) : ℝ) : ℂ) *
            spectralTranslationPhase x z = _
    rw [hrowsPoint]
    push_cast
    ring
  rw [hpoint]
  calc
    (∫ x : ℝ in Ioi 0,
        (dyadicEvenRemoteAmplitude N : ℂ) *
            (∑ j ∈ P.support, (P.coeff j : ℂ) *
              ((thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                  spectralTranslationPhase x z)) -
          (thetaCuspTailSecondDensity x : ℂ) * spectralTranslationPhase x z +
          (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
            ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z)) =
      (∫ x : ℝ in Ioi 0,
        (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                spectralTranslationPhase x z))) -
        thetaCuspTailSecondDensityPhaseValue z +
        (∫ x : ℝ in Ioi 0,
          (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
            ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z)) := by
      change (∫ x : ℝ,
          (((fun x : ℝ => (dyadicEvenRemoteAmplitude N : ℂ) *
                (∑ j ∈ P.support, (P.coeff j : ℂ) *
                  ((thetaCuspTailSecondEvenRemainder
                    (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                      spectralTranslationPhase x z))) -
              (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
                spectralTranslationPhase x z)) +
            (fun x : ℝ =>
              (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
                ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase x z))) x
            ∂(volume.restrict (Ioi 0))) = _
      have hadd := MeasureTheory.integral_add (hremote.sub hdensity)
        (hseam.const_mul (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)))
      have hsub := MeasureTheory.integral_sub hremote hdensity
      change (∫ a : ℝ in Ioi 0,
          ((fun x : ℝ => (dyadicEvenRemoteAmplitude N : ℂ) *
              (∑ j ∈ P.support, (P.coeff j : ℂ) *
                ((thetaCuspTailSecondEvenRemainder
                  (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                    spectralTranslationPhase x z))) -
            (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
              spectralTranslationPhase x z)) a) = _ at hsub
      rw [hsub] at hadd
      unfold thetaCuspTailSecondDensityPhaseValue
      simpa only [Pi.add_apply, Pi.sub_apply] using hadd
    _ = (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            (∫ x : ℝ in Ioi 0,
              (thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                  spectralTranslationPhase x z)) -
        thetaCuspTailSecondDensityPhaseValue z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          thetaHalfExponentialPhaseValue z := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finsetSum]
      · simp_rw [MeasureTheory.integral_const_mul]
        rw [integral_Ioi_thetaHalfExponential_mul_phase (by linarith)]
      · intro j _hj
        exact hrow j
    _ = _ := by
      have hpacket :=
        phaseAdaptedProuhet_evenRemainderHalfLineValue_sum_eq_neg_returned
          m N dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau
            (Real.log 2) hz0.le hzHalf
      dsimp only at hpacket
      have hP : P = phaseAdaptedTwoEndpointProuhetPolynomial m
          (spectralTranslationPhase (Real.log 2) z)
          dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau := rfl
      rw [← hP] at hpacket
      rw [hpacket]
      have hpair : (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            thetaCuspTailSecondEvenRemainderReturnedValue
              (((N + j : ℕ) : ℝ) * Real.log 2) z) =
          phaseAdaptedCriticalReturnedValuePairing P N z := by
        unfold phaseAdaptedCriticalReturnedValuePairing
          realPolynomialComplexCoefficientPairing Polynomial.sum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [← hpair]
      ring

/-- Exact derivative transform companion of the canonical weighted Haar residual. -/
theorem
    integral_Ioi_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative_eq
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
    (∫ x : ℝ in Ioi 0,
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z)) =
      phaseAdaptedCriticalReturnedDerivativePairing P N z -
        thetaCuspTailSecondDensityPhaseDerivative z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          thetaHalfExponentialPhaseDerivative z := by
  dsimp only
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  have hq : P.eval dyadicProuhetDecayCharacter = 1 := by
    exact canonicalPhaseAdaptedWeightedHaarPolynomial_eval_decay m hzHalf tau
  have hr : P.eval dyadicProuhetGrowthCharacter = tau := by
    exact canonicalPhaseAdaptedWeightedHaarPolynomial_eval_growth m hz0 tau
  have hrow (j : ℕ) : IntegrableOn (fun x : ℝ =>
      (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z))) (Ioi 0) :=
    (integrableOn_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phaseDerivative
      (((N + j : ℕ) : ℝ) * Real.log 2) hz0.le hzHalf).const_mul
        (P.coeff j : ℂ)
  have hrows : IntegrableOn (fun x : ℝ =>
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        ((thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z))) (Ioi 0) :=
    MeasureTheory.integrable_finsetSum P.support fun j _hj => hrow j
  have hremote := hrows.const_mul (dyadicEvenRemoteAmplitude N : ℂ)
  have hdensity := integrableOn_thetaCuspTailSecondDensity_mul_phaseDerivative hz0.le
  have hseam := integrableOn_thetaHalfExponential_mul_phaseDerivative
    (z := z) (by linarith)
  have hpoint : (fun x : ℝ =>
      (phaseAdaptedWeightedHaarResidualSource
        P dyadicProuhetDecayCharacter N x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z)) = fun x : ℝ =>
      (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                ((x : ℂ) * I * spectralTranslationPhase x z))) -
        (thetaCuspTailSecondDensity x : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase x z) +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          ((Real.exp (-x / 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z)) := by
    funext x
    have hrowsPoint := real_weighted_finset_sum_mul_complex_kernel
      P.support P.coeff
        (fun j => thetaCuspTailSecondEvenRemainder
          (x - ((N + j : ℕ) : ℝ) * Real.log 2))
        ((x : ℂ) * I * spectralTranslationPhase x z)
    rw [phaseAdaptedWeightedHaarResidualSource_eq_source P tau N x hq hr]
    change ((dyadicEvenRemoteAmplitude N *
            (∑ j ∈ P.support, P.coeff j *
              thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
          thetaCuspTailSecondDensity x +
          (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) : ℝ) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z) = _
    rw [hrowsPoint]
    push_cast
    ring
  rw [hpoint]
  calc
    (∫ x : ℝ in Ioi 0,
        (dyadicEvenRemoteAmplitude N : ℂ) *
            (∑ j ∈ P.support, (P.coeff j : ℂ) *
              ((thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                  ((x : ℂ) * I * spectralTranslationPhase x z))) -
          (thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase x z) +
          (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
            ((Real.exp (-x / 2) : ℂ) *
              ((x : ℂ) * I * spectralTranslationPhase x z))) =
      (∫ x : ℝ in Ioi 0,
        (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            ((thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                ((x : ℂ) * I * spectralTranslationPhase x z)))) -
        thetaCuspTailSecondDensityPhaseDerivative z +
        (∫ x : ℝ in Ioi 0,
          (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
            ((Real.exp (-x / 2) : ℂ) *
              ((x : ℂ) * I * spectralTranslationPhase x z))) := by
      change (∫ x : ℝ,
          (((fun x : ℝ => (dyadicEvenRemoteAmplitude N : ℂ) *
                (∑ j ∈ P.support, (P.coeff j : ℂ) *
                  ((thetaCuspTailSecondEvenRemainder
                    (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                      ((x : ℂ) * I * spectralTranslationPhase x z)))) -
              (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
                ((x : ℂ) * I * spectralTranslationPhase x z))) +
            (fun x : ℝ =>
              (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
                ((Real.exp (-x / 2) : ℂ) *
                  ((x : ℂ) * I * spectralTranslationPhase x z)))) x
            ∂(volume.restrict (Ioi 0))) = _
      have hadd := MeasureTheory.integral_add (hremote.sub hdensity)
        (hseam.const_mul (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)))
      have hsub := MeasureTheory.integral_sub hremote hdensity
      change (∫ a : ℝ in Ioi 0,
          ((fun x : ℝ => (dyadicEvenRemoteAmplitude N : ℂ) *
              (∑ j ∈ P.support, (P.coeff j : ℂ) *
                ((thetaCuspTailSecondEvenRemainder
                  (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                    ((x : ℂ) * I * spectralTranslationPhase x z)))) -
            (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
              ((x : ℂ) * I * spectralTranslationPhase x z))) a) = _ at hsub
      rw [hsub] at hadd
      unfold thetaCuspTailSecondDensityPhaseDerivative
      simpa only [Pi.add_apply, Pi.sub_apply] using hadd
    _ = (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            (∫ x : ℝ in Ioi 0,
              (thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2) : ℂ) *
                  ((x : ℂ) * I * spectralTranslationPhase x z))) -
        thetaCuspTailSecondDensityPhaseDerivative z +
        (((((2 : ℝ) ^ N * tau + 1) / 4 : ℝ) : ℂ)) *
          thetaHalfExponentialPhaseDerivative z := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finsetSum]
      · simp_rw [MeasureTheory.integral_const_mul]
        rw [integral_Ioi_thetaHalfExponential_mul_phaseDerivative (by linarith)]
      · intro j _hj
        exact hrow j
    _ = _ := by
      have hpacket :=
        phaseAdaptedProuhet_evenRemainderHalfLineDerivative_sum_eq_returned
          m N dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau
            (Real.log 2) hz0.le hzHalf
      dsimp only at hpacket
      have hP : P = phaseAdaptedTwoEndpointProuhetPolynomial m
          (spectralTranslationPhase (Real.log 2) z)
          dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau := rfl
      rw [← hP] at hpacket
      rw [hpacket]
      have hpair : (dyadicEvenRemoteAmplitude N : ℂ) *
          (∑ j ∈ P.support, (P.coeff j : ℂ) *
            thetaCuspTailSecondEvenRemainderReturnedDerivative
              (((N + j : ℕ) : ℝ) * Real.log 2) z) =
          phaseAdaptedCriticalReturnedDerivativePairing P N z := by
        unfold phaseAdaptedCriticalReturnedDerivativePairing
          realPolynomialComplexCoefficientPairing Polynomial.sum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [hpair]

/-- The literal integrated signed reflected Haar prefix at an arbitrary prescribed endpoint. -/
def phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint
    (m N : ℕ) (z : ℂ) (tau : ℝ) : ℝ :=
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  ∫ p : ℝ × ℝ,
    phaseAdaptedWeightedReflectedHaarPrefixSource
        P dyadicProuhetDecayCharacter N p *
      symmetricHermitianPairCurrentKernel
        (fun x : ℝ => spectralTranslationPhase x z)
        (fun x : ℝ => (x : ℂ) * I * spectralTranslationPhase x z) p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- The arbitrary-endpoint integrated prefix is exactly one half of the corresponding returned
source current.  No self-consistent choice is used in this identity. -/
theorem phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint_eq
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (tau : ℝ) :
    phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z tau =
      (1 / 2 : ℝ) *
        phaseAdaptedCriticalReturnedSourceCurrent m N
          (spectralTranslationPhase (Real.log 2) z)
          dyadicProuhetGrowthCharacter tau z
          (thetaCuspTailSecondDensityPhaseValue z)
          (thetaCuspTailSecondDensityPhaseDerivative z)
          (thetaHalfExponentialPhaseValue z)
          (thetaHalfExponentialPhaseDerivative z) := by
  let P := canonicalPhaseAdaptedWeightedHaarPolynomial m z tau
  let A : ℝ → ℝ := phaseAdaptedWeightedHaarResidualSource
    P dyadicProuhetDecayCharacter N
  let E : ℝ → ℝ := fun x => Real.exp (-x / 2)
  let V : ℝ → ℂ := fun x => spectralTranslationPhase x z
  let D : ℝ → ℂ := fun x => (x : ℂ) * I * spectralTranslationPhase x z
  have hAV : IntegrableOn (fun x : ℝ => (A x : ℂ) * V x) (Ioi 0) := by
    simpa only [A, V, P] using
      integrableOn_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phase
        m N hz0 hzHalf tau
  have hAD : IntegrableOn (fun x : ℝ => (A x : ℂ) * D x) (Ioi 0) := by
    simpa only [A, D, P] using
      integrableOn_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative
        m N hz0 hzHalf tau
  have hEV : IntegrableOn (fun x : ℝ => (E x : ℂ) * V x) (Ioi 0) := by
    simpa only [E, V] using
      integrableOn_thetaHalfExponential_mul_phase (z := z) (by linarith)
  have hED : IntegrableOn (fun x : ℝ => (E x : ℂ) * D x) (Ioi 0) := by
    simpa only [E, D] using
      integrableOn_thetaHalfExponential_mul_phaseDerivative (z := z) (by linarith)
  have hfubini := integral_rankTwoSource_mul_symmetricHermitianPairCurrent_eq
    A E V D hAV hAD hEV hED
  have hsource : (fun p : ℝ × ℝ =>
      phaseAdaptedWeightedReflectedHaarPrefixSource
          P dyadicProuhetDecayCharacter N p *
        symmetricHermitianPairCurrentKernel V D p) =
      fun p : ℝ × ℝ =>
        ((1 / 2 : ℝ) * (A p.1 * E p.2 + E p.1 * A p.2)) *
          symmetricHermitianPairCurrentKernel V D p := by
    funext p
    rcases p with ⟨x, y⟩
    rw [phaseAdaptedWeightedReflectedHaarPrefixSource_eq_rankTwo]
  unfold phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint
  dsimp only
  change (∫ p : ℝ × ℝ,
      phaseAdaptedWeightedReflectedHaarPrefixSource
          P dyadicProuhetDecayCharacter N p *
        symmetricHermitianPairCurrentKernel V D p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) = _
  rw [hsource, hfubini]
  have hAValue :=
    integral_Ioi_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phase_eq
      m N hz0 hzHalf tau
  have hADerivative :=
    integral_Ioi_canonicalPhaseAdaptedWeightedHaarResidualSource_mul_phaseDerivative_eq
      m N hz0 hzHalf tau
  dsimp only at hAValue hADerivative
  change (∫ x : ℝ in Ioi 0, (A x : ℂ) * V x) = _ at hAValue
  change (∫ x : ℝ in Ioi 0, (A x : ℂ) * D x) = _ at hADerivative
  have hEValue := integral_Ioi_thetaHalfExponential_mul_phase
    (z := z) (by linarith)
  have hEDerivative := integral_Ioi_thetaHalfExponential_mul_phaseDerivative
    (z := z) (by linarith)
  change (∫ x : ℝ in Ioi 0, (E x : ℂ) * V x) = _ at hEValue
  change (∫ x : ℝ in Ioi 0, (E x : ℂ) * D x) = _ at hEDerivative
  rw [hAValue, hADerivative, hEValue, hEDerivative]
  unfold phaseAdaptedCriticalReturnedSourceCurrent
  dsimp only [P]
  rfl

/-- The actual integrated signed reflected Haar-prefix current at the self-consistent endpoint. -/
def canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent
    (m N : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint m N z
    (canonicalThetaTailSeamProuhetEndpoint m N z)

/-- **Integrated Haar-current identification.**  The actual signed reflected Haar-prefix current
is exactly one half of the canonical returned theta-tail/seam cross current. -/
theorem canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq
    (m N : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent m N z =
      (1 / 2 : ℝ) * canonicalThetaTailSeamProuhetUntruncatedCurrent m N z :=
  phaseAdaptedWeightedReflectedHaarIntegratedCurrentAtEndpoint_eq m N hz0 hzHalf
    (canonicalThetaTailSeamProuhetEndpoint m N z)

/-- In the canonical strip, a finite signed reflected Haar prefix has exactly zero integrated
oriented current. -/
theorem exists_canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq_zero
    (m : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    ∃ N : ℕ,
      canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent m N z = 0 := by
  obtain ⟨N, hN⟩ :=
    exists_canonicalThetaTailSeamProuhetUntruncatedCurrent_eq_zero m hz0 hzHalf
  refine ⟨N, ?_⟩
  rw [canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq
    m N hz0 hzHalf, hN, mul_zero]

/-- **Anisotropic sublinear upper current for the actual signed Haar-layer sum.**  For every
admissible schedule and every packet order, the Haar depth may be selected separately at each mesh
point so that the integrated signed reflected Haar-prefix current is strictly below an arbitrary
positive multiple of `(n+1)` times the squared final scheduled Taylor value. -/
theorem
    eventually_exists_canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_lt_scaled_normSq
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (sigma : ℂ) (hsigma0 : 0 < sigma.re) (hsigmaHalf : sigma.re < 1 / 2)
    (m : ℕ → ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∃ N : ℕ,
      canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent
          (m n) N (xiCTaylorAnisotropicCenteredPoint sigma n) <
        (epsilon * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hpositive :=
    eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
      hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hpositive, himPos, himHalf] with n hn hzn0 hznHalf
  obtain ⟨N, hcurrent⟩ :=
    exists_canonicalPhaseAdaptedWeightedReflectedHaarIntegratedCurrent_eq_zero
      (m n) hzn0 hznHalf
  refine ⟨N, ?_⟩
  rw [hcurrent]
  simpa only [zero_mul] using hn

end

end RHTower
