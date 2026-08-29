import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthGeneralModularClosure
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthBellTransfer

open Complex Real

namespace RHTower

noncomputable section

/-- Rank-three D1 after division by the sixth power of the literal normalized source. -/
def thetaCuspReflectedEighthSourceProjectiveValue (x : ℝ) : ℝ :=
  (thetaCuspReflectedEighthSourcePositiveModularValue x).re /
    (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re ^ 6

/-- Polynomial numerator of the projective D1 derivative along the exact source-positive flow. -/
def thetaCuspReflectedEighthSourceProjectiveDrift (x : ℝ) : ℝ :=
  let v := fun i => thetaCuspModularSourcePositiveState i x
  let q := (v HTGeometry.ModularThetaSourcePositiveState.Q).re
  let P := HTGeometry.modularThetaSourcePositiveReflectedEighthPolynomial
  let LP := HTGeometry.modularThetaSourcePositiveLie P
  let LQ := HTGeometry.modularThetaSourcePositiveVectorField
    HTGeometry.ModularThetaSourcePositiveState.Q
  q * (MvPolynomial.eval v LP).re -
    6 * (MvPolynomial.eval v P).re * (MvPolynomial.eval v LQ).re

/-- The exact source-positive projective observable differentiates by one polynomial drift. -/
theorem hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue
    (x : ℝ) :
    HasDerivAt thetaCuspReflectedEighthSourceProjectiveValue
      (thetaCuspReflectedEighthSourceProjectiveDrift x /
        (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x).re ^ 7) x := by
  let v := fun i => thetaCuspModularSourcePositiveState i
  let P := HTGeometry.modularThetaSourcePositiveReflectedEighthPolynomial
  have hP := HTGeometry.hasDerivAt_eval_modularThetaSourcePositivePolynomial
    P v x (hasDerivAt_thetaCuspModularSourcePositiveState x)
  have hPre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hP
  have hQ := hasDerivAt_thetaCuspModularSourcePositiveState x
    HTGeometry.ModularThetaSourcePositiveState.Q
  have hQre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hQ
  have hqpos : 0 < (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re := by
    rw [thetaCuspModularSourcePositiveState_Q_eq_sourceFactor]
    exact thetaCuspModularSourceFactor_re_pos x
  have hquot := hPre.div (hQre.pow 6) (pow_ne_zero 6 hqpos.ne')
  have hfun :
      (Complex.reCLM ∘ (fun y => MvPolynomial.eval (fun j => v j y) P)) /
          (Complex.reCLM ∘ thetaCuspModularSourcePositiveState
            HTGeometry.ModularThetaSourcePositiveState.Q) ^ 6 =
        thetaCuspReflectedEighthSourceProjectiveValue := by
    funext y
    rfl
  rw [hfun] at hquot
  refine hquot.congr_deriv ?_
  dsimp only [thetaCuspReflectedEighthSourceProjectiveDrift,
    thetaCuspReflectedEighthSourcePositiveModularValue, v, P,
    Function.comp_apply, Pi.pow_apply]
  simp only [Complex.reCLM_apply, Nat.cast_ofNat, Nat.reduceSub]
  field_simp [hqpos.ne']

/-- The projective modular observable is exactly four times native normalized D1. -/
theorem thetaCuspReflectedEighthSourceProjectiveValue_eq_four_mul_fullReflection
    {x : ℝ} (hx : 0 < x) :
    thetaCuspReflectedEighthSourceProjectiveValue x =
      4 * thetaCuspFullReflectionEighthHankelCurvature x := by
  let q := (thetaCuspModularSourcePositiveState
    HTGeometry.ModularThetaSourcePositiveState.Q x).re
  have hqpos : 0 < q := by
    simpa only [q] using thetaCuspModularSourcePositiveState_re_pos hx
      HTGeometry.ModularThetaSourcePositiveState.Q
  have hsourceValue := congrArg Complex.re
    (thetaCuspReflectedEighthSourcePositiveModularValue_eq_normalized x)
  have hrawMod :=
    thetaCuspFullSourceReflectionEighthHankelCurvature_eq_mass_pow_six_mul_normalized_re x
  rw [← hsourceValue] at hrawMod
  have hrawNative := thetaCuspFullSourceReflectionEighthHankelCurvature_eq_fullReflection hx
  have hsource : thetaCuspFullSource x =
      Bottcher.completedThetaProfile x * q := by
    have h := congrArg Complex.re
      (ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ x)
    rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at h
    have hQim := thetaCuspModularSourcePositiveState_im_eq_zero x
      HTGeometry.ModularThetaSourcePositiveState.Q
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, hQim, sub_zero] at h
    simpa only [q] using h
  rw [hsource, mul_pow] at hrawNative
  have hHpos := thetaCuspCompletedThetaProfile_pos x
  have hvalue :
      (thetaCuspReflectedEighthSourcePositiveModularValue x).re =
        4 * q ^ 6 * thetaCuspFullReflectionEighthHankelCurvature x := by
    nlinarith [pow_pos hHpos 6]
  dsimp only [thetaCuspReflectedEighthSourceProjectiveValue]
  change (thetaCuspReflectedEighthSourcePositiveModularValue x).re / q ^ 6 = _
  rw [hvalue]
  field_simp [hqpos.ne']

/-- Native normalized D1 has the same projective drift, up to the exact factor four. -/
theorem hasDerivAt_thetaCuspFullReflectionEighthHankelCurvature_projectiveDrift
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFullReflectionEighthHankelCurvature
      (thetaCuspReflectedEighthSourceProjectiveDrift x /
        (4 * (thetaCuspModularSourcePositiveState
          HTGeometry.ModularThetaSourcePositiveState.Q x).re ^ 7)) x := by
  have heq : thetaCuspReflectedEighthSourceProjectiveValue =ᶠ[nhds x]
      fun y => 4 * thetaCuspFullReflectionEighthHankelCurvature y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact thetaCuspReflectedEighthSourceProjectiveValue_eq_four_mul_fullReflection hy
  have hscaled :=
    (hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue x).congr_of_eventuallyEq heq.symm
  have hquarter := hscaled.const_mul (1 / 4 : ℝ)
  have hfun : (fun y => (1 / 4 : ℝ) *
      (4 * thetaCuspFullReflectionEighthHankelCurvature y)) =
      thetaCuspFullReflectionEighthHankelCurvature := by
    funext y
    ring
  rw [hfun] at hquarter
  refine hquarter.congr_deriv ?_
  ring

/-- Strict increase of native D1 is exactly positivity of the projective drift polynomial. -/
theorem deriv_thetaCuspFullReflectionEighthHankelCurvature_pos_iff_projectiveDrift_pos
    {x : ℝ} (hx : 0 < x) :
    0 < deriv thetaCuspFullReflectionEighthHankelCurvature x ↔
      0 < thetaCuspReflectedEighthSourceProjectiveDrift x := by
  rw [(hasDerivAt_thetaCuspFullReflectionEighthHankelCurvature_projectiveDrift hx).deriv]
  have hqpos := thetaCuspModularSourcePositiveState_re_pos hx
    HTGeometry.ModularThetaSourcePositiveState.Q
  rw [div_pos_iff_of_pos_right]
  positivity

/-- Raw rank-three reflected curvature inherits exact modular evenness from the complete source. -/
theorem thetaCuspFullSourceReflectionEighthHankelCurvature_neg (x : ℝ) :
    thetaCuspFullSourceReflectionEighthHankelCurvature (-x) =
      thetaCuspFullSourceReflectionEighthHankelCurvature x := by
  unfold thetaCuspFullSourceReflectionEighthHankelCurvature
  dsimp only
  simp only [iteratedDeriv_thetaCuspFullSource_neg]
  norm_num
  unfold HilbertMetric.signedEvenHankelThreeDet
    HilbertMetric.reflectedProductSecondJet
    HilbertMetric.reflectedProductFourthJet
    HilbertMetric.reflectedProductSixthJet
    HilbertMetric.reflectedProductEighthJet
  ring

/-- The modular theta mass is even in logarithmic source coordinate. -/
theorem completedThetaProfile_neg (x : ℝ) :
    Bottcher.completedThetaProfile (-x) = Bottcher.completedThetaProfile x := by
  rw [Bottcher.completedThetaProfile, Bottcher.completedThetaProfile]
  rw [show 2 * -x = -2 * x by ring]
  have hexp : (Real.exp (-2 * x)) ^ (1 / 2 : ℝ) = Real.exp (-x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [HurwitzZeta.evenKernel_functional_equation, hexp]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  have hne : Real.exp (-x) ≠ 0 := (Real.exp_pos _).ne'
  have hinv : 1 / Real.exp (-2 * x) = Real.exp (2 * x) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv]
  field_simp
  have hprod : Real.exp (-x) * Real.exp (x / 2) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (-x) * HurwitzZeta.cosKernel 0 (Real.exp (x * 2)) *
      Real.exp (x / 2) =
      (Real.exp (-x) * Real.exp (x / 2)) *
        HurwitzZeta.cosKernel 0 (Real.exp (x * 2)) by ring,
    hprod]

/-- Projective D1 is raw D1 divided by the sixth power of the literal theta source. -/
theorem thetaCuspReflectedEighthSourceProjectiveValue_eq_raw_div_source_pow_six
    (x : ℝ) :
    thetaCuspReflectedEighthSourceProjectiveValue x =
      thetaCuspFullSourceReflectionEighthHankelCurvature x /
        thetaCuspFullSource x ^ 6 := by
  let q := (thetaCuspModularSourcePositiveState
    HTGeometry.ModularThetaSourcePositiveState.Q x).re
  have hqpos : 0 < q := by
    simpa only [q, thetaCuspModularSourcePositiveState_Q_eq_sourceFactor] using
      thetaCuspModularSourceFactor_re_pos x
  have hsourceValue := congrArg Complex.re
    (thetaCuspReflectedEighthSourcePositiveModularValue_eq_normalized x)
  have hraw :=
    thetaCuspFullSourceReflectionEighthHankelCurvature_eq_mass_pow_six_mul_normalized_re x
  rw [← hsourceValue] at hraw
  have hsource : thetaCuspFullSource x =
      Bottcher.completedThetaProfile x * q := by
    have h := congrArg Complex.re
      (ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ x)
    rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at h
    have hQim := thetaCuspModularSourcePositiveState_im_eq_zero x
      HTGeometry.ModularThetaSourcePositiveState.Q
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, hQim, sub_zero] at h
    simpa only [q] using h
  have hHpos := thetaCuspCompletedThetaProfile_pos x
  dsimp only [thetaCuspReflectedEighthSourceProjectiveValue]
  change (thetaCuspReflectedEighthSourcePositiveModularValue x).re / q ^ 6 = _
  rw [hraw, hsource, mul_pow]
  field_simp [hqpos.ne', hHpos.ne']

/-- Projective D1 is even on the full physical theta trajectory. -/
theorem thetaCuspReflectedEighthSourceProjectiveValue_neg (x : ℝ) :
    thetaCuspReflectedEighthSourceProjectiveValue (-x) =
      thetaCuspReflectedEighthSourceProjectiveValue x := by
  rw [thetaCuspReflectedEighthSourceProjectiveValue_eq_raw_div_source_pow_six,
    thetaCuspReflectedEighthSourceProjectiveValue_eq_raw_div_source_pow_six,
    thetaCuspFullSourceReflectionEighthHankelCurvature_neg,
    thetaCuspFullSource_neg]

/-- The literal source coordinate `Q` is even on the physical theta trajectory. -/
theorem thetaCuspModularSourcePositiveState_Q_re_neg (x : ℝ) :
    (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q (-x)).re =
    (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re := by
  have hneg := congrArg Complex.re
    (ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ (-x))
  have hpos := congrArg Complex.re
    (ofReal_thetaCuspFullSource_eq_modularMass_mul_sourcePositiveQ x)
  have hQneg := thetaCuspModularSourcePositiveState_im_eq_zero (-x)
    HTGeometry.ModularThetaSourcePositiveState.Q
  have hQpos := thetaCuspModularSourcePositiveState_im_eq_zero x
    HTGeometry.ModularThetaSourcePositiveState.Q
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at hneg
  rw [thetaCuspModularODEState_H_eq_completedThetaProfile] at hpos
  simp only [Complex.ofReal_re, Complex.mul_re,
    hQneg, hQpos, mul_zero, sub_zero] at hneg hpos
  rw [completedThetaProfile_neg, thetaCuspFullSource_neg] at hneg
  nlinarith [thetaCuspCompletedThetaProfile_pos x]

/-- Projective drift is reflection-odd; its apparent seam instability is forced cancellation. -/
theorem thetaCuspReflectedEighthSourceProjectiveDrift_neg (x : ℝ) :
    thetaCuspReflectedEighthSourceProjectiveDrift (-x) =
      -thetaCuspReflectedEighthSourceProjectiveDrift x := by
  have heven : thetaCuspReflectedEighthSourceProjectiveValue ∘ Neg.neg =
      thetaCuspReflectedEighthSourceProjectiveValue := by
    funext y
    exact thetaCuspReflectedEighthSourceProjectiveValue_neg y
  have hleft :=
    (hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue (-x)).comp x
      (hasDerivAt_neg x)
  rw [heven] at hleft
  have h := hleft.unique
    (hasDerivAt_thetaCuspReflectedEighthSourceProjectiveValue x)
  rw [thetaCuspModularSourcePositiveState_Q_re_neg] at h
  have hqpos : 0 < (thetaCuspModularSourcePositiveState
      HTGeometry.ModularThetaSourcePositiveState.Q x).re := by
    rw [thetaCuspModularSourcePositiveState_Q_eq_sourceFactor]
    exact thetaCuspModularSourceFactor_re_pos x
  field_simp [hqpos.ne'] at h
  linarith

/-- The exact projective drift vanishes at the modular seam. -/
theorem thetaCuspReflectedEighthSourceProjectiveDrift_zero :
    thetaCuspReflectedEighthSourceProjectiveDrift 0 = 0 := by
  have h := thetaCuspReflectedEighthSourceProjectiveDrift_neg 0
  norm_num at h
  linarith

end

end RHTower
