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

end

end RHTower
